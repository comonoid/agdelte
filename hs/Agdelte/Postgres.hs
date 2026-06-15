{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | PostgreSQL FFI for the agdelte server runtime (Task 0 spike).
--
-- Backed by hpgsql — a pure-Haskell PostgreSQL driver (no libpq, no C deps:
-- it speaks the wire protocol directly). This keeps deployment simple: on
-- Debian there is no @libpq-dev@ to install, and the dependency set is fixed
-- by cabal.project.freeze.
--
-- Domain-agnostic infrastructure (SPEC §4: the agdelte layer). The pool is an
-- opaque handle on the Agda side (postulate Pool : Set). The whole point of the
-- spike: the pool is created ONCE at startup and survives across every Warp
-- request (cf. the IORef in server/HttpAgent.agda).
--
-- At the FFI boundary everything is text (SPEC §5.6); jsonb/JSON is the generic
-- untyped carrier for reads, decoded on the Agda side via Agdelte.Json.
module Agdelte.Postgres
  ( Pool
  , newPool
  , queryJson
  , queryCol
  , execSql
  , closePool
  ) where

import           Control.Concurrent.MVar
import           Control.Exception (ErrorCall (..), bracket, throwIO)
import           Control.Monad (replicateM)
import           Data.Int (Int64)
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import           Data.Time.Clock (DiffTime)
import           Data.Tuple.Only (Only (..))

import           Hpgsql (HPgConnection, execute, query)
import           Hpgsql.Connection
                   ( ConnectionString
                   , closeGracefully
                   , connect
                   , parseLibpqConnectionString
                   )
import           Hpgsql.Query (mkQuery)

-- | Opaque connection pool: a stack of idle connections in an MVar, plus the
-- parsed conninfo and connect timeout (to open extras under load) and a soft
-- cap on idle connections kept on release.
data Pool = Pool
  { poolConnInfo :: ConnectionString
  , poolTimeout  :: DiffTime
  , poolMaxIdle  :: Int
  , poolIdle     :: MVar [HPgConnection]
  }

-- | Connect timeout for opening a connection (seconds; DiffTime's Num literal).
connectTimeout :: DiffTime
connectTimeout = 10

-- | Create a pool, eagerly opening @size@ connections (proves connectivity at
-- startup). @conninfo@ is a libpq connection string, e.g.
-- @"host=localhost dbname=agdelte user=agdelte"@.
newPool :: Text -> Int -> IO Pool
newPool conninfo size = do
  cs <- case parseLibpqConnectionString conninfo of
          Right c  -> pure c
          Left err -> throwIO (ErrorCall ("hpgsql: bad conninfo: " ++ err))
  let n = max 1 size
  conns <- replicateM n (connect cs connectTimeout)
  mv    <- newMVar conns
  pure (Pool cs connectTimeout n mv)

-- | Borrow a connection: pop an idle one, or open a fresh one if the pool is
-- drained (so we never deadlock on contention).
acquire :: Pool -> IO HPgConnection
acquire (Pool cs t _ mv) = modifyMVar mv $ \conns -> case conns of
  (c : rest) -> pure (rest, c)
  []         -> do c <- connect cs t
                   pure ([], c)

-- | Return a connection. Keep it idle if under the cap, else close it.
release :: Pool -> HPgConnection -> IO ()
release (Pool _ _ maxIdle mv) c = modifyMVar_ mv $ \conns ->
  if length conns >= maxIdle
    then closeGracefully c >> pure conns
    else pure (c : conns)

-- | Run an action with a borrowed connection, always returning it (even on
-- exception). hpgsql requires that the borrowing thread is the one consuming
-- results — guaranteed here, since each request handler runs on its own thread
-- and holds the connection exclusively for the duration.
withConn :: Pool -> (HPgConnection -> IO a) -> IO a
withConn pool = bracket (acquire pool) (release pool)

-- | Run a single SELECT (no trailing ';') and return the full result set as a
-- JSON array (text). The SQL is wrapped in @json_agg@, so it MUST be a single
-- SELECT. Empty result → @"[]"@. Decode with Agdelte.Json.
queryJson :: Pool -> Text -> IO Text
queryJson pool sql = withConn pool $ \conn -> do
  let wrapped = "SELECT coalesce(json_agg(_q), '[]')::text FROM (" <> sql <> ") _q"
  rows <- query conn (mkQuery (TE.encodeUtf8 wrapped) ()) :: IO [Only Text]
  case rows of
    (Only j : _) -> pure j
    []           -> pure "[]"

-- | Run a SELECT whose rows are a single text column; collect the values in
-- order. Generic untyped read for one column (e.g. applied migration versions),
-- avoiding a JSON round-trip.
queryCol :: Pool -> Text -> IO [Text]
queryCol pool sql = withConn pool $ \conn -> do
  rows <- query conn (mkQuery (TE.encodeUtf8 sql) ()) :: IO [Only Text]
  pure (map fromOnly rows)

-- | Run a non-row statement (INSERT/UPDATE/DELETE/DDL). Returns the number of
-- affected rows (0 for DDL).
execSql :: Pool -> Text -> IO Integer
execSql pool sql = withConn pool $ \conn -> do
  n <- execute conn (mkQuery (TE.encodeUtf8 sql) ())
  pure (fromIntegral (n :: Int64))

-- | Close all idle connections in the pool.
closePool :: Pool -> IO ()
closePool (Pool _ _ _ mv) = modifyMVar_ mv $ \conns -> do
  mapM_ closeGracefully conns
  pure []
