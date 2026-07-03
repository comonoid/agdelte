{-# OPTIONS --without-K --guardedness #-}

-- Server FFI: Haskell-only postulates via MAlonzo
-- This module uses {-# COMPILE GHC #-} pragmas — only for server builds

module Agdelte.FFI.Server where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Bool using (if_then_else_)

------------------------------------------------------------------------
-- Basic IO
------------------------------------------------------------------------

postulate
  putStrLn : String → IO ⊤
  getLine  : IO String

{-# FOREIGN GHC import qualified Data.Text    as T    #-}
{-# FOREIGN GHC import qualified Data.Text.IO as TIO  #-}
{-# FOREIGN GHC import qualified Agdelte.Http as Http  #-}
{-# FOREIGN GHC import qualified Data.IORef as IORef   #-}
{-# FOREIGN GHC import qualified Control.Exception as Ex #-}

{-# COMPILE GHC putStrLn = TIO.putStrLn #-}
{-# COMPILE GHC getLine  = TIO.getLine  #-}

------------------------------------------------------------------------
-- IO combinators
------------------------------------------------------------------------

infixl 1 _>>=_ _>>_

postulate
  _>>=_ : ∀ {A B : Set} → IO A → (A → IO B) → IO B
  _>>_  : ∀ {A B : Set} → IO A → IO B → IO B
  pure  : ∀ {A : Set} → A → IO A
  bracket : ∀ {A B : Set} → IO A → (A → IO ⊤) → (A → IO B) → IO B
  onException : ∀ {A B : Set} → IO A → IO B → IO A

{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}
{-# COMPILE GHC _>>_  = \_ _ -> (>>)  #-}
{-# COMPILE GHC pure  = \_ -> return   #-}
{-# COMPILE GHC bracket = \_ _ -> Ex.bracket #-}
{-# COMPILE GHC onException = \_ _ -> Ex.onException #-}

-- | Abort the process loudly with a message. Used when WAL recovery hits
-- mid-log corruption: refusing to start beats silently dropping committed data.
postulate
  die : ∀ {A : Set} → String → IO A

{-# COMPILE GHC die = \_ msg -> ioError (userError (T.unpack msg)) #-}

-- Try an IO action, catching all exceptions as Left String
open import Data.Maybe using (Maybe; just; nothing)

postulate
  tryCatch : ∀ {A : Set} → IO A → IO (Maybe A)

{-# FOREIGN GHC
  tryCatchImpl :: IO a -> IO (Maybe a)
  tryCatchImpl act = fmap eitherToMaybe (Ex.try act)
    where
      eitherToMaybe :: Either Ex.SomeException b -> Maybe b
      eitherToMaybe (Right a) = Just a
      eitherToMaybe (Left _)  = Nothing
  #-}

{-# COMPILE GHC tryCatch = \_ -> tryCatchImpl #-}

-- | Run IO action with async exceptions masked.
-- Prevents async exceptions from interrupting a critical section.
postulate
  mask : ∀ {A : Set} → IO A → IO A

{-# COMPILE GHC mask = \_ act -> Ex.mask_ act #-}

------------------------------------------------------------------------
-- STM
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)


postulate
  IORef : Set → Set
  newIORef          : ∀ {A : Set} → A → IO (IORef A)
  readIORef         : ∀ {A : Set} → IORef A → IO A
  writeIORef        : ∀ {A : Set} → IORef A → A → IO ⊤
  -- NOTE: atomicModifyIORef omitted — Haskell's IORef.atomicModifyIORef
  -- expects native (,) tuples, but Agda's _×_ compiles to MAlonzo's Σ
  -- record (not Haskell tuples). wireAgent uses readIORef+writeIORef
  -- instead (see below); true atomicity requires an MVar or TVar.

{-# COMPILE GHC IORef = type IORef.IORef #-}
{-# COMPILE GHC newIORef          = \_ -> IORef.newIORef          #-}
{-# COMPILE GHC readIORef         = \_ -> IORef.readIORef         #-}
{-# COMPILE GHC writeIORef        = \_ -> IORef.writeIORef        #-}

------------------------------------------------------------------------
-- MVar (mutual exclusion for wireAgent)
------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Control.Concurrent.MVar as MVar #-}

postulate
  MVar : Set → Set
  newMVar   : ∀ {A : Set} → A → IO (MVar A)
  takeMVar  : ∀ {A : Set} → MVar A → IO A
  putMVar   : ∀ {A : Set} → MVar A → A → IO ⊤
  -- Non-destructive snapshot read: returns the current value without emptying
  -- the MVar, so concurrent readers don't exclude one another (state is
  -- immutable, so a pointer read is a consistent snapshot).
  readMVar  : ∀ {A : Set} → MVar A → IO A

{-# COMPILE GHC MVar     = type MVar.MVar #-}
{-# COMPILE GHC newMVar  = \_ -> MVar.newMVar  #-}
{-# COMPILE GHC takeMVar = \_ -> MVar.takeMVar #-}
{-# COMPILE GHC putMVar  = \_ -> MVar.putMVar  #-}
{-# COMPILE GHC readMVar = \_ -> MVar.readMVar #-}

-- A native Haskell 2-tuple at the FFI boundary (Agda's Σ/_×_ compiles to a
-- record MAlonzo can't pass to a (,)-typed callback). modifyMVarMasked's
-- callback must return IO (newState, result); this is that pair.
postulate
  Pair2   : Set → Set → Set
  mkPair2 : ∀ {A B : Set} → A → B → Pair2 A B
{-# COMPILE GHC Pair2   = type (,)        #-}
{-# COMPILE GHC mkPair2 = \_ _ -> (,)     #-}

-- | Exception-safe read-modify-write under a mask.
-- Takes the MVar, runs the callback with ASYNC EXCEPTIONS MASKED; on success
-- puts the returned new state and yields the result; on ANY exception (incl.
-- one thrown while FORCING the pure callback) restores the original value and
-- re-raises. This is the whole critical section done right — durable-before-
-- visible holds because the callback performs its durable write before
-- returning the new state that modifyMVarMasked then makes visible.
postulate
  modifyMVarMasked : ∀ {A B : Set} → MVar A → (A → IO (Pair2 A B)) → IO B
{-# COMPILE GHC modifyMVarMasked = \_ _ -> MVar.modifyMVarMasked #-}

------------------------------------------------------------------------
-- HTTP Server
------------------------------------------------------------------------

-- HTTP request (method, path, body, headers)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

-- A string pair AT THE FFI BOUNDARY, bound to a Haskell 2-tuple. Agda's own
-- pair (Σ / _×_) cannot appear in a COMPILE GHC type: MAlonzo can't translate
-- Σ, and the Σ→tuple binding it suggests is only legal in Σ's own (builtin)
-- module. StrPair lets the header FFI translate while the PUBLIC API keeps
-- List (String × String) via the pure wrappers below.
postulate
  StrPair    : Set
  mkStrPair  : String → String → StrPair
  fstStrPair : StrPair → String
  sndStrPair : StrPair → String
{-# FOREIGN GHC type StrPairH = (T.Text, T.Text) #-}
{-# COMPILE GHC StrPair    = type StrPairH #-}
{-# COMPILE GHC mkStrPair  = (\ k v -> (k, v) :: StrPairH) #-}
{-# COMPILE GHC fstStrPair = (fst :: StrPairH -> T.Text) #-}
{-# COMPILE GHC sndStrPair = (snd :: StrPairH -> T.Text) #-}

postulate
  HttpRequest : Set
  reqMethod  : HttpRequest → String
  reqPath    : HttpRequest → String
  reqBody    : HttpRequest → String
  reqHeadersRaw : HttpRequest → List StrPair

{-# COMPILE GHC HttpRequest = type Http.Request #-}
{-# COMPILE GHC reqMethod  = Http.reqMethod  #-}
{-# COMPILE GHC reqPath    = Http.reqPath    #-}
{-# COMPILE GHC reqBody    = Http.reqBody    #-}
{-# COMPILE GHC reqHeadersRaw = Http.reqHeaders #-}

-- Public API: headers as List (String × String) (Σ is fine in pure Agda).
reqHeaders : HttpRequest → List (String × String)
reqHeaders req = map (λ p → fstStrPair p , sndStrPair p) (reqHeadersRaw req)

-- HTTP Response (status + body + optional headers)
postulate
  HttpResponse : Set
  mkResponse   : Nat → String → HttpResponse
  mkResponseHRaw : Nat → String → List StrPair → HttpResponse

{-# FOREIGN GHC
  data AgdaResponse = AgdaResponse Integer T.Text [(T.Text, T.Text)]
  #-}

{-# COMPILE GHC HttpResponse   = type AgdaResponse #-}
{-# COMPILE GHC mkResponse     = \s b -> AgdaResponse s b []      #-}
{-# COMPILE GHC mkResponseHRaw = AgdaResponse #-}

mkResponseH : Nat → String → List (String × String) → HttpResponse
mkResponseH s b hdrs = mkResponseHRaw s b (map (λ p → mkStrPair (proj₁ p) (proj₂ p)) hdrs)

-- | Lookup a header by name (case-insensitive)
postulate
  eqStrCI : String → String → Bool

{-# FOREIGN GHC
  eqStrCIImpl :: T.Text -> T.Text -> Bool
  eqStrCIImpl a b = T.toCaseFold a == T.toCaseFold b
  #-}
{-# COMPILE GHC eqStrCI = eqStrCIImpl #-}

lookupHeader : String → List (String × String) → Maybe String
lookupHeader _ [] = nothing
lookupHeader name ((k , v) ∷ rest) =
  if eqStrCI name k then just v else lookupHeader name rest

-- Listen on port with request handler
-- Handler receives request, returns HttpResponse with status code
postulate
  listen : Nat → (HttpRequest → IO HttpResponse) → IO ⊤

{-# FOREIGN GHC
  listenImpl :: Integer -> (Http.Request -> IO AgdaResponse) -> IO ()
  listenImpl port handler = Http.serve (fromIntegral port) $ \req -> do
    AgdaResponse status body hdrs <- handler req
    return (Http.Response (fromIntegral status) body hdrs)
  #-}

{-# COMPILE GHC listen = listenImpl #-}

-- Listen bound to a specific host (e.g. "127.0.0.1"). Loopback-only by default
-- keeps the money/PII server off the network until authz exists.
postulate
  listenHost : String → Nat → (HttpRequest → IO HttpResponse) → IO ⊤

{-# FOREIGN GHC
  listenHostImpl :: T.Text -> Integer -> (Http.Request -> IO AgdaResponse) -> IO ()
  listenHostImpl host port handler = Http.serveHost host (fromIntegral port) $ \req -> do
    AgdaResponse status body hdrs <- handler req
    return (Http.Response (fromIntegral status) body hdrs)
  #-}
{-# COMPILE GHC listenHost = listenHostImpl #-}

-- Listen on an AF_UNIX stream socket at `path` (nginx `proxy_pass http://unix:PATH:`). The server
-- creates + chmods (0660) the socket; access is filesystem-gated (off-network). Used by headless
-- deploys behind nginx instead of a TCP port.
postulate
  listenUnix : String → (HttpRequest → IO HttpResponse) → IO ⊤

{-# FOREIGN GHC
  listenUnixImpl :: T.Text -> (Http.Request -> IO AgdaResponse) -> IO ()
  listenUnixImpl path handler = Http.serveUnix (T.unpack path) $ \req -> do
    AgdaResponse status body hdrs <- handler req
    return (Http.Response (fromIntegral status) body hdrs)
  #-}
{-# COMPILE GHC listenUnix = listenUnixImpl #-}

-- Run `action` forever on a background thread, every `sec` seconds (first run immediately).
-- The worker primitive for headless deploys: periodic outbox delivery, reminders, bus dispatch.
-- An exception in one tick is swallowed (logged) so the loop survives transient failures.
postulate
  forkLoopEvery : Nat → IO ⊤ → IO ⊤

{-# FOREIGN GHC import qualified Control.Concurrent as Conc #-}
{-# FOREIGN GHC import qualified Control.Monad as Mon #-}
{-# FOREIGN GHC
  forkLoopEveryImpl :: Integer -> IO () -> IO ()
  forkLoopEveryImpl sec action = do
    _ <- Conc.forkIO (Mon.forever (do
           action `Ex.catch` \e -> putStrLn ("worker tick failed: " ++ show (e :: Ex.SomeException))
           Conc.threadDelay (fromIntegral sec * 1000000)))
    return ()
  #-}
{-# COMPILE GHC forkLoopEvery = forkLoopEveryImpl #-}

-- Read an environment variable, or a default if unset.
{-# FOREIGN GHC import System.Environment (lookupEnv) #-}
postulate
  getEnvOr : String → String → IO String

{-# FOREIGN GHC
  getEnvOrImpl :: T.Text -> T.Text -> IO T.Text
  getEnvOrImpl key def = fmap (maybe def T.pack) (lookupEnv (T.unpack key))
  #-}
{-# COMPILE GHC getEnvOr = getEnvOrImpl #-}

------------------------------------------------------------------------
-- Unix Socket IPC (ProcessOptic)
------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Agdelte.Process as Proc #-}

-- Opaque IPC handle
postulate
  IpcHandle : Set

{-# COMPILE GHC IpcHandle = type Proc.IpcClient #-}

-- Serve agent on Unix socket (ProcessOptic protocol: "peek" / "step:INPUT")
postulate
  serveAgentProcess : String → IO String → (String → IO String) → IO ⊤

{-# FOREIGN GHC
  serveAgentProcessImpl :: T.Text -> IO T.Text -> (T.Text -> IO T.Text) -> IO ()
  serveAgentProcessImpl path observe step = do
    _ <- Proc.serveAgentProcess (T.unpack path) observe step
    return ()
  #-}

{-# COMPILE GHC serveAgentProcess = serveAgentProcessImpl #-}

-- Connect to remote agent via Unix socket
postulate
  connectProcess : String → IO IpcHandle

{-# FOREIGN GHC
  connectProcessImpl :: T.Text -> IO Proc.IpcClient
  connectProcessImpl path = Proc.connectUnix (T.unpack path)
  #-}

{-# COMPILE GHC connectProcess = connectProcessImpl #-}

-- Query remote agent state (peek)
postulate
  queryProcess : IpcHandle → IO String

{-# COMPILE GHC queryProcess = Proc.queryProcess #-}

-- Step remote agent (over)
postulate
  stepProcess : IpcHandle → String → IO String

{-# COMPILE GHC stepProcess = Proc.stepProcess #-}

-- Close IPC connection
postulate
  closeProcess : IpcHandle → IO ⊤

{-# COMPILE GHC closeProcess = Proc.ipcClose #-}

------------------------------------------------------------------------
-- Multi-Agent Server with WebSocket (AgentServer)
------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Agdelte.AgentServer as AS #-}

-- AgentDef: definition of one agent for the server
postulate
  AgentDef : Set
  mkAgentDef : String → String → IO String → (String → IO String) → AgentDef

{-# COMPILE GHC AgentDef = type AS.AgentDef #-}

{-# FOREIGN GHC
  mkAgentDefImpl :: T.Text -> T.Text -> IO T.Text -> (T.Text -> IO T.Text) -> AS.AgentDef
  mkAgentDefImpl name path observe step = AS.AgentDef
    { AS.agentName = name
    , AS.agentPath = path
    , AS.agentObserve = observe
    , AS.agentStep = step
    }
  #-}

{-# COMPILE GHC mkAgentDef = mkAgentDefImpl #-}

-- Run multi-agent server (arbitrary number of agents)

postulate
  runAgentServerN : Nat → List AgentDef → IO ⊤

{-# FOREIGN GHC
  runAgentServerNImpl :: Integer -> [AS.AgentDef] -> IO ()
  runAgentServerNImpl port agents = AS.runAgentServer (fromIntegral port) (Just "*") agents
  #-}

{-# COMPILE GHC runAgentServerN = runAgentServerNImpl #-}

------------------------------------------------------------------------
-- Connection types (for Diagram routing)
------------------------------------------------------------------------

postulate
  ConnectionDef    : Set
  mkBroadcastDef   : String → ConnectionDef
  mkAgentPipeDef   : String → String → ConnectionDef
  mkClientRouteDef : String → ConnectionDef

{-# COMPILE GHC ConnectionDef    = type AS.ConnectionDef #-}
{-# COMPILE GHC mkBroadcastDef   = AS.BroadcastDef      #-}
{-# COMPILE GHC mkAgentPipeDef   = AS.AgentPipeDef      #-}
{-# COMPILE GHC mkClientRouteDef = AS.ClientRouteDef    #-}

-- Run multi-agent server with connection routing
postulate
  runAgentServerNWithConns : Nat → List AgentDef → List ConnectionDef → IO ⊤

{-# FOREIGN GHC
  runAgentServerNWithConnsImpl :: Integer -> [AS.AgentDef] -> [AS.ConnectionDef] -> IO ()
  runAgentServerNWithConnsImpl port agents conns =
    AS.runAgentServerWithConns (fromIntegral port) (Just "*") agents conns
  #-}

{-# COMPILE GHC runAgentServerNWithConns = runAgentServerNWithConnsImpl #-}

------------------------------------------------------------------------
-- Wire pure Agent to AgentDef (bridge coalgebra to mutable server)
------------------------------------------------------------------------

open import Agdelte.Concurrent.Agent using (Agent; state; observe; stepAgent)

wireAgent : ∀ {S} → String → String → Agent S String String → IO AgentDef
wireAgent name path agent =
  newIORef (observe agent (state agent)) >>= λ stateRef →
  newMVar agent                          >>= λ agentMVar →
  let -- Observe under MVar lock: bracket ensures stateRef is read while
      -- the mutex is held, so observe always sees a post-step snapshot.
      -- bracket releases the MVar even if readIORef throws.
      observeIO : IO String
      observeIO = bracket (takeMVar agentMVar) (putMVar agentMVar)
                          (λ _ → readIORef stateRef)
      -- stepIO: take MVar, compute step, store new agent + observation.
      -- onException restores the old agent if stepAgent throws (e.g. debugTrap,
      -- stack overflow). Without this, the MVar stays empty → deadlock.
      -- mask ensures putMVar + writeIORef are atomic w.r.t. async exceptions,
      -- preventing stateRef from going stale relative to the MVar agent.
      stepIO : String → IO String
      stepIO input =
        takeMVar agentMVar >>= λ a →
        onException
          (let result   = stepAgent a input
               newAgent = proj₁ result
               output   = proj₂ result
           in mask (putMVar agentMVar newAgent >>
                    writeIORef stateRef output) >>
              pure output)
          (putMVar agentMVar a)
  in
  pure (mkAgentDef name path observeIO stepIO)
