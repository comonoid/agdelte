{-# OPTIONS --without-K --guardedness #-}

-- Server FFI: Haskell-only postulates via MAlonzo
-- This module uses {-# COMPILE GHC #-} pragmas — only for server builds

module Agdelte.FFI.Server where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool)

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

{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}
{-# COMPILE GHC _>>_  = \_ _ -> (>>)  #-}
{-# COMPILE GHC pure  = \_ -> return   #-}
{-# COMPILE GHC bracket = \_ _ -> Ex.bracket #-}

-- Try an IO action, catching all exceptions as Left String
open import Data.Maybe using (Maybe; just; nothing)

postulate
  tryCatch : ∀ {A : Set} → IO A → IO (Maybe A)

{-# FOREIGN GHC
  tryCatchImpl :: IO a -> IO (Maybe a)
  tryCatchImpl act = do
    r <- Ex.try act :: IO (Either Ex.SomeException a)
    case r of
      Right a -> return (Just a)
      Left _  -> return Nothing
  #-}

{-# COMPILE GHC tryCatch = \_ -> tryCatchImpl #-}

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

{-# COMPILE GHC MVar     = type MVar.MVar #-}
{-# COMPILE GHC newMVar  = \_ -> MVar.newMVar  #-}
{-# COMPILE GHC takeMVar = \_ -> MVar.takeMVar #-}
{-# COMPILE GHC putMVar  = \_ -> MVar.putMVar  #-}

------------------------------------------------------------------------
-- HTTP Server
------------------------------------------------------------------------

-- HTTP request (method, path, body)
postulate
  HttpRequest : Set
  reqMethod : HttpRequest → String
  reqPath   : HttpRequest → String
  reqBody   : HttpRequest → String

{-# COMPILE GHC HttpRequest = type Http.Request #-}
{-# COMPILE GHC reqMethod = Http.reqMethod #-}
{-# COMPILE GHC reqPath   = Http.reqPath   #-}
{-# COMPILE GHC reqBody   = Http.reqBody   #-}

-- Listen on port with request handler
-- Handler receives request, returns response body
postulate
  listen : Nat → (HttpRequest → IO String) → IO ⊤

{-# FOREIGN GHC
  listenImpl :: Integer -> (Http.Request -> IO T.Text) -> IO ()
  listenImpl port handler = Http.serve (fromIntegral port) $ \req -> do
    body <- handler req
    return (Http.Response 200 body [])
  #-}

{-# COMPILE GHC listen = listenImpl #-}

------------------------------------------------------------------------
-- Multi-Agent Server with WebSocket
------------------------------------------------------------------------

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
-- Multi-Agent Server with WebSocket
------------------------------------------------------------------------

{-# FOREIGN GHC import qualified Agdelte.AgentServer as AS #-}
{-# FOREIGN GHC import qualified Agdelte.WebSocket as WS #-}

-- AgentDef: definition of one agent for the server
postulate
  AgentDef : Set
  mkAgentDef : String → String → IORef String → IO String → (String → IO String) → AgentDef

{-# COMPILE GHC AgentDef = type AS.AgentDef #-}

{-# FOREIGN GHC
  mkAgentDefImpl :: T.Text -> T.Text -> IORef.IORef T.Text -> IO T.Text -> (T.Text -> IO T.Text) -> AS.AgentDef
  mkAgentDefImpl name path stateRef observe step = AS.AgentDef
    { AS.agentName = name
    , AS.agentPath = path
    , AS.agentState = stateRef
    , AS.agentObserve = observe
    , AS.agentStep = step
    }
  #-}

{-# COMPILE GHC mkAgentDef = mkAgentDefImpl #-}

-- Run multi-agent server (arbitrary number of agents)
open import Agda.Builtin.List using (List; []; _∷_)

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

{-# FOREIGN GHC
  data ConnectionDef_
    = BroadcastDef_   T.Text
    | AgentPipeDef_   T.Text T.Text
    | ClientRouteDef_ T.Text
  #-}

{-# COMPILE GHC ConnectionDef    = type ConnectionDef_ #-}
{-# COMPILE GHC mkBroadcastDef   = BroadcastDef_       #-}
{-# COMPILE GHC mkAgentPipeDef   = AgentPipeDef_       #-}
{-# COMPILE GHC mkClientRouteDef = ClientRouteDef_     #-}

-- Run multi-agent server with connection routing
postulate
  runAgentServerNWithConns : Nat → List AgentDef → List ConnectionDef → IO ⊤

{-# FOREIGN GHC
  runAgentServerNWithConnsImpl :: Integer -> [AS.AgentDef] -> [ConnectionDef_] -> IO ()
  runAgentServerNWithConnsImpl port agents _conns =
    -- TODO: implement connection routing (agentPipe, broadcast, clientRoute)
    -- in AgentServer.hs. The connection data is available here; currently
    -- delegates to runAgentServer which only wires HTTP endpoints.
    AS.runAgentServer (fromIntegral port) (Just "*") agents
  #-}

{-# COMPILE GHC runAgentServerNWithConns = runAgentServerNWithConnsImpl #-}

------------------------------------------------------------------------
-- Wire pure Agent to AgentDef (bridge coalgebra to mutable server)
------------------------------------------------------------------------

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Agdelte.Concurrent.Agent using (Agent; state; observe; stepAgent)

wireAgent : ∀ {S} → String → String → Agent S String String → IO AgentDef
wireAgent name path agent =
  newIORef (observe agent (state agent)) >>= λ stateRef →
  newMVar agent                          >>= λ agentMVar →
  let observeIO : IO String
      observeIO = readIORef stateRef

      -- MVar guarantees mutual exclusion: only one step runs at a time.
      -- stateRef is written while the MVar is held (between takeMVar and
      -- putMVar), so observe sees a consistent snapshot.
      stepIO : String → IO String
      stepIO input =
        takeMVar agentMVar >>= λ a →
        let result = stepAgent a input
        in writeIORef stateRef (proj₂ result) >>
           putMVar agentMVar (proj₁ result)   >>
           pure (proj₂ result)
  in
  pure (mkAgentDef name path stateRef observeIO stepIO)
