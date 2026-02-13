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

{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}
{-# COMPILE GHC _>>_  = \_ _ -> (>>)  #-}
{-# COMPILE GHC pure  = \_ -> return   #-}

------------------------------------------------------------------------
-- String operations
------------------------------------------------------------------------

infixr 5 _++s_

postulate
  _++s_ : String → String → String

{-# COMPILE GHC _++s_ = T.append #-}

------------------------------------------------------------------------
-- STM
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)


postulate
  IORef : Set → Set
  newIORef   : ∀ {A : Set} → A → IO (IORef A)
  readIORef  : ∀ {A : Set} → IORef A → IO A
  writeIORef : ∀ {A : Set} → IORef A → A → IO ⊤

{-# COMPILE GHC IORef = type IORef.IORef #-}
{-# COMPILE GHC newIORef   = \_ -> IORef.newIORef   #-}
{-# COMPILE GHC readIORef  = \_ -> IORef.readIORef   #-}
{-# COMPILE GHC writeIORef = \_ -> IORef.writeIORef  #-}

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

-- HTTP response
postulate
  mkResponse : Nat → String → IO ⊤

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

-- Run multi-agent server
postulate
  runAgentServer : Nat → IORef AgentDef → IO ⊤
  runAgentServer1 : Nat → AgentDef → IO ⊤
  runAgentServer2 : Nat → AgentDef → AgentDef → IO ⊤

{-# FOREIGN GHC
  runAgentServer1Impl :: Integer -> AS.AgentDef -> IO ()
  runAgentServer1Impl port a1 = AS.runAgentServer (fromIntegral port) (Just "*") [a1]

  runAgentServer2Impl :: Integer -> AS.AgentDef -> AS.AgentDef -> IO ()
  runAgentServer2Impl port a1 a2 = AS.runAgentServer (fromIntegral port) (Just "*") [a1, a2]
  #-}

{-# COMPILE GHC runAgentServer1 = runAgentServer1Impl #-}
{-# COMPILE GHC runAgentServer2 = runAgentServer2Impl #-}
