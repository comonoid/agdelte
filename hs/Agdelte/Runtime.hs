{-# LANGUAGE OverloadedStrings #-}

-- | Generic Agent runner — runs an Agent as a green thread with STM channels.
--
-- Extracts the common "run agent in a thread" pattern from AgentServer.hs.
-- AgentServer uses this for HTTP/WS-exposed agents; this module provides
-- the lower-level building blocks.

module Agdelte.Runtime
  ( AgentRuntime(..)
  , runAgent
  , stepAgent
  , observeAgent
  , AgentRef
  , newAgentRef
  , readAgent
  , modifyAgent
  ) where

import Control.Concurrent (forkIO, ThreadId)
import Control.Concurrent.STM
import Data.IORef
import Data.Text (Text)

------------------------------------------------------------------------
-- AgentRef: mutable agent state with observation
------------------------------------------------------------------------

-- | Mutable reference to agent state with observe/step functions.
-- This is the core runtime representation of an Agent coalgebra.
data AgentRef s = AgentRef
  { arState   :: !(IORef s)
  , arObserve :: s -> Text
  , arStep    :: s -> Text -> s
  }

-- | Create a new AgentRef from initial state + functions
newAgentRef :: s -> (s -> Text) -> (s -> Text -> s) -> IO (AgentRef s)
newAgentRef s0 obs step = do
  ref <- newIORef s0
  return (AgentRef ref obs step)

-- | Read current observation
readAgent :: AgentRef s -> IO Text
readAgent ar = do
  s <- readIORef (arState ar)
  return (arObserve ar s)

-- | Modify agent state by stepping with input, return new observation
modifyAgent :: AgentRef s -> Text -> IO Text
modifyAgent ar input = do
  s <- readIORef (arState ar)
  let s' = arStep ar s input
  writeIORef (arState ar) s'
  return (arObserve ar s')

------------------------------------------------------------------------
-- AgentRuntime: agent running in a green thread
------------------------------------------------------------------------

-- | A running agent with input/output channels
data AgentRuntime = AgentRuntime
  { rtInput     :: TChan Text       -- ^ Send input to agent
  , rtOutput    :: TChan Text       -- ^ Broadcast channel for observations
  , rtThread    :: ThreadId         -- ^ Thread ID of the agent loop
  }

-- | Run an agent as a green thread.
-- The agent reads from input channel, steps, and broadcasts output.
-- Returns runtime handle for sending input and subscribing to output.
runAgent :: IORef Text               -- ^ Mutable state (as Text for simplicity)
         -> (Text -> IO Text)        -- ^ Observe function
         -> (Text -> IO Text)        -- ^ Step function (input -> new observation)
         -> IO AgentRuntime
runAgent stateRef observe step = do
  inChan  <- newTChanIO
  outChan <- newBroadcastTChanIO
  tid <- forkIO $ agentLoop inChan outChan
  return (AgentRuntime inChan outChan tid)
  where
    agentLoop :: TChan Text -> TChan Text -> IO ()
    agentLoop inChan outChan = do
      input <- atomically $ readTChan inChan
      output <- step input
      atomically $ writeTChan outChan output
      agentLoop inChan outChan

-- | Step an agent synchronously (no threading)
-- Useful for simple request-response patterns
stepAgent :: IORef Text -> (Text -> IO Text) -> Text -> IO Text
stepAgent _stateRef stepFn input = stepFn input

-- | Observe agent state synchronously
observeAgent :: IORef Text -> IO Text -> IO Text
observeAgent _stateRef obs = obs
