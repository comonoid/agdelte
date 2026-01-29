{-# LANGUAGE OverloadedStrings #-}

-- | STM-based channels for inter-agent communication.
--
-- Provides typed channels on top of STM TChan for coordinating
-- between agents running as green threads.
--
-- Architecture:
--   Agent A writes to channel → Agent B reads from channel
--   Both agents run as green threads (via Runtime.hs)
--   Channel is backed by STM TChan (composable, no deadlocks)
--
-- Note: Text-based channels for simplicity. The Serialize record
-- (FFI/Shared.agda) handles encoding/decoding of typed values.

module Agdelte.STM
  ( Channel(..)
  , newChannel
  , sendChannel
  , recvChannel
  , tryRecvChannel
  , dupChannel
  , Mailbox(..)
  , newMailbox
  , putMailbox
  , takeMailbox
  , tryTakeMailbox
  , readMailbox
  ) where

import Control.Concurrent.STM
import qualified Data.Text as T

------------------------------------------------------------------------
-- Channel: multi-producer, multi-consumer broadcast channel
------------------------------------------------------------------------

-- | A broadcast channel. Writers write to one end, readers each get
-- their own copy of all messages (via dupTChan).
data Channel = Channel
  { chWrite :: TChan T.Text      -- ^ Write end (shared)
  , chRead  :: TChan T.Text      -- ^ Read end (per-subscriber via dup)
  }

-- | Create a new broadcast channel
newChannel :: IO Channel
newChannel = do
  ch <- newBroadcastTChanIO
  readCh <- atomically $ dupTChan ch
  return (Channel ch readCh)

-- | Send a message to the channel (all subscribers receive it)
sendChannel :: Channel -> T.Text -> IO ()
sendChannel ch msg = atomically $ writeTChan (chWrite ch) msg

-- | Receive next message (blocks until available)
recvChannel :: Channel -> IO T.Text
recvChannel ch = atomically $ readTChan (chRead ch)

-- | Try to receive (non-blocking, returns Nothing if empty)
tryRecvChannel :: Channel -> IO (Maybe T.Text)
tryRecvChannel ch = atomically $ tryReadTChan (chRead ch)

-- | Duplicate channel for a new subscriber
-- Each subscriber gets their own read position
dupChannel :: Channel -> IO Channel
dupChannel ch = do
  readCh <- atomically $ dupTChan (chWrite ch)
  return (Channel (chWrite ch) readCh)

------------------------------------------------------------------------
-- Mailbox: single-value mutable cell (like TVar but with blocking take)
------------------------------------------------------------------------

-- | A mailbox holds at most one value. Useful for request/response patterns
-- between agents: one agent puts a value, another takes it.
data Mailbox = Mailbox
  { mbVar :: TMVar T.Text
  }

-- | Create an empty mailbox
newMailbox :: IO Mailbox
newMailbox = Mailbox <$> newEmptyTMVarIO

-- | Put a value into the mailbox (blocks if full)
putMailbox :: Mailbox -> T.Text -> IO ()
putMailbox mb val = atomically $ putTMVar (mbVar mb) val

-- | Take a value from the mailbox (blocks until available)
takeMailbox :: Mailbox -> IO T.Text
takeMailbox mb = atomically $ takeTMVar (mbVar mb)

-- | Try to take (non-blocking)
tryTakeMailbox :: Mailbox -> IO (Maybe T.Text)
tryTakeMailbox mb = atomically $ tryTakeTMVar (mbVar mb)

-- | Read without taking (blocks until available, leaves value)
readMailbox :: Mailbox -> IO T.Text
readMailbox mb = atomically $ readTMVar (mbVar mb)
