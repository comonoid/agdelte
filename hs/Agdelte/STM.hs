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
  ( Channel
  , Subscription
  , newChannel
  , sendChannel
  , dupChannel
  , recvChannel
  , tryRecvChannel
  , Mailbox
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

-- | A broadcast channel. Write-only by default; call 'dupChannel' to create
-- a subscriber that can read. This avoids memory leaks when a Channel is
-- used only for writing (no phantom read-end accumulating messages).
newtype Channel = Channel
  { chWrite :: TChan T.Text      -- ^ Write end (shared)
  }

-- | A subscriber for a broadcast channel. Created via 'dupChannel'.
-- Each subscriber has its own read position.
newtype Subscription = Subscription
  { subRead :: TChan T.Text
  }

-- | Create a new broadcast channel (write-only until 'dupChannel' is called)
newChannel :: IO Channel
newChannel = Channel <$> newBroadcastTChanIO

-- | Send a message to the channel (all subscribers receive it)
sendChannel :: Channel -> T.Text -> IO ()
sendChannel ch msg = atomically $ writeTChan (chWrite ch) msg

-- | Create a new subscriber. Each subscriber gets its own read position
-- and receives all messages sent after this call.
dupChannel :: Channel -> IO Subscription
dupChannel ch = Subscription <$> atomically (dupTChan (chWrite ch))

-- | Receive next message from a subscription (blocks until available)
recvChannel :: Subscription -> IO T.Text
recvChannel sub = atomically $ readTChan (subRead sub)

-- | Try to receive from a subscription (non-blocking, returns Nothing if empty)
tryRecvChannel :: Subscription -> IO (Maybe T.Text)
tryRecvChannel sub = atomically $ tryReadTChan (subRead sub)

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
