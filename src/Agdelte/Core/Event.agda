{-# OPTIONS --without-K #-}

-- Event: discrete events as AST (description of subscriptions)
-- Runtime interprets this description and creates real subscriptions
--
-- This module re-exports everything from submodules for backward compatibility:
--   Core.agda        — types (WsMsg, KeyboardEvent, MouseEvent, etc.),
--                      Sub, Event, mapSub, mapE, filterE, backward-compat constructors
--   Keyboard.agda    — keyboard convenience constructors (onKey, onKeys, etc.)
--   Mouse.agda       — mouse convenience constructors (onLeftClick, mousePosition, etc.)
--   Combinators.agda — mergeAll, accumE, mapAccum, sequenceE, etc.

module Agdelte.Core.Event where

open import Agdelte.Core.Event.Core public
open import Agdelte.Core.Event.Keyboard public
open import Agdelte.Core.Event.Mouse public
open import Agdelte.Core.Event.Combinators public
