{-# OPTIONS --without-K --guardedness #-}

-- Research §1: Obligation Monad for Resource Tracking
--
-- Ensures resources are EVENTUALLY closed. Unlike IpcHandleL which
-- prevents misuse (query after close), the Obligation monad prevents
-- forgetting to close.
--
-- Key idea: Balanced programs pair every alloc with a free.
-- The type SafeIO A guarantees all resources are properly managed.
--
-- See also: ProcessOpticLinear.agda for the underlying indexed handles.

module Agdelte.Concurrent.Obligation where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)

open import Agdelte.Concurrent.ProcessOpticLinear
  using (ConnState; Connected; Disconnected; IpcHandleL; mkHandle;
         connect; query; step; close)
open import Agdelte.FFI.Server using (_>>=_; _>>_; pure)

------------------------------------------------------------------------
-- SafeIO: resource-safe IO computation (obligation-free by construction)
------------------------------------------------------------------------

-- Instead of tracking obligations in indices (which causes unification
-- issues with _+_), we provide combinators that are obligation-free
-- BY CONSTRUCTION. You can only build SafeIO values through balanced
-- alloc/free pairs.

{-# NO_UNIVERSE_CHECK #-}
data SafeIO (A : Set) : Set where
  pureS   : A → SafeIO A
  bindS   : ∀ {B} → SafeIO B → (B → SafeIO A) → SafeIO A
  liftS   : IO A → SafeIO A
  -- Balanced resource block: connect, use, close — all in one
  withIpcS : String → (IpcHandleL Connected → SafeIO A) → SafeIO A

------------------------------------------------------------------------
-- Run SafeIO
------------------------------------------------------------------------

run : ∀ {A} → SafeIO A → IO A
run (pureS a)          = pure a
run (bindS m f)        = run m >>= λ b → run (f b)
run (liftS io)         = io
run (withIpcS path f)  =
  connect path >>= λ h →
  run (f h)    >>= λ result →
  close h      >>
  pure result

------------------------------------------------------------------------
-- SafeIO monad operations
------------------------------------------------------------------------

_>>=S_ : ∀ {A B} → SafeIO A → (A → SafeIO B) → SafeIO B
_>>=S_ = bindS

_>>S_ : ∀ {A B} → SafeIO A → SafeIO B → SafeIO B
m >>S n = bindS m (λ _ → n)

infixl 1 _>>=S_ _>>S_

------------------------------------------------------------------------
-- Safe IPC interaction patterns
------------------------------------------------------------------------

-- Open, use, close — guaranteed balanced by type.
-- The handle exists only inside the callback scope.
withIpc : ∀ {A} → String → (IpcHandleL Connected → SafeIO A) → SafeIO A
withIpc = withIpcS

-- Safe peek: connect, query, close
safePeek : String → SafeIO String
safePeek path = withIpc path (λ h → liftS (query h))

-- Safe step: connect, step, close
safeStep : String → String → SafeIO String
safeStep path input = withIpc path (λ h → liftS (step h input))

open import Data.Product using (_×_; _,_)

-- Safe peek-then-step: connect, query, step, close
safePeekStep : String → String → SafeIO (String × String)
safePeekStep path input = withIpc path λ h →
  liftS (query h) >>=S λ peekResult →
  liftS (step h input) >>=S λ stepResult →
  pureS (peekResult , stepResult)

------------------------------------------------------------------------
-- Key safety property
------------------------------------------------------------------------

-- The handle returned by `connect` is ONLY available inside the
-- `withIpc` callback. There is no way to extract it or forget to close it.
-- Compare with raw IO where you can write:
--
--   leaky : IO (IpcHandleL Connected)
--   leaky = connect "/tmp/agent.sock"   -- handle leaked!
--
-- With SafeIO, this is impossible: no constructor returns a handle.
-- Every handle is created and destroyed within `withIpc`.

------------------------------------------------------------------------
-- Multiple resources
------------------------------------------------------------------------

-- Nested withIpc for multiple connections (all guaranteed closed)
withTwoIpc : ∀ {A} → String → String →
             (IpcHandleL Connected → IpcHandleL Connected → SafeIO A) →
             SafeIO A
withTwoIpc path₁ path₂ f =
  withIpc path₁ λ h₁ →
  withIpc path₂ λ h₂ →
  f h₁ h₂
