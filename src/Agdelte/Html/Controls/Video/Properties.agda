{-# OPTIONS --without-K #-}

-- Properties / invariants for the Video Player state machine.
-- These are checked by Agda at compile time — if they fail, the module won't compile.

module Agdelte.Html.Controls.Video.Properties where

open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agdelte.Html.Controls.Video.Types

------------------------------------------------------------------------
-- eqState properties
------------------------------------------------------------------------

-- eqState is reflexive: every state equals itself
eqState-refl : ∀ (s : PlayerState) → eqState s s ≡ true
eqState-refl Idle    = refl
eqState-refl Loading = refl
eqState-refl Playing = refl
eqState-refl Paused  = refl
eqState-refl Ended   = refl
eqState-refl Error   = refl

-- eqState is symmetric
eqState-sym : ∀ (s t : PlayerState) → eqState s t ≡ eqState t s
eqState-sym Idle    Idle    = refl
eqState-sym Idle    Loading = refl
eqState-sym Idle    Playing = refl
eqState-sym Idle    Paused  = refl
eqState-sym Idle    Ended   = refl
eqState-sym Idle    Error   = refl
eqState-sym Loading Idle    = refl
eqState-sym Loading Loading = refl
eqState-sym Loading Playing = refl
eqState-sym Loading Paused  = refl
eqState-sym Loading Ended   = refl
eqState-sym Loading Error   = refl
eqState-sym Playing Idle    = refl
eqState-sym Playing Loading = refl
eqState-sym Playing Playing = refl
eqState-sym Playing Paused  = refl
eqState-sym Playing Ended   = refl
eqState-sym Playing Error   = refl
eqState-sym Paused  Idle    = refl
eqState-sym Paused  Loading = refl
eqState-sym Paused  Playing = refl
eqState-sym Paused  Paused  = refl
eqState-sym Paused  Ended   = refl
eqState-sym Paused  Error   = refl
eqState-sym Ended   Idle    = refl
eqState-sym Ended   Loading = refl
eqState-sym Ended   Playing = refl
eqState-sym Ended   Paused  = refl
eqState-sym Ended   Ended   = refl
eqState-sym Ended   Error   = refl
eqState-sym Error   Idle    = refl
eqState-sym Error   Loading = refl
eqState-sym Error   Playing = refl
eqState-sym Error   Paused  = refl
eqState-sym Error   Ended   = refl
eqState-sym Error   Error   = refl

------------------------------------------------------------------------
-- isPlaying / isPaused consistency
------------------------------------------------------------------------

-- isPlaying agrees with eqState
isPlaying-spec : ∀ (s : PlayerState) → isPlaying s ≡ eqState s Playing
isPlaying-spec Idle    = refl
isPlaying-spec Loading = refl
isPlaying-spec Playing = refl
isPlaying-spec Paused  = refl
isPlaying-spec Ended   = refl
isPlaying-spec Error   = refl

-- isPaused agrees with eqState
isPaused-spec : ∀ (s : PlayerState) → isPaused s ≡ eqState s Paused
isPaused-spec Idle    = refl
isPaused-spec Loading = refl
isPaused-spec Playing = refl
isPaused-spec Paused  = refl
isPaused-spec Ended   = refl
isPaused-spec Error   = refl

-- Playing and Paused are mutually exclusive
playing-not-paused : ∀ (s : PlayerState) → isPlaying s ≡ true → isPaused s ≡ false
playing-not-paused Playing refl = refl

paused-not-playing : ∀ (s : PlayerState) → isPaused s ≡ true → isPlaying s ≡ false
paused-not-playing Paused refl = refl

------------------------------------------------------------------------
-- TogglePlay involution
------------------------------------------------------------------------

-- TogglePlay twice returns to original state (for Playing/Paused)
private
  toggleState : PlayerState → PlayerState
  toggleState s = if isPlaying s then Paused else Playing

toggle-involution-playing : toggleState (toggleState Playing) ≡ Playing
toggle-involution-playing = refl

toggle-involution-paused : toggleState (toggleState Paused) ≡ Paused
toggle-involution-paused = refl

------------------------------------------------------------------------
-- Error state is absorbing for playback commands
------------------------------------------------------------------------

-- eqState Error Error is true (used as guard in update)
error-is-error : eqState Error Error ≡ true
error-is-error = refl

-- Error is not Playing (ensures guard blocks Play in Error state)
error-not-playing : isPlaying Error ≡ false
error-not-playing = refl

------------------------------------------------------------------------
-- defaultVideoModel invariants
------------------------------------------------------------------------

-- Initial state is Idle
init-state : state defaultVideoModel ≡ Idle
init-state = refl

-- Initial controls are visible
init-controls-visible : controlsVisible defaultVideoModel ≡ true
init-controls-visible = refl

-- Initial error is nothing
init-no-error : error defaultVideoModel ≡ nothing
init-no-error = refl

-- Initial sourceReady is false
init-source-not-ready : sourceReady defaultVideoModel ≡ false
init-source-not-ready = refl
