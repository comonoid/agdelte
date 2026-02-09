{-# OPTIONS --without-K #-}

-- Toast: Notification messages that appear temporarily
-- CSS classes: .agdelte-toast-container, .agdelte-toast,
--              .agdelte-toast--info, .agdelte-toast--success,
--              .agdelte-toast--warning, .agdelte-toast--error,
--              .agdelte-toast__message, .agdelte-toast__close

module Agdelte.Html.Controls.Toast where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Function using (_∘_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Toast types
------------------------------------------------------------------------

data ToastType : Set where
  Info Success Warning Error : ToastType

------------------------------------------------------------------------
-- Toast record
------------------------------------------------------------------------

record ToastData : Set where
  constructor mkToast
  field
    toastId      : ℕ
    toastMessage : String
    toastType    : ToastType

open ToastData public

------------------------------------------------------------------------
-- Internal helpers
------------------------------------------------------------------------

private
  toastTypeClass : ToastType → String
  toastTypeClass Info    = "agdelte-toast agdelte-toast--info"
  toastTypeClass Success = "agdelte-toast agdelte-toast--success"
  toastTypeClass Warning = "agdelte-toast agdelte-toast--warning"
  toastTypeClass Error   = "agdelte-toast agdelte-toast--error"

  renderToast : ∀ {M A} → (ℕ → A) → ToastData → ℕ → Node M A
  renderToast dismissMsg t _ =
    div ( class (toastTypeClass (toastType t))
        ∷ attr "role" "alert"
        ∷ [] )
      ( span ( class "agdelte-toast__message" ∷ [] )
          ( text (toastMessage t) ∷ [] )
      ∷ button ( class "agdelte-toast__close"
               ∷ attr "aria-label" "Close"
               ∷ onClick (dismissMsg (toastId t))
               ∷ [] )
          ( text "×" ∷ [] )
      ∷ [] )

------------------------------------------------------------------------
-- Toast container
------------------------------------------------------------------------

-- | Container for toast notifications.
-- | getToasts: extract list of toasts from model
-- | dismissMsg: message constructor for dismissing a toast by id
toastContainer : ∀ {M A}
               → (M → List ToastData)   -- get toasts from model
               → (ℕ → A)                -- dismiss message by id
               → Node M A
toastContainer getToasts dismissMsg =
  div ( class "agdelte-toast-container"
      ∷ attr "aria-live" "polite"
      ∷ [] )
    ( foreach getToasts (renderToast dismissMsg)
    ∷ [] )

------------------------------------------------------------------------
-- Toast container with keyed rendering
------------------------------------------------------------------------

-- | Toast container with keyed rendering (better for add/remove animations).
-- | keyFn: function to extract unique string key from ToastData
toastContainerKeyed : ∀ {M A}
                    → (M → List ToastData)
                    → (ToastData → String)   -- key function
                    → (ℕ → A)
                    → Node M A
toastContainerKeyed getToasts keyFn dismissMsg =
  div ( class "agdelte-toast-container"
      ∷ attr "aria-live" "polite"
      ∷ [] )
    ( foreachKeyed getToasts keyFn (renderToast dismissMsg)
    ∷ [] )

------------------------------------------------------------------------
-- Simple toast (no container, single toast)
------------------------------------------------------------------------

-- | Single toast notification (without container).
-- | Use this if you manage positioning yourself.
toast : ∀ {M A}
      → (M → Bool)       -- is visible
      → ToastType        -- type
      → (M → String)     -- message
      → A                -- dismiss message
      → Node M A
toast isVisible ttype getMessage dismissMsg =
  when isVisible
    ( div ( class (toastTypeClass ttype)
          ∷ attr "role" "alert"
          ∷ [] )
        ( span ( class "agdelte-toast__message" ∷ [] )
            ( bindF getMessage ∷ [] )
        ∷ button ( class "agdelte-toast__close"
                 ∷ attr "aria-label" "Close"
                 ∷ onClick dismissMsg
                 ∷ [] )
            ( text "×" ∷ [] )
        ∷ [] ) )

------------------------------------------------------------------------
-- Toast with transition
------------------------------------------------------------------------

-- | Single toast with enter/leave transition
toastT : ∀ {M A}
       → (M → Bool)
       → ToastType
       → (M → String)
       → A
       → Transition
       → Node M A
toastT isVisible ttype getMessage dismissMsg trans =
  whenT isVisible trans
    ( div ( class (toastTypeClass ttype)
          ∷ attr "role" "alert"
          ∷ [] )
        ( span ( class "agdelte-toast__message" ∷ [] )
            ( bindF getMessage ∷ [] )
        ∷ button ( class "agdelte-toast__close"
                 ∷ attr "aria-label" "Close"
                 ∷ onClick dismissMsg
                 ∷ [] )
            ( text "×" ∷ [] )
        ∷ [] ) )

------------------------------------------------------------------------
-- Convenience constructors
------------------------------------------------------------------------

-- | Create info toast data
infoToast : ℕ → String → ToastData
infoToast id msg = mkToast id msg Info

-- | Create success toast data
successToast : ℕ → String → ToastData
successToast id msg = mkToast id msg Success

-- | Create warning toast data
warningToast : ℕ → String → ToastData
warningToast id msg = mkToast id msg Warning

-- | Create error toast data
errorToast : ℕ → String → ToastData
errorToast id msg = mkToast id msg Error
