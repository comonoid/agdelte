{-# OPTIONS --without-K #-}

-- Modal: Overlay dialog with backdrop
-- CSS classes: .agdelte-modal, .agdelte-modal__backdrop,
--              .agdelte-modal__content, .agdelte-modal--open

module Agdelte.Html.Controls.Modal where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Function using (_∘_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Focus trap sentinels
------------------------------------------------------------------------

-- | Invisible sentinel divs with tabindex="0" placed at the start
-- | and end of the modal content area.  When Tab moves focus past
-- | the last focusable element the end sentinel receives focus and
-- | redirects it to the first focusable child inside the modal.
-- | Shift+Tab past the first element hits the start sentinel which
-- | redirects to the last focusable child.  This is the standard
-- | "JS-free" focus trap pattern (inline onfocus handler).
private
  -- Redirect focus to the first focusable element inside .agdelte-modal__content
  focusFirst : String
  focusFirst =
    "var m=this.closest('.agdelte-modal--open');" ++
    "if(m){var f=m.querySelector('.agdelte-modal__content [tabindex],." ++
    "agdelte-modal__content button,.agdelte-modal__content a,.agdelte-modal__content input,.agdelte-modal__content select,.agdelte-modal__content textarea');" ++
    "if(f)f.focus()}"

  -- Redirect focus to the last focusable element inside .agdelte-modal__content
  focusLast : String
  focusLast =
    "var m=this.closest('.agdelte-modal--open');" ++
    "if(m){var a=m.querySelectorAll('.agdelte-modal__content [tabindex],." ++
    "agdelte-modal__content button,.agdelte-modal__content a,.agdelte-modal__content input,.agdelte-modal__content select,.agdelte-modal__content textarea');" ++
    "if(a.length)a[a.length-1].focus()}"

  sentinelAttrs : ∀ {M A} → String → List (Attr M A)
  sentinelAttrs handler =
      class "agdelte-modal__sentinel"
    ∷ attr "tabindex" "0"
    ∷ attr "onfocus" handler
    ∷ []

  startSentinel : ∀ {M A} → Node M A
  startSentinel = div (sentinelAttrs focusLast) []

  endSentinel : ∀ {M A} → Node M A
  endSentinel = div (sentinelAttrs focusFirst) []

------------------------------------------------------------------------
-- Basic modal
------------------------------------------------------------------------

-- | Modal dialog overlay.
-- | isOpen: extract open state from model
-- | closeMsg: message to send when closing (via close button or backdrop)
-- | content: modal content
modal : ∀ {M A} → (M → Bool) → A → Node M A → Node M A
modal isOpen closeMsg content =
  when isOpen
    ( div ( class "agdelte-modal agdelte-modal--open"
          ∷ onKeyFiltered ("Escape" ∷ []) (λ _ → closeMsg)
          ∷ [] )
        ( startSentinel
        ∷ div ( class "agdelte-modal__backdrop"
              ∷ onClick closeMsg
              ∷ [] )
            []
        ∷ div ( class "agdelte-modal__content" ∷ [] )
            ( content ∷ [] )
        ∷ endSentinel
        ∷ [] ) )

------------------------------------------------------------------------
-- Modal with transition
------------------------------------------------------------------------

-- | Modal with enter/leave CSS transitions
modalT : ∀ {M A} → (M → Bool) → A → Transition → Node M A → Node M A
modalT isOpen closeMsg trans content =
  whenT isOpen trans
    ( div ( class "agdelte-modal agdelte-modal--open"
          ∷ onKeyFiltered ("Escape" ∷ []) (λ _ → closeMsg)
          ∷ [] )
        ( startSentinel
        ∷ div ( class "agdelte-modal__backdrop"
              ∷ onClick closeMsg
              ∷ [] )
            []
        ∷ div ( class "agdelte-modal__content" ∷ [] )
            ( content ∷ [] )
        ∷ endSentinel
        ∷ [] ) )

------------------------------------------------------------------------
-- Modal without backdrop close
------------------------------------------------------------------------

-- | Modal that doesn't close when clicking backdrop
modalStrict : ∀ {M A} → (M → Bool) → Node M A → Node M A
modalStrict isOpen content =
  when isOpen
    ( div ( class "agdelte-modal agdelte-modal--open"
          ∷ [] )
        ( div ( class "agdelte-modal__backdrop" ∷ [] )
            []
        ∷ div ( class "agdelte-modal__content" ∷ [] )
            ( content ∷ [] )
        ∷ [] ) )

------------------------------------------------------------------------
-- Confirmation dialog
------------------------------------------------------------------------

-- | Simple confirmation dialog with title, message, and two buttons
confirmDialog : ∀ {M A}
              → (M → Bool)    -- isOpen
              → String        -- title
              → String        -- message
              → String        -- confirm button text
              → String        -- cancel button text
              → A             -- on confirm
              → A             -- on cancel
              → Node M A
confirmDialog isOpen title message confirmText cancelText onConfirm onCancel =
  modal isOpen onCancel
    ( div ( class "agdelte-modal__dialog" ∷ [] )
        ( h2 ( class "agdelte-modal__title" ∷ [] )
            ( text title ∷ [] )
        ∷ p ( class "agdelte-modal__message" ∷ [] )
            ( text message ∷ [] )
        ∷ div ( class "agdelte-modal__actions" ∷ [] )
            ( button ( class "agdelte-modal__btn agdelte-modal__btn--cancel"
                     ∷ onClick onCancel
                     ∷ [] )
                ( text cancelText ∷ [] )
            ∷ button ( class "agdelte-modal__btn agdelte-modal__btn--confirm"
                     ∷ onClick onConfirm
                     ∷ [] )
                ( text confirmText ∷ [] )
            ∷ [] )
        ∷ [] ) )

------------------------------------------------------------------------
-- Alert dialog
------------------------------------------------------------------------

-- | Simple alert dialog with just OK button
alertDialog : ∀ {M A}
            → (M → Bool)    -- isOpen
            → String        -- title
            → String        -- message
            → A             -- on ok/close
            → Node M A
alertDialog isOpen title message onOk =
  modal isOpen onOk
    ( div ( class "agdelte-modal__dialog" ∷ [] )
        ( h2 ( class "agdelte-modal__title" ∷ [] )
            ( text title ∷ [] )
        ∷ p ( class "agdelte-modal__message" ∷ [] )
            ( text message ∷ [] )
        ∷ div ( class "agdelte-modal__actions" ∷ [] )
            ( button ( class "agdelte-modal__btn agdelte-modal__btn--ok"
                     ∷ onClick onOk
                     ∷ [] )
                ( text "OK" ∷ [] )
            ∷ [] )
        ∷ [] ) )
