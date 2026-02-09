{-# OPTIONS --without-K #-}

-- Modal: Overlay dialog with backdrop
-- CSS classes: .agdelte-modal, .agdelte-modal__backdrop,
--              .agdelte-modal__content, .agdelte-modal--open

module Agdelte.Html.Controls.Modal where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Function using (_∘_)

open import Agdelte.Reactive.Node

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
          ∷ attr "role" "dialog"
          ∷ attr "aria-modal" "true"
          ∷ [] )
        ( div ( class "agdelte-modal__backdrop"
              ∷ onClick closeMsg
              ∷ [] )
            []
        ∷ div ( class "agdelte-modal__content" ∷ [] )
            ( content ∷ [] )
        ∷ [] ) )

------------------------------------------------------------------------
-- Modal with transition
------------------------------------------------------------------------

-- | Modal with enter/leave CSS transitions
modalT : ∀ {M A} → (M → Bool) → A → Transition → Node M A → Node M A
modalT isOpen closeMsg trans content =
  whenT isOpen trans
    ( div ( class "agdelte-modal agdelte-modal--open"
          ∷ attr "role" "dialog"
          ∷ attr "aria-modal" "true"
          ∷ [] )
        ( div ( class "agdelte-modal__backdrop"
              ∷ onClick closeMsg
              ∷ [] )
            []
        ∷ div ( class "agdelte-modal__content" ∷ [] )
            ( content ∷ [] )
        ∷ [] ) )

------------------------------------------------------------------------
-- Modal without backdrop close
------------------------------------------------------------------------

-- | Modal that doesn't close when clicking backdrop
modalStrict : ∀ {M A} → (M → Bool) → Node M A → Node M A
modalStrict isOpen content =
  when isOpen
    ( div ( class "agdelte-modal agdelte-modal--open"
          ∷ attr "role" "dialog"
          ∷ attr "aria-modal" "true"
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
