{-# OPTIONS --without-K #-}

-- Popover: Floating content panels
-- Like tooltip but with rich interactive content
-- CSS classes: .agdelte-popover-container, .agdelte-popover,
--              .agdelte-popover__trigger, .agdelte-popover__content,
--              .agdelte-popover--top/bottom/left/right,
--              .agdelte-popover--menu, .agdelte-popover--confirm

module Agdelte.Html.Controls.Popover where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool)
open import Data.Product using (_×_; _,_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Popover position
------------------------------------------------------------------------

data PopoverPosition : Set where
  Top    : PopoverPosition
  Bottom : PopoverPosition
  Left   : PopoverPosition
  Right  : PopoverPosition

positionClass : PopoverPosition → String
positionClass Top    = "agdelte-popover--top"
positionClass Bottom = "agdelte-popover--bottom"
positionClass Left   = "agdelte-popover--left"
positionClass Right  = "agdelte-popover--right"

------------------------------------------------------------------------
-- Basic popover
------------------------------------------------------------------------

-- | Popover with trigger and content
-- | isOpen: extract open state from model
-- | toggle: message to toggle popover
-- | trigger: element that triggers the popover
-- | content: popover content
popover : ∀ {M A}
        → (M → Bool)          -- isOpen
        → A                   -- toggle message
        → Node M A            -- trigger element
        → Node M A            -- popover content
        → Node M A
popover isOpen toggle trigger content =
  div (class "agdelte-popover-container" ∷ [])
    ( -- Trigger
      div ( class "agdelte-popover__trigger"
          ∷ onClick toggle
          ∷ [] )
        ( trigger ∷ [] )
    -- Popover panel (conditional)
    ∷ when isOpen
        ( div (class "agdelte-popover agdelte-popover--bottom" ∷ [])
            ( content ∷ [] ) )
    ∷ [] )

------------------------------------------------------------------------
-- Popover with position
------------------------------------------------------------------------

-- | Popover with configurable position
popoverPositioned : ∀ {M A}
                  → (M → Bool)
                  → A
                  → PopoverPosition
                  → Node M A
                  → Node M A
                  → Node M A
popoverPositioned isOpen toggle pos trigger content =
  div (class "agdelte-popover-container" ∷ [])
    ( div ( class "agdelte-popover__trigger"
          ∷ onClick toggle
          ∷ [] )
        ( trigger ∷ [] )
    ∷ when isOpen
        ( div (class ("agdelte-popover " ++ positionClass pos) ∷ [])
            ( content ∷ [] ) )
    ∷ [] )

------------------------------------------------------------------------
-- Popover with close button
------------------------------------------------------------------------

-- | Popover with explicit close button
popoverWithClose : ∀ {M A}
                 → (M → Bool)
                 → A              -- open/toggle
                 → A              -- close
                 → Node M A
                 → Node M A
                 → Node M A
popoverWithClose isOpen toggle close trigger content =
  div (class "agdelte-popover-container" ∷ [])
    ( div ( class "agdelte-popover__trigger"
          ∷ onClick toggle
          ∷ [] )
        ( trigger ∷ [] )
    ∷ when isOpen
        ( div (class "agdelte-popover agdelte-popover--bottom" ∷ [])
            ( -- Close button
              button ( class "agdelte-popover__close"
                     ∷ onClick close
                     ∷ [] )
                ( text "×" ∷ [] )
            -- Content
            ∷ div (class "agdelte-popover__content" ∷ [])
                ( content ∷ [] )
            ∷ [] ) )
    ∷ [] )

------------------------------------------------------------------------
-- Popover with header
------------------------------------------------------------------------

-- | Popover with header title and close button
popoverWithHeader : ∀ {M A}
                  → (M → Bool)
                  → A
                  → A              -- close
                  → String         -- header title
                  → Node M A       -- trigger
                  → Node M A       -- content
                  → Node M A
popoverWithHeader isOpen toggle close title trigger content =
  div (class "agdelte-popover-container" ∷ [])
    ( div ( class "agdelte-popover__trigger"
          ∷ onClick toggle
          ∷ [] )
        ( trigger ∷ [] )
    ∷ when isOpen
        ( div (class "agdelte-popover agdelte-popover--bottom" ∷ [])
            ( -- Header
              div (class "agdelte-popover__header" ∷ [])
                ( span (class "agdelte-popover__title" ∷ [])
                    ( text title ∷ [] )
                ∷ button ( class "agdelte-popover__close"
                         ∷ onClick close
                         ∷ [] )
                    ( text "×" ∷ [] )
                ∷ [] )
            -- Content
            ∷ div (class "agdelte-popover__content" ∷ [])
                ( content ∷ [] )
            ∷ [] ) )
    ∷ [] )

------------------------------------------------------------------------
-- Dropdown menu (popover variant)
------------------------------------------------------------------------

-- | Popover styled as dropdown menu
popoverMenu : ∀ {M A}
            → (M → Bool)
            → A                       -- toggle
            → Node M A                -- trigger
            → List (String × A)       -- menu items (label, message)
            → Node M A
popoverMenu {M} {A} isOpen toggle trigger items =
  div (class "agdelte-popover-container" ∷ [])
    ( div ( class "agdelte-popover__trigger"
          ∷ onClick toggle
          ∷ [] )
        ( trigger ∷ [] )
    ∷ when isOpen
        ( div (class "agdelte-popover agdelte-popover--bottom agdelte-popover--menu" ∷ [])
            (renderItems items) )
    ∷ [] )
  where
    renderItems : List (String × A) → List (Node M A)
    renderItems [] = []
    renderItems ((lbl , msg) ∷ rest) =
      button ( class "agdelte-popover__menu-item"
             ∷ onClick msg
             ∷ [] )
        ( text lbl ∷ [] )
      ∷ renderItems rest

------------------------------------------------------------------------
-- Confirmation popover
------------------------------------------------------------------------

-- | Popover for confirming actions
popoverConfirm : ∀ {M A}
               → (M → Bool)
               → A              -- cancel (close)
               → A              -- confirm
               → String         -- message
               → Node M A       -- trigger
               → Node M A
popoverConfirm isOpen cancel confirm message trigger =
  div (class "agdelte-popover-container" ∷ [])
    ( div (class "agdelte-popover__trigger" ∷ [])
        ( trigger ∷ [] )
    ∷ when isOpen
        ( div (class "agdelte-popover agdelte-popover--bottom agdelte-popover--confirm" ∷ [])
            ( -- Message
              div (class "agdelte-popover__message" ∷ [])
                ( text message ∷ [] )
            -- Buttons
            ∷ div (class "agdelte-popover__actions" ∷ [])
                ( button ( class "agdelte-popover__btn agdelte-popover__btn--cancel"
                         ∷ onClick cancel
                         ∷ [] )
                    ( text "Cancel" ∷ [] )
                ∷ button ( class "agdelte-popover__btn agdelte-popover__btn--confirm"
                         ∷ onClick confirm
                         ∷ [] )
                    ( text "Confirm" ∷ [] )
                ∷ [] )
            ∷ [] ) )
    ∷ [] )
