{-# OPTIONS --without-K #-}

-- Tooltip: Hover tooltips and popovers
-- CSS classes: .agdelte-tooltip, .agdelte-tooltip__trigger,
--              .agdelte-tooltip__content, .agdelte-popover

module Agdelte.Html.Controls.Tooltip where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Tooltip position
------------------------------------------------------------------------

data TooltipPosition : Set where
  Top    : TooltipPosition
  Bottom : TooltipPosition
  Left   : TooltipPosition
  Right  : TooltipPosition

positionClass : TooltipPosition → String
positionClass Top    = "agdelte-tooltip--top"
positionClass Bottom = "agdelte-tooltip--bottom"
positionClass Left   = "agdelte-tooltip--left"
positionClass Right  = "agdelte-tooltip--right"

------------------------------------------------------------------------
-- Simple CSS-only tooltip (using title attribute)
------------------------------------------------------------------------

-- | Simple tooltip using native title attribute.
-- | Simplest approach, browser handles display.
simpleTooltip : ∀ {M A} → String → Node M A → Node M A
simpleTooltip tip content =
  span ( attr "title" tip ∷ [] )
    ( content ∷ [] )

------------------------------------------------------------------------
-- CSS-hover tooltip
------------------------------------------------------------------------

-- | CSS-based tooltip that shows on hover.
-- | Uses CSS :hover to show/hide (no JS needed).
-- | trigger: content that triggers tooltip
-- | tip: tooltip text
-- | position: where to show tooltip
tooltip : ∀ {M A}
        → Node M A           -- trigger content
        → String             -- tooltip text
        → TooltipPosition    -- position
        → Node M A
tooltip {M} {A} trigger tip position =
  span ( class ("agdelte-tooltip " ++ positionClass position) ∷ [] )
    ( span ( class "agdelte-tooltip__trigger" ∷ [] )
        ( trigger ∷ [] )
    ∷ span ( class "agdelte-tooltip__content"
           ∷ attr "role" "tooltip"
           ∷ [] )
        ( text tip ∷ [] )
    ∷ [] )
  where
    open import Data.String using (_++_)

-- | Tooltip with custom content (not just text)
tooltipCustom : ∀ {M A}
              → Node M A           -- trigger
              → Node M A           -- tooltip content
              → TooltipPosition
              → Node M A
tooltipCustom {M} {A} trigger content position =
  span ( class ("agdelte-tooltip " ++ positionClass position) ∷ [] )
    ( span ( class "agdelte-tooltip__trigger" ∷ [] )
        ( trigger ∷ [] )
    ∷ span ( class "agdelte-tooltip__content"
           ∷ attr "role" "tooltip"
           ∷ [] )
        ( content ∷ [] )
    ∷ [] )
  where
    open import Data.String using (_++_)

------------------------------------------------------------------------
-- Popover (click-triggered)
------------------------------------------------------------------------

-- | Popover that shows/hides on click.
-- | isOpen: extract open state from model
-- | toggleMsg: message to toggle popover
-- | trigger: content that triggers popover
-- | content: popover content
popover : ∀ {M A}
        → (M → Bool)         -- is open
        → A                  -- toggle message
        → Node M A           -- trigger
        → Node M A           -- popover content
        → Node M A
popover {M} {A} isOpen toggleMsg trigger content =
  div ( class "agdelte-popover" ∷ [] )
    ( button ( class "agdelte-popover__trigger"
             ∷ onClick toggleMsg
             ∷ [] )
        ( trigger ∷ [] )
    ∷ when isOpen
        (div ( class "agdelte-popover__content" ∷ [] )
          ( content ∷ [] ))
    ∷ [] )

-- | Popover with close button
popoverWithClose : ∀ {M A}
                 → (M → Bool)         -- is open
                 → A                  -- close message
                 → Node M A           -- trigger (opening handled separately)
                 → Node M A           -- popover content
                 → Node M A
popoverWithClose {M} {A} isOpen closeMsg trigger content =
  div ( class "agdelte-popover" ∷ [] )
    ( span ( class "agdelte-popover__trigger" ∷ [] )
        ( trigger ∷ [] )
    ∷ when isOpen
        (div ( class "agdelte-popover__content" ∷ [] )
          ( button ( class "agdelte-popover__close"
                   ∷ onClick closeMsg
                   ∷ [] )
              ( text "×" ∷ [] )
          ∷ content
          ∷ [] ))
    ∷ [] )

------------------------------------------------------------------------
-- Help icon with tooltip
------------------------------------------------------------------------

-- | Help icon (?) with tooltip.
helpIcon : ∀ {M A} → String → Node M A
helpIcon tip =
  tooltip
    (span ( class "agdelte-help-icon" ∷ [] ) ( text "?" ∷ [] ))
    tip
    Top

-- | Info icon (i) with tooltip.
infoIcon : ∀ {M A} → String → Node M A
infoIcon tip =
  tooltip
    (span ( class "agdelte-info-icon" ∷ [] ) ( text "ⓘ" ∷ [] ))
    tip
    Top
