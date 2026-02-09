{-# OPTIONS --without-K #-}

-- Accordion: Collapsible content sections
-- CSS classes: .agdelte-accordion, .agdelte-accordion__item,
--              .agdelte-accordion__header, .agdelte-accordion__content,
--              .agdelte-accordion__icon

module Agdelte.Html.Controls.Accordion where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Accordion item definition
------------------------------------------------------------------------

record AccordionItem (M : Set) (A : Set) : Set₁ where
  constructor mkAccordionItem
  field
    itemTitle   : String
    itemContent : Node M A

open AccordionItem public

------------------------------------------------------------------------
-- Helper
------------------------------------------------------------------------

private
  eqStr : String → String → Bool
  eqStr a b with a ≟ b
  ... | yes _ = true
  ... | no _  = false

------------------------------------------------------------------------
-- Single collapsible section
------------------------------------------------------------------------

-- | Single collapsible section.
-- | title: section header
-- | isOpen: extract open state from model
-- | toggleMsg: message to toggle open state
-- | content: section content
collapsible : ∀ {M A}
            → String         -- title
            → (M → Bool)     -- is open
            → A              -- toggle message
            → Node M A       -- content
            → Node M A
collapsible {M} {A} title isOpen toggleMsg content =
  div ( class "agdelte-accordion__item" ∷ [] )
    ( button ( class "agdelte-accordion__header"
             ∷ attrBind "aria-expanded" (mkBinding
                 (λ m → if isOpen m then "true" else "false")
                 eqStr)
             ∷ onClick toggleMsg
             ∷ [] )
        ( span ( class "agdelte-accordion__title" ∷ [] )
            ( text title ∷ [] )
        ∷ span ( attrBind "class" (mkBinding
                   (λ m → if isOpen m
                          then "agdelte-accordion__icon agdelte-accordion__icon--open"
                          else "agdelte-accordion__icon")
                   eqStr)
               ∷ [] )
            ( text "▼" ∷ [] )
        ∷ [] )
    ∷ when isOpen
        (div ( class "agdelte-accordion__content" ∷ [] )
          ( content ∷ [] ))
    ∷ [] )

------------------------------------------------------------------------
-- Accordion (single item open at a time)
------------------------------------------------------------------------

-- | Accordion with only one item open at a time.
-- | getOpenIndex: extract currently open item index (Nothing = all closed)
-- | toggleMsg: message to toggle item by index
-- | items: list of accordion items
accordion : ∀ {M A}
          → (M → Maybe ℕ)            -- open item index
          → (ℕ → A)                  -- toggle message (index)
          → List (AccordionItem M A)
          → Node M A
accordion {M} {A} getOpenIndex toggleMsg items =
  div ( class "agdelte-accordion" ∷ [] )
    (renderItems 0 items)
  where
    isOpen : ℕ → M → Bool
    isOpen idx m with getOpenIndex m
    ... | nothing = false
    ... | just openIdx = idx ≡ᵇ openIdx

    renderItem : ℕ → AccordionItem M A → Node M A
    renderItem idx item =
      div ( class "agdelte-accordion__item" ∷ [] )
        ( button ( class "agdelte-accordion__header"
                 ∷ attrBind "aria-expanded" (mkBinding
                     (λ m → if isOpen idx m then "true" else "false")
                     eqStr)
                 ∷ onClick (toggleMsg idx)
                 ∷ [] )
            ( span ( class "agdelte-accordion__title" ∷ [] )
                ( text (itemTitle item) ∷ [] )
            ∷ span ( attrBind "class" (mkBinding
                       (λ m → if isOpen idx m
                              then "agdelte-accordion__icon agdelte-accordion__icon--open"
                              else "agdelte-accordion__icon")
                       eqStr)
                   ∷ [] )
                ( text "▼" ∷ [] )
            ∷ [] )
        ∷ when (isOpen idx)
            (div ( class "agdelte-accordion__content" ∷ [] )
              ( itemContent item ∷ [] ))
        ∷ [] )

    {-# TERMINATING #-}
    renderItems : ℕ → List (AccordionItem M A) → List (Node M A)
    renderItems _ [] = []
    renderItems idx (item ∷ rest) = renderItem idx item ∷ renderItems (suc idx) rest

------------------------------------------------------------------------
-- Accordion (multiple items can be open)
------------------------------------------------------------------------

-- | Accordion where multiple items can be open simultaneously.
-- | isItemOpen: check if item at index is open
-- | toggleMsg: message to toggle item by index
-- | items: list of accordion items
accordionMulti : ∀ {M A}
               → (ℕ → M → Bool)         -- is item open (by index)
               → (ℕ → A)                -- toggle message (index)
               → List (AccordionItem M A)
               → Node M A
accordionMulti {M} {A} isItemOpen toggleMsg items =
  div ( class "agdelte-accordion agdelte-accordion--multi" ∷ [] )
    (renderItems 0 items)
  where
    renderItem : ℕ → AccordionItem M A → Node M A
    renderItem idx item =
      div ( class "agdelte-accordion__item" ∷ [] )
        ( button ( class "agdelte-accordion__header"
                 ∷ attrBind "aria-expanded" (mkBinding
                     (λ m → if isItemOpen idx m then "true" else "false")
                     eqStr)
                 ∷ onClick (toggleMsg idx)
                 ∷ [] )
            ( span ( class "agdelte-accordion__title" ∷ [] )
                ( text (itemTitle item) ∷ [] )
            ∷ span ( attrBind "class" (mkBinding
                       (λ m → if isItemOpen idx m
                              then "agdelte-accordion__icon agdelte-accordion__icon--open"
                              else "agdelte-accordion__icon")
                       eqStr)
                   ∷ [] )
                ( text "▼" ∷ [] )
            ∷ [] )
        ∷ when (isItemOpen idx)
            (div ( class "agdelte-accordion__content" ∷ [] )
              ( itemContent item ∷ [] ))
        ∷ [] )

    {-# TERMINATING #-}
    renderItems : ℕ → List (AccordionItem M A) → List (Node M A)
    renderItems _ [] = []
    renderItems idx (item ∷ rest) = renderItem idx item ∷ renderItems (suc idx) rest
