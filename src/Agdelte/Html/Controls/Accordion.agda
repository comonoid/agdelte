{-# OPTIONS --without-K #-}

-- Accordion: Collapsible content sections
-- CSS classes: .agdelte-accordion, .agdelte-accordion__item,
--              .agdelte-accordion__header, .agdelte-accordion__content,
--              .agdelte-accordion__icon

module Agdelte.Html.Controls.Accordion where

open import Data.String using (String; _≟_; _++_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node
open import Agdelte.Html.Controls.Util using (eqStr)

------------------------------------------------------------------------
-- Default accordion transition
------------------------------------------------------------------------

private
  accordionTransition : Transition
  accordionTransition = mkTransition "agdelte-enter-slide-down" "agdelte-leave-slide-down" 300

------------------------------------------------------------------------
-- Accordion item definition
------------------------------------------------------------------------

record AccordionItem (M : Set) (A : Set) : Set where
  constructor mkAccordionItem
  field
    itemTitle   : String
    itemContent : Node M A

open AccordionItem public

------------------------------------------------------------------------
-- Collapsible configuration
------------------------------------------------------------------------

record CollapsibleConfig (M A : Set) : Set where
  constructor mkCollapsible
  field
    panelId   : String       -- unique ID prefix
    title     : String       -- section header
    isOpen    : M → Bool     -- extract open state from model
    toggleMsg : A            -- message to toggle open state
    content   : Node M A     -- section content

open CollapsibleConfig public

------------------------------------------------------------------------
-- Single collapsible section
------------------------------------------------------------------------

collapsibleWith : ∀ {M A} → CollapsibleConfig M A → Node M A
collapsibleWith = collapsible'
  where
    collapsible' : _
    collapsible' cfg =
      let open CollapsibleConfig cfg renaming (panelId to pid; title to t; isOpen to io; toggleMsg to tm; content to c)
          headerId  = pid ++ "-header"
          contentId = pid ++ "-panel"
      in
      div ( class "agdelte-accordion__item" ∷ [] )
        ( button ( class "agdelte-accordion__header"
                 ∷ id' headerId
                 ∷ attr "aria-controls" contentId
                 ∷ attrBind "aria-expanded" (mkBinding
                     (λ m → if io m then "true" else "false")
                     eqStr)
                 ∷ onClick tm
                 ∷ [] )
            ( span ( class "agdelte-accordion__title" ∷ [] )
                ( text t ∷ [] )
            ∷ span ( attrBind "class" (mkBinding
                       (λ m → if io m
                              then "agdelte-accordion__icon agdelte-accordion__icon--open"
                              else "agdelte-accordion__icon")
                       eqStr)
                   ∷ attr "aria-hidden" "true"
                   ∷ [] )
                ( text "▼" ∷ [] )
            ∷ [] )
        ∷ whenT io accordionTransition
            (div ( class "agdelte-accordion__content"
                 ∷ id' contentId
                 ∷ attr "role" "region"
                 ∷ attr "aria-labelledby" headerId
                 ∷ [] )
              ( c ∷ [] ))
        ∷ [] )

-- | Backward-compatible positional-args version
collapsible : ∀ {M A}
            → String         -- panel ID prefix
            → String         -- title
            → (M → Bool)     -- is open
            → A              -- toggle message
            → Node M A       -- content
            → Node M A
collapsible {M} {A} panelId title isOpen toggleMsg content =
  let headerId = panelId ++ "-header"
      contentId = panelId ++ "-panel"
  in
  div ( class "agdelte-accordion__item" ∷ [] )
    ( button ( class "agdelte-accordion__header"
             ∷ id' headerId
             ∷ attr "aria-controls" contentId
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
               ∷ attr "aria-hidden" "true"
               ∷ [] )
            ( text "▼" ∷ [] )
        ∷ [] )
    ∷ whenT isOpen accordionTransition
        (div ( class "agdelte-accordion__content"
             ∷ id' contentId
             ∷ attr "role" "region"
             ∷ attr "aria-labelledby" headerId
             ∷ [] )
          ( content ∷ [] ))
    ∷ [] )

------------------------------------------------------------------------
-- Accordion configuration (record config pattern)
------------------------------------------------------------------------

record AccordionConfig (M A : Set) : Set where
  constructor mkAccordionConfig
  field
    accPrefix       : String                  -- ID prefix for aria
    accGetOpenIndex : M → Maybe ℕ            -- open item index (Nothing = all closed)
    accToggleMsg    : ℕ → A                  -- toggle message by index
    accItems        : List (AccordionItem M A) -- accordion items

open AccordionConfig public

record AccordionMultiConfig (M A : Set) : Set where
  constructor mkAccordionMultiConfig
  field
    amPrefix     : String                    -- ID prefix for aria
    amIsItemOpen : ℕ → M → Bool            -- check if item at index is open
    amToggleMsg  : ℕ → A                   -- toggle message by index
    amItems      : List (AccordionItem M A) -- accordion items

open AccordionMultiConfig public

------------------------------------------------------------------------
-- Backward-compatible positional-args API
------------------------------------------------------------------------

-- | Accordion with only one item open at a time.
-- | prefix: ID prefix for aria attributes (items get <prefix>-N-header/panel)
-- | getOpenIndex: extract currently open item index (Nothing = all closed)
-- | toggleMsg: message to toggle item by index
-- | items: list of accordion items
accordion : ∀ {M A}
          → String                     -- ID prefix
          → (M → Maybe ℕ)            -- open item index
          → (ℕ → A)                  -- toggle message (index)
          → List (AccordionItem M A)
          → Node M A
accordion {M} {A} prefix getOpenIndex toggleMsg items =
  div ( class "agdelte-accordion" ∷ [] )
    (renderItems 0 items)
  where
    isItemOpen : ℕ → M → Bool
    isItemOpen idx m with getOpenIndex m
    ... | nothing = false
    ... | just openIdx = idx ≡ᵇ openIdx

    renderItem : ℕ → AccordionItem M A → Node M A
    renderItem idx item =
      let panelId  = prefix ++ "-" ++ show idx
          headerId = panelId ++ "-header"
          contentId = panelId ++ "-panel"
      in
      div ( class "agdelte-accordion__item" ∷ [] )
        ( button ( class "agdelte-accordion__header"
                 ∷ id' headerId
                 ∷ attr "aria-controls" contentId
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
                   ∷ attr "aria-hidden" "true"
                   ∷ [] )
                ( text "▼" ∷ [] )
            ∷ [] )
        ∷ whenT (isItemOpen idx) accordionTransition
            (div ( class "agdelte-accordion__content"
                 ∷ id' contentId
                 ∷ attr "role" "region"
                 ∷ attr "aria-labelledby" headerId
                 ∷ [] )
              ( itemContent item ∷ [] ))
        ∷ [] )

    renderItems : ℕ → List (AccordionItem M A) → List (Node M A)
    renderItems _ [] = []
    renderItems idx (item ∷ rest) = renderItem idx item ∷ renderItems (suc idx) rest

------------------------------------------------------------------------
-- Accordion (multiple items can be open)
------------------------------------------------------------------------

-- | Accordion where multiple items can be open simultaneously.
-- | prefix: ID prefix for aria attributes (items get <prefix>-N-header/panel)
-- | isItemOpen: check if item at index is open
-- | toggleMsg: message to toggle item by index
-- | items: list of accordion items
accordionMulti : ∀ {M A}
               → String                   -- ID prefix
               → (ℕ → M → Bool)         -- is item open (by index)
               → (ℕ → A)                -- toggle message (index)
               → List (AccordionItem M A)
               → Node M A
accordionMulti {M} {A} prefix isItemOpen toggleMsg items =
  div ( class "agdelte-accordion agdelte-accordion--multi" ∷ [] )
    (renderItems 0 items)
  where
    renderItem : ℕ → AccordionItem M A → Node M A
    renderItem idx item =
      let panelId  = prefix ++ "-" ++ show idx
          headerId = panelId ++ "-header"
          contentId = panelId ++ "-panel"
      in
      div ( class "agdelte-accordion__item" ∷ [] )
        ( button ( class "agdelte-accordion__header"
                 ∷ id' headerId
                 ∷ attr "aria-controls" contentId
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
                   ∷ attr "aria-hidden" "true"
                   ∷ [] )
                ( text "▼" ∷ [] )
            ∷ [] )
        ∷ whenT (isItemOpen idx) accordionTransition
            (div ( class "agdelte-accordion__content"
                 ∷ id' contentId
                 ∷ attr "role" "region"
                 ∷ attr "aria-labelledby" headerId
                 ∷ [] )
              ( itemContent item ∷ [] ))
        ∷ [] )

    renderItems : ℕ → List (AccordionItem M A) → List (Node M A)
    renderItems _ [] = []
    renderItems idx (item ∷ rest) = renderItem idx item ∷ renderItems (suc idx) rest

------------------------------------------------------------------------
-- Config-based API (unified pattern)
------------------------------------------------------------------------

-- | Accordion (single open) from config.
accordionWith : ∀ {M A} → AccordionConfig M A → Node M A
accordionWith cfg = accordion (accPrefix cfg) (accGetOpenIndex cfg)
                              (accToggleMsg cfg) (accItems cfg)

-- | Accordion (multi open) from config.
accordionMultiWith : ∀ {M A} → AccordionMultiConfig M A → Node M A
accordionMultiWith cfg = accordionMulti (amPrefix cfg) (amIsItemOpen cfg)
                                        (amToggleMsg cfg) (amItems cfg)
