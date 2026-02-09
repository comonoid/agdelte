{-# OPTIONS --without-K #-}

-- Sidebar: Navigation sidebar with collapsible sections
-- CSS classes: .agdelte-sidebar, .agdelte-sidebar__header,
--              .agdelte-sidebar__nav, .agdelte-sidebar__item,
--              .agdelte-sidebar__link, .agdelte-sidebar--collapsed

module Agdelte.Html.Controls.Sidebar where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Sidebar item definition
------------------------------------------------------------------------

record SidebarItem (A : Set) : Set where
  constructor mkSidebarItem
  field
    sidebarLabel : String
    sidebarIcon  : Maybe String   -- optional icon (text/emoji)
    sidebarMsg   : A              -- click message

open SidebarItem public

------------------------------------------------------------------------
-- Sidebar section (group of items)
------------------------------------------------------------------------

record SidebarSection (A : Set) : Set₁ where
  constructor mkSection
  field
    sectionTitle : String
    sectionItems : List (SidebarItem A)

open SidebarSection public

------------------------------------------------------------------------
-- Helper
------------------------------------------------------------------------

private
  eqStr : String → String → Bool
  eqStr a b with a ≟ b
  ... | yes _ = true
  ... | no _  = false

------------------------------------------------------------------------
-- Simple sidebar (flat list of items)
------------------------------------------------------------------------

-- | Simple sidebar with flat list of items.
-- | title: sidebar header title
-- | activeIndex: extract active item index from model
-- | items: list of sidebar items
simpleSidebar : ∀ {M A}
              → String                  -- title
              → (M → Maybe ℕ)           -- active item index
              → List (SidebarItem A)
              → Node M A
simpleSidebar {M} {A} title activeIndex items =
  nav ( class "agdelte-sidebar" ∷ [] )
    ( div ( class "agdelte-sidebar__header" ∷ [] )
        ( text title ∷ [] )
    ∷ ul ( class "agdelte-sidebar__nav" ∷ [] )
        (renderItems 0 items)
    ∷ [] )
  where
    isActive : ℕ → M → Bool
    isActive idx m with activeIndex m
    ... | nothing = false
    ... | just active = idx ≡ᵇ active

    renderItem : ℕ → SidebarItem A → Node M A
    renderItem idx item =
      li ( class "agdelte-sidebar__item" ∷ [] )
        ( button ( attrBind "class" (mkBinding
                     (λ m → if isActive idx m
                            then "agdelte-sidebar__link agdelte-sidebar__link--active"
                            else "agdelte-sidebar__link")
                     eqStr)
                 ∷ onClick (sidebarMsg item)
                 ∷ [] )
            ( (case sidebarIcon item of λ where
                nothing → []
                (just icon) → span ( class "agdelte-sidebar__icon" ∷ [] )
                                ( text icon ∷ [] ) ∷ [])
            ++ ( span ( class "agdelte-sidebar__label" ∷ [] )
                   ( text (sidebarLabel item) ∷ [] )
               ∷ [] ) )
        ∷ [] )
      where
        case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
        case x of f = f x
        open import Data.List using (_++_)

    {-# TERMINATING #-}
    renderItems : ℕ → List (SidebarItem A) → List (Node M A)
    renderItems _ [] = []
    renderItems idx (item ∷ rest) = renderItem idx item ∷ renderItems (suc idx) rest

------------------------------------------------------------------------
-- Collapsible sidebar
------------------------------------------------------------------------

-- | Sidebar that can be collapsed.
-- | title: sidebar header title
-- | isCollapsed: extract collapsed state from model
-- | toggleMsg: message to toggle collapse
-- | activeIndex: extract active item index from model
-- | items: list of sidebar items
collapsibleSidebar : ∀ {M A}
                   → String                  -- title
                   → (M → Bool)              -- is collapsed
                   → A                       -- toggle message
                   → (M → Maybe ℕ)           -- active item index
                   → List (SidebarItem A)
                   → Node M A
collapsibleSidebar {M} {A} title isCollapsed toggleMsg activeIndex items =
  nav ( attrBind "class" (mkBinding
          (λ m → if isCollapsed m
                 then "agdelte-sidebar agdelte-sidebar--collapsed"
                 else "agdelte-sidebar")
          eqStr)
      ∷ [] )
    ( div ( class "agdelte-sidebar__header" ∷ [] )
        ( button ( class "agdelte-sidebar__toggle"
                 ∷ onClick toggleMsg
                 ∷ [] )
            ( text "☰" ∷ [] )
        ∷ when (not ∘ isCollapsed)
            (span ( class "agdelte-sidebar__title" ∷ [] )
              ( text title ∷ [] ))
        ∷ [] )
    ∷ ul ( class "agdelte-sidebar__nav" ∷ [] )
        (renderItems 0 items)
    ∷ [] )
  where
    isActive : ℕ → M → Bool
    isActive idx m with activeIndex m
    ... | nothing = false
    ... | just active = idx ≡ᵇ active

    renderItem : ℕ → SidebarItem A → Node M A
    renderItem idx item =
      li ( class "agdelte-sidebar__item" ∷ [] )
        ( button ( attrBind "class" (mkBinding
                     (λ m → if isActive idx m
                            then "agdelte-sidebar__link agdelte-sidebar__link--active"
                            else "agdelte-sidebar__link")
                     eqStr)
                 ∷ attr "title" (sidebarLabel item)  -- tooltip when collapsed
                 ∷ onClick (sidebarMsg item)
                 ∷ [] )
            ( (case sidebarIcon item of λ where
                nothing → []
                (just icon) → span ( class "agdelte-sidebar__icon" ∷ [] )
                                ( text icon ∷ [] ) ∷ [])
            ++ ( when (not ∘ isCollapsed)
                   (span ( class "agdelte-sidebar__label" ∷ [] )
                     ( text (sidebarLabel item) ∷ [] ))
               ∷ [] ) )
        ∷ [] )
      where
        case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
        case x of f = f x
        open import Data.List using (_++_)

    {-# TERMINATING #-}
    renderItems : ℕ → List (SidebarItem A) → List (Node M A)
    renderItems _ [] = []
    renderItems idx (item ∷ rest) = renderItem idx item ∷ renderItems (suc idx) rest

------------------------------------------------------------------------
-- Convenience constructors
------------------------------------------------------------------------

-- | Create sidebar item with icon
sidebarItem : ∀ {A} → String → String → A → SidebarItem A
sidebarItem label icon msg = mkSidebarItem label (just icon) msg

-- | Create sidebar item without icon
sidebarItemPlain : ∀ {A} → String → A → SidebarItem A
sidebarItemPlain label msg = mkSidebarItem label nothing msg
