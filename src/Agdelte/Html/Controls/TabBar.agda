{-# OPTIONS --without-K #-}

-- TabBar: Horizontal tabs with content panels
-- CSS classes: .agdelte-tabs, .agdelte-tabs__header, .agdelte-tabs__tab,
--              .agdelte-tabs__tab--active, .agdelte-tabs__panel

module Agdelte.Html.Controls.TabBar where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function using (_∘_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Tab record: label + content
------------------------------------------------------------------------

record Tab (M : Set) (A : Set) : Set₁ where
  constructor mkTab
  field
    tabLabel   : String
    tabContent : Node M A

open Tab public

------------------------------------------------------------------------
-- Internal helpers
------------------------------------------------------------------------

private
  -- Render single tab header button
  renderTabHeader : ∀ {M A} → (M → ℕ) → (ℕ → A) → ℕ → Tab M A → Node M A
  renderTabHeader getActive selectMsg idx tab =
    button
      ( classBind (λ m →
          if getActive m ≡ᵇ idx
          then "agdelte-tabs__tab agdelte-tabs__tab--active"
          else "agdelte-tabs__tab")
      ∷ attr "role" "tab"
      ∷ attrBind "aria-selected" (mkBinding
          (λ m → if getActive m ≡ᵇ idx then "true" else "false")
          (λ a b → true))  -- always update (simple equality)
      ∷ onClick (selectMsg idx)
      ∷ [] )
      ( text (Tab.tabLabel tab) ∷ [] )

  -- Render all tab headers with indices
  {-# TERMINATING #-}
  renderTabHeaders : ∀ {M A} → (M → ℕ) → (ℕ → A) → ℕ → List (Tab M A) → List (Node M A)
  renderTabHeaders getActive selectMsg idx [] = []
  renderTabHeaders getActive selectMsg idx (tab ∷ tabs) =
    renderTabHeader getActive selectMsg idx tab
    ∷ renderTabHeaders getActive selectMsg (suc idx) tabs

  -- Render single tab panel (conditionally shown)
  renderTabPanel : ∀ {M A} → (M → ℕ) → ℕ → Tab M A → Node M A
  renderTabPanel getActive idx tab =
    when (λ m → getActive m ≡ᵇ idx)
      ( div
          ( class "agdelte-tabs__panel"
          ∷ attr "role" "tabpanel"
          ∷ [] )
          ( Tab.tabContent tab ∷ [] ) )

  -- Render all tab panels with indices
  {-# TERMINATING #-}
  renderTabPanels : ∀ {M A} → (M → ℕ) → ℕ → List (Tab M A) → List (Node M A)
  renderTabPanels getActive idx [] = []
  renderTabPanels getActive idx (tab ∷ tabs) =
    renderTabPanel getActive idx tab
    ∷ renderTabPanels getActive (suc idx) tabs

------------------------------------------------------------------------
-- Main tabBar function
------------------------------------------------------------------------

-- | Horizontal tab bar with content panels.
-- | getActive: extract active tab index from model
-- | selectMsg: message constructor for tab selection
-- | tabs: list of Tab records
tabBar : ∀ {M A} → (M → ℕ) → (ℕ → A) → List (Tab M A) → Node M A
tabBar getActive selectMsg tabs =
  div ( class "agdelte-tabs" ∷ [] )
    ( div ( class "agdelte-tabs__header" ∷ attr "role" "tablist" ∷ [] )
        (renderTabHeaders getActive selectMsg 0 tabs)
    ∷ div ( class "agdelte-tabs__content" ∷ [] )
        (renderTabPanels getActive 0 tabs)
    ∷ [] )

------------------------------------------------------------------------
-- Convenience: tabBar with transition animations
------------------------------------------------------------------------

private
  renderPanelT : ∀ {M A} → (M → ℕ) → Transition → ℕ → Tab M A → Node M A
  renderPanelT getActive trans idx tab =
    whenT (λ m → getActive m ≡ᵇ idx) trans
      ( div ( class "agdelte-tabs__panel" ∷ attr "role" "tabpanel" ∷ [] )
          ( Tab.tabContent tab ∷ [] ) )

  {-# TERMINATING #-}
  renderPanelsT : ∀ {M A} → (M → ℕ) → Transition → ℕ → List (Tab M A) → List (Node M A)
  renderPanelsT getActive trans idx [] = []
  renderPanelsT getActive trans idx (tab ∷ rest) =
    renderPanelT getActive trans idx tab ∷ renderPanelsT getActive trans (suc idx) rest

-- | TabBar with enter/leave CSS transitions for panel switching
tabBarT : ∀ {M A} → (M → ℕ) → (ℕ → A) → Transition → List (Tab M A) → Node M A
tabBarT getActive selectMsg trans tabs =
  div ( class "agdelte-tabs" ∷ [] )
    ( div ( class "agdelte-tabs__header" ∷ attr "role" "tablist" ∷ [] )
        (renderTabHeaders getActive selectMsg 0 tabs)
    ∷ div ( class "agdelte-tabs__content" ∷ [] )
        (renderPanelsT getActive trans 0 tabs)
    ∷ [] )
