{-# OPTIONS --without-K #-}

-- TabBar: Horizontal tabs with content panels
-- CSS classes: .agdelte-tabs, .agdelte-tabs__header, .agdelte-tabs__tab,
--              .agdelte-tabs__tab--active, .agdelte-tabs__panel

module Agdelte.Html.Controls.TabBar where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function using (_∘_)

open import Agdelte.Reactive.Node
open import Agdelte.Html.Controls.Util using (eqStr)

------------------------------------------------------------------------
-- Tab record: label + content
------------------------------------------------------------------------

record Tab (M : Set) (A : Set) : Set where
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
  renderTabHeader : ∀ {M A} → String → (M → ℕ) → (ℕ → A) → ℕ → Tab M A → Node M A
  renderTabHeader prefix getActive selectMsg idx tab =
    let tabId   = prefix ++ "-tab-" ++ show idx
        panelId = prefix ++ "-panel-" ++ show idx
    in
    button
      ( classBind (λ m →
          if getActive m ≡ᵇ idx
          then "agdelte-tabs__tab agdelte-tabs__tab--active"
          else "agdelte-tabs__tab")
      ∷ id' tabId
      ∷ attr "role" "tab"
      ∷ attr "aria-controls" panelId
      ∷ attrBind "aria-selected" (mkBinding
          (λ m → if getActive m ≡ᵇ idx then "true" else "false")
          eqStr)
      ∷ attrBind "tabindex" (mkBinding
          (λ m → if getActive m ≡ᵇ idx then "0" else "-1")
          eqStr)
      ∷ onClick (selectMsg idx)
      ∷ [] )
      ( text (Tab.tabLabel tab) ∷ [] )

  -- Render all tab headers with indices
  renderTabHeaders : ∀ {M A} → String → (M → ℕ) → (ℕ → A) → ℕ → List (Tab M A) → List (Node M A)
  renderTabHeaders prefix getActive selectMsg idx [] = []
  renderTabHeaders prefix getActive selectMsg idx (tab ∷ tabs) =
    renderTabHeader prefix getActive selectMsg idx tab
    ∷ renderTabHeaders prefix getActive selectMsg (suc idx) tabs

  -- Render single tab panel (conditionally shown)
  renderTabPanel : ∀ {M A} → String → (M → ℕ) → ℕ → Tab M A → Node M A
  renderTabPanel prefix getActive idx tab =
    let tabId   = prefix ++ "-tab-" ++ show idx
        panelId = prefix ++ "-panel-" ++ show idx
    in
    when (λ m → getActive m ≡ᵇ idx)
      ( div
          ( class "agdelte-tabs__panel"
          ∷ id' panelId
          ∷ attr "role" "tabpanel"
          ∷ attr "aria-labelledby" tabId
          ∷ [] )
          ( Tab.tabContent tab ∷ [] ) )

  -- Render all tab panels with indices
  renderTabPanels : ∀ {M A} → String → (M → ℕ) → ℕ → List (Tab M A) → List (Node M A)
  renderTabPanels prefix getActive idx [] = []
  renderTabPanels prefix getActive idx (tab ∷ tabs) =
    renderTabPanel prefix getActive idx tab
    ∷ renderTabPanels prefix getActive (suc idx) tabs

------------------------------------------------------------------------
-- Main tabBar function
------------------------------------------------------------------------

-- | Horizontal tab bar with content panels.
-- | prefix: ID prefix for aria linkage (tabs get <prefix>-tab-N, panels get <prefix>-panel-N)
-- | getActive: extract active tab index from model
-- | selectMsg: message constructor for tab selection
-- | keyMsg: message constructor for keyboard events (ArrowLeft/ArrowRight/Home/End)
-- | tabs: list of Tab records
tabBar : ∀ {M A} → String → (M → ℕ) → (ℕ → A) → (String → A) → List (Tab M A) → Node M A
tabBar prefix getActive selectMsg keyMsg tabs =
  div ( class "agdelte-tabs" ∷ [] )
    ( div ( class "agdelte-tabs__header"
          ∷ attr "role" "tablist"
          ∷ onKeyFiltered ("ArrowLeft" ∷ "ArrowRight" ∷ "Home" ∷ "End" ∷ []) keyMsg
          ∷ [] )
        (renderTabHeaders prefix getActive selectMsg 0 tabs)
    ∷ div ( class "agdelte-tabs__content" ∷ [] )
        (renderTabPanels prefix getActive 0 tabs)
    ∷ [] )

------------------------------------------------------------------------
-- Convenience: tabBar with transition animations
------------------------------------------------------------------------

private
  renderPanelT : ∀ {M A} → String → (M → ℕ) → Transition → ℕ → Tab M A → Node M A
  renderPanelT prefix getActive trans idx tab =
    let tabId   = prefix ++ "-tab-" ++ show idx
        panelId = prefix ++ "-panel-" ++ show idx
    in
    whenT (λ m → getActive m ≡ᵇ idx) trans
      ( div ( class "agdelte-tabs__panel"
            ∷ id' panelId
            ∷ attr "role" "tabpanel"
            ∷ attr "aria-labelledby" tabId
            ∷ [] )
          ( Tab.tabContent tab ∷ [] ) )

  renderPanelsT : ∀ {M A} → String → (M → ℕ) → Transition → ℕ → List (Tab M A) → List (Node M A)
  renderPanelsT prefix getActive trans idx [] = []
  renderPanelsT prefix getActive trans idx (tab ∷ rest) =
    renderPanelT prefix getActive trans idx tab ∷ renderPanelsT prefix getActive trans (suc idx) rest

-- | TabBar with enter/leave CSS transitions for panel switching
tabBarT : ∀ {M A} → String → (M → ℕ) → (ℕ → A) → (String → A) → Transition → List (Tab M A) → Node M A
tabBarT prefix getActive selectMsg keyMsg trans tabs =
  div ( class "agdelte-tabs" ∷ [] )
    ( div ( class "agdelte-tabs__header"
          ∷ attr "role" "tablist"
          ∷ onKeyFiltered ("ArrowLeft" ∷ "ArrowRight" ∷ "Home" ∷ "End" ∷ []) keyMsg
          ∷ [] )
        (renderTabHeaders prefix getActive selectMsg 0 tabs)
    ∷ div ( class "agdelte-tabs__content" ∷ [] )
        (renderPanelsT prefix getActive trans 0 tabs)
    ∷ [] )
