{-# OPTIONS --without-K #-}

-- DataGrid: Table/grid for displaying tabular data
-- CSS classes: .agdelte-grid, .agdelte-grid__header, .agdelte-grid__row,
--              .agdelte-grid__cell, .agdelte-grid__cell--header,
--              .agdelte-grid__row--clickable, .agdelte-grid__row--selected

module Agdelte.Html.Controls.DataGrid where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Column definition
------------------------------------------------------------------------

record Column (R : Set) (M : Set) (A : Set) : Set₁ where
  constructor mkColumn
  field
    colHeader : String
    colWidth  : String              -- CSS width ("100px", "1fr", "auto")
    colRender : R → Node M A        -- cell content renderer

open Column public

------------------------------------------------------------------------
-- Grid configuration
------------------------------------------------------------------------

record GridConfig (R : Set) (M : Set) (A : Set) : Set₁ where
  constructor mkGridConfig
  field
    columns    : List (Column R M A)
    rowKey     : R → String         -- unique key for keyed rendering
    onRowClick : Maybe (R → A)      -- optional row click handler

open GridConfig public

------------------------------------------------------------------------
-- Internal helpers
------------------------------------------------------------------------

private
  -- Render header cell
  renderHeaderCell : ∀ {R M A} → Column R M A → Node M A
  renderHeaderCell col =
    div ( class "agdelte-grid__cell agdelte-grid__cell--header"
        ∷ style "width" (colWidth col)
        ∷ [] )
      ( text (colHeader col) ∷ [] )

  -- Render data cell
  renderDataCell : ∀ {R M A} → R → Column R M A → Node M A
  renderDataCell row col =
    div ( class "agdelte-grid__cell"
        ∷ style "width" (colWidth col)
        ∷ [] )
      ( colRender col row ∷ [] )

  -- Render a single row
  renderRow : ∀ {R M A} → GridConfig R M A → R → ℕ → Node M A
  renderRow cfg row _ =
    case onRowClick cfg of λ where
      nothing →
        div ( class "agdelte-grid__row"
            ∷ keyAttr (rowKey cfg row)
            ∷ [] )
          (map (renderDataCell row) (columns cfg))
      (just handler) →
        div ( class "agdelte-grid__row agdelte-grid__row--clickable"
            ∷ keyAttr (rowKey cfg row)
            ∷ onClick (handler row)
            ∷ [] )
          (map (renderDataCell row) (columns cfg))
    where
      case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
      case x of f = f x

------------------------------------------------------------------------
-- Main dataGrid function
------------------------------------------------------------------------

-- | Data grid for displaying tabular data.
-- | config: grid configuration (columns, row key, click handler)
-- | getData: extract list of rows from model
dataGrid : ∀ {R M A} → GridConfig R M A → (M → List R) → Node M A
dataGrid cfg getData =
  div ( class "agdelte-grid" ∷ [] )
    ( div ( class "agdelte-grid__header" ∷ [] )
        (map renderHeaderCell (columns cfg))
    ∷ div ( class "agdelte-grid__body" ∷ [] )
        ( foreachKeyed getData (rowKey cfg) (renderRow cfg)
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Simple table (convenience function)
------------------------------------------------------------------------

-- | Simple table with string headers and custom row renderer.
-- | headers: list of column header strings
-- | renderRowCells: function to render row as list of cells
-- | getData: extract list of rows from model
simpleTable : ∀ {R M A} → List String → (R → List (Node M A)) → (M → List R) → Node M A
simpleTable headers renderRowCells getData =
  elem "table" ( class "agdelte-table" ∷ [] )
    ( elem "thead" []
        ( elem "tr" []
            (map (λ h → elem "th" [] ( text h ∷ [] )) headers)
        ∷ [] )
    ∷ elem "tbody" []
        ( foreach getData (λ row _ →
            elem "tr" []
              (map (λ cell → elem "td" [] ( cell ∷ [] )) (renderRowCells row)))
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Convenience: column constructors
------------------------------------------------------------------------

-- | Text column: display a string field
textColumn : ∀ {R M A} → String → String → (R → String) → Column R M A
textColumn header width getText = mkColumn header width (λ r → text (getText r))

-- | Node column: custom rendering
nodeColumn : ∀ {R M A} → String → String → (R → Node M A) → Column R M A
nodeColumn = mkColumn

-- | Action column: button in each row
actionColumn : ∀ {R M A} → String → String → String → (R → A) → Column R M A
actionColumn header width btnText handler =
  mkColumn header width (λ r →
    button ( class "agdelte-grid__action" ∷ onClick (handler r) ∷ [] )
      ( text btnText ∷ [] ))
