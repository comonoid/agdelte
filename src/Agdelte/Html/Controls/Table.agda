{-# OPTIONS --without-K #-}

-- Table: Simple table for small datasets
-- For large datasets use DataGrid with virtualization
-- CSS classes: .agdelte-table, .agdelte-table__header,
--              .agdelte-table__row, .agdelte-table__cell,
--              .agdelte-table--striped, .agdelte-table--bordered

module Agdelte.Html.Controls.Table where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Function using (_∘_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Internal helpers
------------------------------------------------------------------------

private
  -- Table elements (not in Node.agda but can use elem)
  table : ∀ {M A} → List (Attr M A) → List (Node M A) → Node M A
  table = elem "table"

  thead : ∀ {M A} → List (Attr M A) → List (Node M A) → Node M A
  thead = elem "thead"

  tbody : ∀ {M A} → List (Attr M A) → List (Node M A) → Node M A
  tbody = elem "tbody"

  tr : ∀ {M A} → List (Attr M A) → List (Node M A) → Node M A
  tr = elem "tr"

  th : ∀ {M A} → List (Attr M A) → List (Node M A) → Node M A
  th = elem "th"

  td : ∀ {M A} → List (Attr M A) → List (Node M A) → Node M A
  td = elem "td"

  -- Wrap cells in <td> elements
  wrapCells : ∀ {M A} → List (Node M A) → List (Node M A)
  wrapCells [] = []
  wrapCells (c ∷ cs) =
    td (class "agdelte-table__cell" ∷ []) (c ∷ [])
    ∷ wrapCells cs

  -- Render header cells
  renderHeaders : ∀ {M A} → List String → List (Node M A)
  renderHeaders [] = []
  renderHeaders (h ∷ hs) =
    th (class "agdelte-table__header" ∷ []) (text h ∷ [])
    ∷ renderHeaders hs

------------------------------------------------------------------------
-- Simple table
------------------------------------------------------------------------

-- | Render a simple table with headers and rows.
-- | headers: column headers
-- | rowRenderer: function that renders a row's cells
-- | getData: extract list of rows from model
basicTable : ∀ {R M A}
           → List String                 -- column headers
           → (R → List (Node M A))       -- row renderer (returns cells)
           → (M → List R)                -- data extractor
           → Node M A
basicTable {R} headers rowRenderer getData =
  table (class "agdelte-table" ∷ [])
    ( thead []
        ( tr [] (renderHeaders headers) ∷ [] )
    ∷ tbody []
        ( foreach getData (λ r _ →
            tr (class "agdelte-table__row" ∷ [])
              (wrapCells (rowRenderer r)))
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Clickable table
------------------------------------------------------------------------

-- | Table with clickable rows.
-- | onRowClick: handler called when a row is clicked
basicTableClickable : ∀ {R M A}
                    → List String
                    → (R → List (Node M A))
                    → (R → A)                  -- row click handler
                    → (M → List R)
                    → Node M A
basicTableClickable {R} headers rowRenderer onRowClick getData =
  table (class "agdelte-table agdelte-table--clickable" ∷ [])
    ( thead []
        ( tr [] (renderHeaders headers) ∷ [] )
    ∷ tbody []
        ( foreach getData (λ r _ →
            tr ( class "agdelte-table__row"
               ∷ style "cursor" "pointer"
               ∷ onClick (onRowClick r)
               ∷ [] )
              (wrapCells (rowRenderer r)))
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Striped table
------------------------------------------------------------------------

-- | Table with alternating row colors.
stripedTable : ∀ {R M A}
             → List String
             → (R → List (Node M A))
             → (M → List R)
             → Node M A
stripedTable {R} headers rowRenderer getData =
  table (class "agdelte-table agdelte-table--striped" ∷ [])
    ( thead []
        ( tr [] (renderHeaders headers) ∷ [] )
    ∷ tbody []
        ( foreach getData (λ r idx →
            tr (class (rowClass idx) ∷ [])
              (wrapCells (rowRenderer r)))
        ∷ [] )
    ∷ [] )
  where
    even : ℕ → Bool
    even zero = true
    even (suc zero) = false
    even (suc (suc n)) = even n

    rowClass : ℕ → String
    rowClass idx = if even idx
                   then "agdelte-table__row agdelte-table__row--even"
                   else "agdelte-table__row agdelte-table__row--odd"
      where open import Data.Bool using (if_then_else_)

------------------------------------------------------------------------
-- Bordered table
------------------------------------------------------------------------

-- | Table with cell borders.
borderedTable : ∀ {R M A}
              → List String
              → (R → List (Node M A))
              → (M → List R)
              → Node M A
borderedTable {R} headers rowRenderer getData =
  table (class "agdelte-table agdelte-table--bordered" ∷ [])
    ( thead []
        ( tr [] (renderHeaders headers) ∷ [] )
    ∷ tbody []
        ( foreach getData (λ r _ →
            tr (class "agdelte-table__row" ∷ [])
              (wrapCells (rowRenderer r)))
        ∷ [] )
    ∷ [] )
