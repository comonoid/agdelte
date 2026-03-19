{-# OPTIONS --without-K #-}

-- DataGrid: Table/grid for displaying tabular data
-- CSS classes: .agdelte-grid, .agdelte-grid__header, .agdelte-grid__row,
--              .agdelte-grid__cell, .agdelte-grid__cell--header,
--              .agdelte-grid__row--clickable, .agdelte-grid__row--selected

module Agdelte.Html.Controls.DataGrid where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map; null)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)

open import Agdelte.Reactive.Node
open import Agdelte.Html.Controls.Util using (case_of_; noDataText)
open import Agdelte.Data.Array as Arr using (Array; CmpResult; cmpLT; cmpEQ; cmpGT; fromList; toList; sortBy)

------------------------------------------------------------------------
-- Column definition
------------------------------------------------------------------------

record Column (R : Set) (M : Set) (A : Set) : Set where
  constructor mkColumn
  field
    colHeader : String
    colWidth  : String              -- CSS width ("100px", "1fr", "auto")
    colRender : R → Node M A        -- cell content renderer

open Column public

------------------------------------------------------------------------
-- Grid configuration
------------------------------------------------------------------------

record GridConfig (R : Set) (M : Set) (A : Set) : Set where
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
        ∷ attr "role" "columnheader"
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
            ∷ attr "role" "row"
            ∷ keyAttr (rowKey cfg row)
            ∷ [] )
          (map (renderDataCell row) (columns cfg))
      (just handler) →
        div ( class "agdelte-grid__row agdelte-grid__row--clickable"
            ∷ attr "role" "row"
            ∷ keyAttr (rowKey cfg row)
            ∷ onClick (handler row)
            ∷ [] )
          (map (renderDataCell row) (columns cfg))

------------------------------------------------------------------------
-- Main dataGrid function
------------------------------------------------------------------------

-- | Data grid for displaying tabular data.
-- | config: grid configuration (columns, row key, click handler)
-- | getData: extract list of rows from model
dataGrid : ∀ {R M A} → GridConfig R M A → (M → List R) → Node M A
dataGrid cfg getData =
  div ( class "agdelte-grid" ∷ attr "role" "grid" ∷ [] )
    ( div ( class "agdelte-grid__header" ∷ attr "role" "row" ∷ [] )
        (map renderHeaderCell (columns cfg))
    ∷ div ( class "agdelte-grid__body" ∷ [] )
        ( when (null ∘ getData)
            (div ( class "agdelte-grid__row agdelte-grid__empty"
                 ∷ attr "role" "row"
                 ∷ [] )
              ( text noDataText ∷ [] ))
        ∷ foreachKeyed getData (rowKey cfg) (renderRow cfg)
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
        ( when (null ∘ getData)
            (elem "tr" []
              ( elem "td" ( attr "colspan" (show (length headers)) ∷ [] )
                  ( text noDataText ∷ [] )
              ∷ [] ))
        ∷ foreach getData (λ row _ →
            elem "tr" []
              (map (λ cell → elem "td" [] ( cell ∷ [] )) (renderRowCells row)))
        ∷ [] )
    ∷ [] )
  where
    open import Data.List using (length)
    open import Data.Nat.Show using (show)

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

------------------------------------------------------------------------
-- Sort state
------------------------------------------------------------------------

-- | Sort state: column index and ascending flag
SortState : Set
SortState = Maybe (ℕ × Bool)

------------------------------------------------------------------------
-- Sortable grid configuration
------------------------------------------------------------------------

record SortableGridConfig (R : Set) (M : Set) (A : Set) : Set where
  constructor mkSortableGridConfig
  field
    sgColumns    : List (Column R M A)
    sgRowKey     : R → String
    sgOnRowClick : Maybe (R → A)
    sgSortState  : M → SortState
    sgOnSort     : ℕ → A                -- message when header clicked
    sgComparators : List (R → R → CmpResult)  -- one comparator per column

open SortableGridConfig public

------------------------------------------------------------------------
-- Sortable grid internals
------------------------------------------------------------------------

private
  -- Render sortable header cell with click handler and indicator
  renderSortableHeaderCell : ∀ {R M A}
                           → ℕ → (ℕ → A) → SortState → Column R M A → Node M A
  renderSortableHeaderCell colIdx onSort' sortSt col =
    let indicator = case sortSt of λ where
          nothing → ""
          (just (si , asc)) →
            if si ≡ᵇ colIdx
            then (if asc then " ▲" else " ▼")
            else ""
    in div ( class "agdelte-grid__cell agdelte-grid__cell--header agdelte-grid__cell--sortable"
           ∷ attr "role" "columnheader"
           ∷ style "width" (colWidth col)
           ∷ style "cursor" "pointer"
           ∷ onClick (onSort' colIdx)
           ∷ [] )
         ( text (colHeader col ++ indicator) ∷ [] )
    where
      open import Data.String using (_++_)

  renderSortableHeaders : ∀ {R M A}
                        → List (Column R M A) → (ℕ → A) → SortState → ℕ
                        → List (Node M A)
  renderSortableHeaders [] _ _ _ = []
  renderSortableHeaders (c ∷ cs) onSort' ss idx =
    renderSortableHeaderCell idx onSort' ss c
    ∷ renderSortableHeaders cs onSort' ss (suc idx)

  -- Get comparator at index
  getComparator : ∀ {R : Set} → ℕ → List (R → R → CmpResult) → Maybe (R → R → CmpResult)
  getComparator _ [] = nothing
  getComparator zero (c ∷ _) = just c
  getComparator (suc n) (_ ∷ cs) = getComparator n cs

  -- Flip comparator for descending
  flipCmp : CmpResult → CmpResult
  flipCmp cmpLT = cmpGT
  flipCmp cmpEQ = cmpEQ
  flipCmp cmpGT = cmpLT

  -- Sort rows using sort state
  sortRows : ∀ {R : Set}
           → SortState → List (R → R → CmpResult) → List R → List R
  sortRows nothing _ rows = rows
  sortRows (just (colIdx , asc)) comparators rows =
    case getComparator colIdx comparators of λ where
      nothing → rows
      (just cmp) →
        let cmp' = if asc then cmp
                   else (λ a b → flipCmp (cmp a b))
        in toList (sortBy cmp' (fromList rows))

------------------------------------------------------------------------
-- Sortable data grid
------------------------------------------------------------------------

-- | Sortable data grid with clickable column headers and sort indicators.
-- | cfg: sortable grid configuration
-- | getData: extract list of rows from model
sortableGrid : ∀ {R M A} → SortableGridConfig R M A → (M → List R) → Node M A
sortableGrid cfg getData =
  div ( class "agdelte-grid agdelte-grid--sortable" ∷ attr "role" "grid" ∷ [] )
    ( foreach (λ m → m ∷ []) (λ m _ →
        let ss = sgSortState cfg m
            sortedData = sortRows ss (sgComparators cfg) (getData m)
            gridCfg = mkGridConfig (sgColumns cfg) (sgRowKey cfg) (sgOnRowClick cfg)
        in div []
          ( div ( class "agdelte-grid__header" ∷ attr "role" "row" ∷ [] )
              (renderSortableHeaders (sgColumns cfg) (sgOnSort cfg) ss 0)
          ∷ div ( class "agdelte-grid__body" ∷ [] )
              ( when (λ _ → null sortedData)
                  (div ( class "agdelte-grid__row agdelte-grid__empty"
                       ∷ attr "role" "row"
                       ∷ [] )
                    ( text noDataText ∷ [] ))
              ∷ foreach (λ _ → sortedData) (renderRow gridCfg)
              ∷ [] )
          ∷ [] ))
    ∷ [] )
