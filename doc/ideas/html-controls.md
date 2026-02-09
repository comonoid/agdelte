# HTML Controls Library (Agdelte.Html.Controls)

Pure Agda library of common UI widgets built on top of `Agdelte.Reactive.Node`.
No JavaScript required — all logic in Agda, compiled to JS.

## Design Principles

1. **Composable** — widgets are `Node Model Msg` functions, easily embedded
2. **Themeable** — CSS classes, not inline styles; users provide their own CSS
3. **Accessible** — ARIA attributes, keyboard navigation where applicable
4. **Type-safe** — Agda types enforce correct usage (e.g., Tab requires non-empty list)

## Core Widgets

### Navigation & Layout

#### TabBar
Horizontal tabs with content panels.

```agda
record Tab (M : Set) (A : Set) : Set where
  constructor mkTab
  field
    label   : String
    content : Node M A

-- Active tab index in model
tabBar : ∀ {M A} → (M → ℕ) → (ℕ → A) → List (Tab M A) → Node M A
```

Usage:
```agda
data Msg = SelectTab ℕ | ...

tabs : List (Tab Model Msg)
tabs = mkTab "Overview" overviewContent
     ∷ mkTab "Settings" settingsContent
     ∷ mkTab "Help" helpContent
     ∷ []

view = tabBar activeTab SelectTab tabs
```

#### Accordion
Collapsible sections, one or multiple open.

```agda
record AccordionItem (M : Set) (A : Set) : Set where
  constructor mkAccordionItem
  field
    header  : String
    content : Node M A
    isOpen  : M → Bool

accordion : ∀ {M A} → (ℕ → A) → List (AccordionItem M A) → Node M A
```

#### Sidebar
Collapsible side navigation.

```agda
sidebar : ∀ {M A} → (M → Bool) → A → Node M A → Node M A → Node M A
-- (isOpen) (toggleMsg) (sidebarContent) (mainContent)
```

### Data Display

#### DataGrid
Fast virtualized grid for large datasets.

```agda
record Column (R : Set) (M : Set) (A : Set) : Set where
  constructor mkColumn
  field
    header    : String
    width     : String           -- CSS width ("100px", "1fr", etc.)
    render    : R → Node M A     -- cell renderer
    sortKey   : Maybe (R → R → Ordering)  -- optional sorting

record GridConfig (R : Set) (M : Set) (A : Set) : Set where
  constructor mkGridConfig
  field
    columns     : List (Column R M A)
    rowKey      : R → String     -- unique key for keyed rendering
    onRowClick  : Maybe (R → A)
    pageSize    : ℕ              -- for pagination/virtualization

dataGrid : ∀ {R M A} → GridConfig R M A → (M → List R) → Node M A
```

#### Table
Simple table (non-virtualized, for small datasets).

```agda
simpleTable : ∀ {R M A} → List String → (R → List (Node M A)) → (M → List R) → Node M A
-- headers, row renderer, data extractor
```

#### TreeView
Hierarchical tree with expand/collapse.

```agda
record TreeNode (D : Set) : Set where
  constructor mkTreeNode
  field
    value    : D
    children : List (TreeNode D)

treeView : ∀ {D M A}
         → (D → String)           -- label extractor
         → (M → D → Bool)         -- isExpanded
         → (D → A)                -- toggle message
         → (M → List (TreeNode D))
         → Node M A
```

### Forms & Input

#### Dropdown / Select
Dropdown menu with search/filter option.

```agda
record SelectOption (V : Set) : Set where
  constructor mkOption
  field
    value : V
    label : String

dropdown : ∀ {V M A}
         → (M → Maybe V)          -- selected value
         → (V → A)                -- on select
         → List (SelectOption V)
         → Node M A

searchableDropdown : ∀ {V M A}
                   → (M → Maybe V)
                   → (M → String)      -- search text
                   → (String → A)      -- on search change
                   → (V → A)           -- on select
                   → List (SelectOption V)
                   → Node M A
```

#### Checkbox / CheckboxGroup
```agda
checkbox : ∀ {M A} → String → (M → Bool) → A → Node M A

checkboxGroup : ∀ {V M A}
              → (M → List V)           -- selected values
              → (V → A)                -- toggle message
              → List (SelectOption V)
              → Node M A
```

#### RadioGroup
```agda
radioGroup : ∀ {V M A}
           → String                    -- group name
           → (M → V)                   -- selected value
           → (V → A)                   -- on select
           → List (SelectOption V)
           → Node M A
```

#### Slider / RangeInput
```agda
slider : ∀ {M A}
       → Float → Float → Float        -- min, max, step
       → (M → Float)                  -- current value
       → (Float → A)                  -- on change
       → Node M A

rangeSlider : ∀ {M A}
            → Float → Float → Float
            → (M → Float × Float)     -- (low, high)
            → (Float → Float → A)     -- on change
            → Node M A
```

#### DatePicker
```agda
-- Requires date type (could use ℕ for unix timestamp or custom record)
record Date : Set where
  constructor mkDate
  field year : ℕ ; month : ℕ ; day : ℕ

datePicker : ∀ {M A}
           → (M → Maybe Date)
           → (Date → A)
           → Node M A
```

### Feedback & Overlay

#### Modal / Dialog
```agda
modal : ∀ {M A}
      → (M → Bool)                    -- isOpen
      → A                             -- close message
      → Node M A                      -- content
      → Node M A

-- With backdrop click to close
modalWithBackdrop : ∀ {M A} → (M → Bool) → A → Node M A → Node M A
```

#### Toast / Notification
```agda
data ToastType : Set where
  Info Success Warning Error : ToastType

record ToastData : Set where
  constructor mkToast
  field
    message : String
    type    : ToastType
    id      : ℕ

toastContainer : ∀ {M A}
               → (M → List ToastData)
               → (ℕ → A)              -- dismiss by id
               → Node M A
```

#### Tooltip
```agda
tooltip : ∀ {M A}
        → String                      -- tooltip text
        → Node M A                    -- trigger element
        → Node M A

-- With custom content
tooltipCustom : ∀ {M A} → Node M A → Node M A → Node M A
```

#### Popover
```agda
popover : ∀ {M A}
        → (M → Bool)                  -- isOpen
        → A                           -- toggle message
        → Node M A                    -- trigger
        → Node M A                    -- content
        → Node M A
```

### Progress & Loading

#### ProgressBar
```agda
progressBar : ∀ {M A} → (M → Float) → Node M A  -- 0.0 to 1.0

-- Indeterminate (animated)
progressIndeterminate : ∀ {M A} → Node M A
```

#### Spinner
```agda
spinner : ∀ {M A} → Node M A
spinnerWithText : ∀ {M A} → String → Node M A
```

#### Skeleton
Placeholder while loading.
```agda
skeleton : ∀ {M A} → String → String → Node M A  -- width, height
skeletonText : ∀ {M A} → ℕ → Node M A            -- number of lines
```

### Navigation

#### Breadcrumb
```agda
record BreadcrumbItem (A : Set) : Set where
  constructor mkBreadcrumb
  field
    label : String
    action : Maybe A                  -- Nothing for current (no link)

breadcrumb : ∀ {M A} → List (BreadcrumbItem A) → Node M A
```

#### Pagination
```agda
pagination : ∀ {M A}
           → (M → ℕ)                  -- current page
           → (M → ℕ)                  -- total pages
           → (ℕ → A)                  -- go to page
           → Node M A
```

#### Stepper
Multi-step wizard indicator.
```agda
record Step : Set where
  constructor mkStep
  field
    label : String
    description : Maybe String

stepper : ∀ {M A}
        → (M → ℕ)                     -- current step
        → List Step
        → Node M A
```

## Module Structure

```
Agdelte/
  Html/
    Controls.agda           -- re-exports all
    Controls/
      TabBar.agda
      Accordion.agda
      Sidebar.agda
      DataGrid.agda
      Table.agda
      TreeView.agda
      Dropdown.agda
      Checkbox.agda
      Radio.agda
      Slider.agda
      DatePicker.agda
      Modal.agda
      Toast.agda
      Tooltip.agda
      Popover.agda
      Progress.agda
      Spinner.agda
      Skeleton.agda
      Breadcrumb.agda
      Pagination.agda
      Stepper.agda
```

## CSS Framework Integration

Widgets output semantic HTML with BEM-style class names:

```
.agdelte-tabs
.agdelte-tabs__header
.agdelte-tabs__tab
.agdelte-tabs__tab--active
.agdelte-tabs__panel

.agdelte-accordion
.agdelte-accordion__item
.agdelte-accordion__header
.agdelte-accordion__content
.agdelte-accordion__content--open
```

Users can:
1. Use provided `agdelte-controls.css` (minimal, functional)
2. Override with custom CSS
3. Use CSS variables for theming

## Implementation Priority

### Phase 1: Core (most commonly needed)
1. TabBar
2. Modal
3. Dropdown
4. DataGrid (basic, no virtualization)
5. Toast

### Phase 2: Forms
6. Checkbox / CheckboxGroup
7. RadioGroup
8. Slider
9. Pagination

### Phase 3: Layout & Navigation
10. Accordion
11. Sidebar
12. Breadcrumb
13. TreeView

### Phase 4: Polish
14. Tooltip / Popover
15. Progress / Spinner / Skeleton
16. DatePicker
17. Stepper
18. DataGrid virtualization

## SVG Components Integration

This library focuses on HTML-based controls. SVG-based components (charts, diagrams,
icons, gauges, etc.) will be in a separate module `Agdelte.Svg.Controls` — see
`doc/ideas/svg-controls.md`.

However, both libraries share the same `Node M A` type, so they compose naturally:

```agda
-- HTML control with embedded SVG chart
dashboard : Node Model Msg
dashboard =
  div [ class "dashboard" ]
    ( tabBar activeTab SelectTab
        ( mkTab "Overview" (
            div []
              ( statsCards        -- HTML
              ∷ lineChart data    -- SVG (from Agdelte.Svg.Controls)
              ∷ [] ))
        ∷ mkTab "Details" detailsTable
        ∷ [] )
    ∷ [] )
```

Shared design principles:
- Same `Node M A` return type
- Same BEM-style class naming (`.agdelte-*`)
- Same theming via CSS variables
- Consistent API patterns (extractors from model, message constructors)

## Open Questions

1. **Virtualization strategy** — How to implement efficient virtual scrolling in Agda?
   - Option A: Calculate visible range in Agda, render only those items
   - Option B: Render all, let CSS `content-visibility: auto` handle it
   - Option C: Hybrid with JS helper for scroll position

2. **Animation** — Use `whenT` transitions or CSS-only?
   - Accordion expand/collapse
   - Modal fade in/out
   - Toast slide in

3. **Focus management** — How to handle focus trapping in modals?
   - May need `Cmd.focus` integration

4. **Keyboard navigation** — Full ARIA compliance?
   - Arrow keys in tabs, dropdowns
   - Escape to close modals
   - Could use global `onKeyDown` subscription

5. **Internationalization** — How to handle translated labels?
   - Pass String directly (user handles i18n)
   - Or create `I18n` module with message keys
