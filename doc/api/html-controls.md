# Agdelte.Html.Controls

Pure Agda library of common HTML-based UI widgets.
All components return `Node M A` and compose naturally with other Agdelte elements.

## Design Principles

1. **Composable** — widgets are `Node M A` functions, easily embedded
2. **Themeable** — BEM-style CSS classes, users provide their own CSS
3. **Accessible** — ARIA attributes, semantic HTML
4. **Type-safe** — Agda types enforce correct usage

## Quick Start

```agda
open import Agdelte.Html.Controls

-- Use individual controls
view = tabBar getActiveTab SetTab tabs
```

## Navigation & Layout

### TabBar

Horizontal tabs with content panels.

```agda
record Tab (M : Set) (A : Set) : Set where
  constructor mkTab
  field
    label   : String
    content : Node M A

tabBar : (M → ℕ) → (ℕ → A) → List (Tab M A) → Node M A
```

CSS classes: `.agdelte-tabs`, `.agdelte-tabs__header`, `.agdelte-tabs__tab`, `.agdelte-tabs__tab--active`, `.agdelte-tabs__panel`

### Accordion

Collapsible sections.

```agda
record AccordionItem (M : Set) (A : Set) : Set where
  constructor mkAccordionItem
  field
    header  : String
    content : Node M A
    isOpen  : M → Bool

accordion : (ℕ → A) → List (AccordionItem M A) → Node M A
```

CSS classes: `.agdelte-accordion`, `.agdelte-accordion__item`, `.agdelte-accordion__header`, `.agdelte-accordion__content--open`

### Sidebar

Collapsible side navigation.

```agda
sidebar : (M → Bool) → A → Node M A → Node M A → Node M A
-- (isOpen) (toggleMsg) (sidebarContent) (mainContent)
```

CSS classes: `.agdelte-sidebar-layout`, `.agdelte-sidebar`, `.agdelte-sidebar--open`, `.agdelte-main-content`

### Breadcrumb

Navigation path.

```agda
record BreadcrumbItem (A : Set) : Set where
  constructor mkBreadcrumb
  field
    label  : String
    action : Maybe A   -- Nothing for current (no link)

breadcrumb : List (BreadcrumbItem A) → Node M A
```

CSS classes: `.agdelte-breadcrumb`, `.agdelte-breadcrumb__item`, `.agdelte-breadcrumb__separator`

## Data Display

### DataGrid

Fast grid for datasets with sorting support.

```agda
record Column (R : Set) (M : Set) (A : Set) : Set where
  constructor mkColumn
  field
    header  : String
    width   : String              -- CSS width
    render  : R → Node M A
    sortKey : Maybe (R → R → Ordering)

record GridConfig (R : Set) (M : Set) (A : Set) : Set where
  constructor mkGridConfig
  field
    columns    : List (Column R M A)
    rowKey     : R → String
    onRowClick : Maybe (R → A)
    pageSize   : ℕ

dataGrid : GridConfig R M A → (M → List R) → Node M A
```

CSS classes: `.agdelte-grid`, `.agdelte-grid__header`, `.agdelte-grid__row`, `.agdelte-grid__cell`

### Table

Simple table for small datasets.

```agda
simpleTable : List String → (R → List (Node M A)) → (M → List R) → Node M A
-- headers, row renderer, data extractor
```

CSS classes: `.agdelte-table`, `.agdelte-table__header`, `.agdelte-table__row`, `.agdelte-table__cell`

### TreeView

Hierarchical tree with expand/collapse.

```agda
record TreeNode (D : Set) : Set where
  constructor mkTreeNode
  field
    value    : D
    children : List (TreeNode D)

treeView : (D → String) → (M → D → Bool) → (D → A) → (M → List (TreeNode D)) → Node M A
-- labelFn, isExpanded, toggleMsg, getData
```

CSS classes: `.agdelte-tree`, `.agdelte-tree__node`, `.agdelte-tree__toggle`, `.agdelte-tree__label`

## Forms & Input

### Dropdown

Dropdown menu with options.

```agda
record SelectOption (V : Set) : Set where
  constructor mkOption
  field
    value : V
    label : String

dropdown : (M → Maybe V) → (V → A) → List (SelectOption V) → Node M A
searchableDropdown : (M → Maybe V) → (M → String) → (String → A) → (V → A) → List (SelectOption V) → Node M A
```

CSS classes: `.agdelte-dropdown`, `.agdelte-dropdown__trigger`, `.agdelte-dropdown__menu`, `.agdelte-dropdown__option`

### Checkbox

```agda
checkbox : String → (M → Bool) → A → Node M A
```

CSS classes: `.agdelte-checkbox`, `.agdelte-checkbox__input`, `.agdelte-checkbox__label`

### RadioGroup

```agda
radioGroup : String → (M → V) → (V → A) → List (SelectOption V) → Node M A
```

CSS classes: `.agdelte-radio-group`, `.agdelte-radio`, `.agdelte-radio__input`, `.agdelte-radio__label`

### Slider

```agda
slider : Float → Float → Float → (M → Float) → (Float → A) → Node M A
-- min, max, step, getValue, onChange
```

CSS classes: `.agdelte-slider`, `.agdelte-slider__track`, `.agdelte-slider__thumb`

### DatePicker

```agda
record Date : Set where
  constructor mkDate
  field year : ℕ ; month : ℕ ; day : ℕ

datePicker : (M → Maybe Date) → (Date → A) → Node M A
```

CSS classes: `.agdelte-datepicker`, `.agdelte-datepicker__calendar`, `.agdelte-datepicker__day`

## Feedback & Overlay

### Modal

```agda
modal : (M → Bool) → A → Node M A → Node M A
-- isOpen, closeMsg, content
modalWithBackdrop : (M → Bool) → A → Node M A → Node M A
```

CSS classes: `.agdelte-modal`, `.agdelte-modal__backdrop`, `.agdelte-modal__content`

### Toast

```agda
data ToastType : Set where
  Info Success Warning Error : ToastType

record ToastData : Set where
  constructor mkToast
  field
    message : String
    type    : ToastType
    id      : ℕ

toastContainer : (M → List ToastData) → (ℕ → A) → Node M A
```

CSS classes: `.agdelte-toast-container`, `.agdelte-toast`, `.agdelte-toast--success`, `.agdelte-toast--error`

### Tooltip

```agda
tooltip : String → Node M A → Node M A
tooltipCustom : Node M A → Node M A → Node M A
```

CSS classes: `.agdelte-tooltip-wrapper`, `.agdelte-tooltip`

### Popover

```agda
popover : (M → Bool) → A → Node M A → Node M A → Node M A
-- isOpen, toggleMsg, trigger, content
```

CSS classes: `.agdelte-popover`, `.agdelte-popover__trigger`, `.agdelte-popover__content`

## Progress & Loading

### Progress

```agda
progressBar : (M → Float) → Node M A  -- 0.0 to 1.0
progressIndeterminate : Node M A
```

CSS classes: `.agdelte-progress`, `.agdelte-progress__bar`, `.agdelte-progress--indeterminate`

### Spinner

```agda
spinner : Node M A
spinnerWithText : String → Node M A
```

CSS classes: `.agdelte-spinner`

### Skeleton

```agda
skeleton : String → String → Node M A  -- width, height
skeletonText : ℕ → Node M A            -- number of lines
```

CSS classes: `.agdelte-skeleton`, `.agdelte-skeleton--text`

## Navigation

### Pagination

```agda
pagination : (M → ℕ) → (M → ℕ) → (ℕ → A) → Node M A
-- currentPage, totalPages, goToPage
```

CSS classes: `.agdelte-pagination`, `.agdelte-pagination__page`, `.agdelte-pagination__page--active`

### Stepper

Multi-step wizard indicator.

```agda
record Step : Set where
  constructor mkStep
  field
    label       : String
    description : Maybe String

stepper : (M → ℕ) → List Step → Node M A
```

CSS classes: `.agdelte-stepper`, `.agdelte-stepper__step`, `.agdelte-stepper__step--active`, `.agdelte-stepper__step--completed`

## Module Structure

```
Agdelte/Html/Controls.agda       -- re-exports all
Agdelte/Html/Controls/
  TabBar.agda
  Modal.agda
  Dropdown.agda
  Toast.agda
  DataGrid.agda
  Table.agda
  TreeView.agda
  Checkbox.agda
  RadioGroup.agda
  Slider.agda
  DatePicker.agda
  Accordion.agda
  Sidebar.agda
  Breadcrumb.agda
  Tooltip.agda
  Popover.agda
  Progress.agda
  Spinner.agda
  Skeleton.agda
  Pagination.agda
  Stepper.agda
```

## CSS Theming

All controls use BEM-style class names. Override with custom CSS:

```css
.agdelte-tabs__tab--active {
  background: var(--primary-color);
  color: white;
}

.agdelte-modal__backdrop {
  background: rgba(0, 0, 0, 0.5);
}
```

CSS variables for theming:

```css
:root {
  --agdelte-primary: #3b82f6;
  --agdelte-success: #22c55e;
  --agdelte-warning: #f59e0b;
  --agdelte-error: #ef4444;
  --agdelte-border-radius: 4px;
}
```
