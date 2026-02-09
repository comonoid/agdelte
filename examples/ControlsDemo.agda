{-# OPTIONS --without-K #-}

-- Demo of Agdelte HTML Controls Library
-- Shows all HTML controls with grouped tabs
-- Uses typed CSS from Agdelte.Css

module ControlsDemo where

open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _*_; _+_; _<ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (const; _∘_)

open import Agdelte.Reactive.Node
open import Agdelte.Core.Event using (Event; never)
open import Agdelte.Core.Cmd using (Cmd; ε; delay; _<>_)
open import Agdelte.Html.Controls

open import Agda.Builtin.String using (primShowNat)

-- Typed CSS
open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Length using (px; rem; pct)
open import Agdelte.Css.Color using (hex; named; rgba)
open import Agdelte.Css.Properties using (padding'; margin'; backgroundColor';
                                          color'; fontSize'; borderRadius';
                                          gap'; maxWidth')
open import Agdelte.Css.Layout using (row; col; center; wrap)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet; renderStylesheet)

------------------------------------------------------------------------
-- Parse natural number from string
------------------------------------------------------------------------

open import Data.Char using (Char; toℕ)
open import Agda.Builtin.String using (primStringToList)

-- Parse a digit character to ℕ (0-9), returns 0 for non-digits
digitToℕ : Char → ℕ
digitToℕ c = let n = toℕ c in
  if (48 ≤ᵇ n) ∧ (n ≤ᵇ 57) then n ∸ 48 else 0
  where
    open import Data.Nat using (_≤ᵇ_; _∸_)
    open import Data.Bool using (_∧_)

-- Parse string to ℕ (simple, no error handling)
{-# TERMINATING #-}
parseℕ : String → ℕ
parseℕ s = go (primStringToList s) 0
  where
    go : List Char → ℕ → ℕ
    go [] acc = acc
    go (c ∷ cs) acc = go cs (acc * 10 + digitToℕ c)

-- Default timeout
defaultTimeout : ℕ
defaultTimeout = 3000

------------------------------------------------------------------------
-- Typed CSS Styles
------------------------------------------------------------------------

-- Demo container style
demoContainerStyle : Style
demoContainerStyle =
    maxWidth' (px 800)
  ∷ margin' (px 0)
  ∷ padding' (rem 1.0)
  ∷ []

-- Tab content panel
tabContentStyle : Style
tabContentStyle =
    padding' (rem 1.0)
  ∷ "min-height" ∶ "200px"
  ∷ []

-- Demo button base
demoBtnStyle : Style
demoBtnStyle =
    padding' (px 10)
  ∷ margin' (px 4)
  ∷ borderRadius' (px 4)
  ∷ fontSize' (rem 1.0)
  ∷ "cursor" ∶ "pointer"
  ∷ "border" ∶ "none"
  ∷ []

-- Button variants
infoBtnStyle : Style
infoBtnStyle = demoBtnStyle ++ (backgroundColor' (hex "#3b82f6") ∷ color' (named "white") ∷ [])

successBtnStyle : Style
successBtnStyle = demoBtnStyle ++ (backgroundColor' (hex "#10b981") ∷ color' (named "white") ∷ [])

warningBtnStyle : Style
warningBtnStyle = demoBtnStyle ++ (backgroundColor' (hex "#f59e0b") ∷ color' (hex "#1f2937") ∷ [])

errorBtnStyle : Style
errorBtnStyle = demoBtnStyle ++ (backgroundColor' (hex "#ef4444") ∷ color' (named "white") ∷ [])

-- Toast buttons container
toastButtonsStyle : Style
toastButtonsStyle = row ++ wrap ++ (gap' (px 8) ∷ [])

-- Selected display box
selectedDisplayStyle : Style
selectedDisplayStyle =
    "margin-top" ∶ "16px"
  ∷ padding' (px 12)
  ∷ backgroundColor' (hex "#e8f4e8")
  ∷ borderRadius' (px 4)
  ∷ "border" ∶ "1px solid #ccc"
  ∷ color' (hex "#1f2937")
  ∷ "font-weight" ∶ "500"
  ∷ []

-- Timeout input container
timeoutInputStyle : Style
timeoutInputStyle =
    "margin-bottom" ∶ "16px"
  ∷ padding' (px 12)
  ∷ backgroundColor' (hex "#f0f4f8")
  ∷ borderRadius' (px 4)
  ∷ color' (hex "#1f2937")
  ∷ []

------------------------------------------------------------------------
-- CSS Stylesheet (can be generated at build time)
------------------------------------------------------------------------

appCSS : Stylesheet
appCSS =
    rule ".controls-demo" demoContainerStyle
  ∷ rule ".tab-content" tabContentStyle
  ∷ rule ".demo-btn" demoBtnStyle
  ∷ rule ".demo-btn.info" infoBtnStyle
  ∷ rule ".demo-btn.success" successBtnStyle
  ∷ rule ".demo-btn.warning" warningBtnStyle
  ∷ rule ".demo-btn.error" errorBtnStyle
  ∷ rule ".toast-buttons" toastButtonsStyle
  ∷ rule ".selected-display" selectedDisplayStyle
  ∷ rule ".timeout-input" timeoutInputStyle
  ∷ []

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

-- Checkbox states for demo
record CheckboxStates : Set where
  constructor mkCheckboxStates
  field
    check1 : Bool
    check2 : Bool
    check3 : Bool

open CheckboxStates public

-- Tree expanded states (for simplicity, list of expanded indices)
-- We'll track which accordion sections are open
record LayoutState : Set where
  constructor mkLayoutState
  field
    accordion1 : Bool
    accordion2 : Bool
    accordion3 : Bool
    tree1      : Bool
    tree2      : Bool

open LayoutState public

record Model : Set where
  constructor mkModel
  field
    -- Navigation
    activeTab       : ℕ
    -- Modal & Toast
    modalOpen       : Bool
    toasts          : List ToastData
    nextToastId     : ℕ
    toastTimeoutStr : String
    -- Dropdown
    dropdownOpen    : Bool
    selectedOption  : Maybe ℕ
    -- Forms: Checkbox
    checkStates     : CheckboxStates
    -- Forms: Radio
    selectedRadio   : ℕ
    -- Forms: Slider
    sliderValue     : String
    -- Navigation: Pagination
    currentPage     : ℕ
    totalPages      : ℕ
    -- Layout
    layoutState     : LayoutState
    -- Feedback: Progress
    progressValue   : ℕ
    isLoading       : Bool
    -- Wizard: Stepper
    currentStep     : ℕ
    -- Tooltip: Popover
    popoverOpen     : Bool

open Model public

initCheckboxStates : CheckboxStates
initCheckboxStates = mkCheckboxStates false true false

initLayoutState : LayoutState
initLayoutState = mkLayoutState true false false true false

initModel : Model
initModel = mkModel
  0                    -- activeTab
  false                -- modalOpen
  []                   -- toasts
  0                    -- nextToastId
  "3000"               -- toastTimeoutStr
  false                -- dropdownOpen
  nothing              -- selectedOption
  initCheckboxStates   -- checkStates
  0                    -- selectedRadio
  "50"                 -- sliderValue
  1                    -- currentPage
  10                   -- totalPages
  initLayoutState      -- layoutState
  25                   -- progressValue
  false                -- isLoading
  0                    -- currentStep
  false                -- popoverOpen

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  -- Navigation
  SelectTab      : ℕ → Msg
  -- Modal
  OpenModal      : Msg
  CloseModal     : Msg
  ConfirmModal   : Msg
  -- Toast
  AddToast       : ToastType → String → Msg
  DismissToast   : ℕ → Msg
  SetTimeout     : String → Msg
  -- Dropdown
  ToggleDropdown : Msg
  PickOption     : ℕ → Msg
  -- Forms: Checkbox
  ToggleCheck1   : Msg
  ToggleCheck2   : Msg
  ToggleCheck3   : Msg
  -- Forms: Radio
  SelectRadio    : ℕ → Msg
  -- Forms: Slider
  SetSlider      : String → Msg
  -- Navigation: Pagination
  PrevPage       : Msg
  NextPage       : Msg
  GoToPage       : ℕ → Msg
  -- Layout: Accordion
  ToggleAcc1     : Msg
  ToggleAcc2     : Msg
  ToggleAcc3     : Msg
  -- Layout: Tree
  ToggleTree1    : Msg
  ToggleTree2    : Msg
  -- Feedback: Progress
  SetProgress    : ℕ → Msg
  ToggleLoading  : Msg
  -- Wizard: Stepper
  NextStep       : Msg
  PrevStep       : Msg
  GoToStep       : ℕ → Msg
  -- Tooltip: Popover
  TogglePopover  : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

{-# TERMINATING #-}
filterBool : ∀ {A : Set} → (A → Bool) → List A → List A
filterBool _ [] = []
filterBool p (x ∷ xs) = if p x then x ∷ filterBool p xs else filterBool p xs

removeToast : ℕ → List ToastData → List ToastData
removeToast tid = filterBool (λ t → not (toastId t ≡ᵇ tid))

-- Snoc for lists
_∷ʳ_ : ∀ {A : Set} → List A → A → List A
[] ∷ʳ x = x ∷ []
(y ∷ ys) ∷ʳ x = y ∷ (ys ∷ʳ x)

-- Clamp helper
clamp : ℕ → ℕ → ℕ → ℕ
clamp lo hi n = if n <ᵇ lo then lo else if hi <ᵇ n then hi else n

updateModel : Msg → Model → Model
-- Navigation
updateModel (SelectTab n) m = record m { activeTab = n }
-- Modal
updateModel OpenModal m = record m { modalOpen = true }
updateModel CloseModal m = record m { modalOpen = false }
updateModel ConfirmModal m = record m { modalOpen = false }
-- Toast
updateModel (AddToast ttype msg) m =
  let id = nextToastId m
      newToast = mkToast id msg ttype
  in record m { toasts = toasts m ∷ʳ newToast ; nextToastId = suc id }
updateModel (DismissToast id) m = record m { toasts = removeToast id (toasts m) }
updateModel (SetTimeout s) m = record m { toastTimeoutStr = s }
-- Dropdown
updateModel ToggleDropdown m = record m { dropdownOpen = not (dropdownOpen m) }
updateModel (PickOption n) m = record m { selectedOption = just n ; dropdownOpen = false }
-- Forms: Checkbox
updateModel ToggleCheck1 m =
  record m { checkStates = mkCheckboxStates (not (check1 (checkStates m)))
                                            (check2 (checkStates m))
                                            (check3 (checkStates m)) }
updateModel ToggleCheck2 m =
  record m { checkStates = mkCheckboxStates (check1 (checkStates m))
                                            (not (check2 (checkStates m)))
                                            (check3 (checkStates m)) }
updateModel ToggleCheck3 m =
  record m { checkStates = mkCheckboxStates (check1 (checkStates m))
                                            (check2 (checkStates m))
                                            (not (check3 (checkStates m))) }
-- Forms: Radio
updateModel (SelectRadio n) m = record m { selectedRadio = n }
-- Forms: Slider
updateModel (SetSlider s) m = record m { sliderValue = s }
-- Navigation: Pagination
updateModel PrevPage m = record m { currentPage = if currentPage m ≡ᵇ 1 then 1 else currentPage m ∸ 1 }
  where open import Data.Nat using (_∸_)
updateModel NextPage m = record m { currentPage = if currentPage m <ᵇ totalPages m then suc (currentPage m) else totalPages m }
updateModel (GoToPage n) m = record m { currentPage = clamp 1 (totalPages m) n }
-- Layout: Accordion
updateModel ToggleAcc1 m = record m { layoutState = mkLayoutState (not (accordion1 (layoutState m)))
                                                                   (accordion2 (layoutState m))
                                                                   (accordion3 (layoutState m))
                                                                   (tree1 (layoutState m))
                                                                   (tree2 (layoutState m)) }
updateModel ToggleAcc2 m = record m { layoutState = mkLayoutState (accordion1 (layoutState m))
                                                                   (not (accordion2 (layoutState m)))
                                                                   (accordion3 (layoutState m))
                                                                   (tree1 (layoutState m))
                                                                   (tree2 (layoutState m)) }
updateModel ToggleAcc3 m = record m { layoutState = mkLayoutState (accordion1 (layoutState m))
                                                                   (accordion2 (layoutState m))
                                                                   (not (accordion3 (layoutState m)))
                                                                   (tree1 (layoutState m))
                                                                   (tree2 (layoutState m)) }
-- Layout: Tree
updateModel ToggleTree1 m = record m { layoutState = mkLayoutState (accordion1 (layoutState m))
                                                                   (accordion2 (layoutState m))
                                                                   (accordion3 (layoutState m))
                                                                   (not (tree1 (layoutState m)))
                                                                   (tree2 (layoutState m)) }
updateModel ToggleTree2 m = record m { layoutState = mkLayoutState (accordion1 (layoutState m))
                                                                   (accordion2 (layoutState m))
                                                                   (accordion3 (layoutState m))
                                                                   (tree1 (layoutState m))
                                                                   (not (tree2 (layoutState m))) }
-- Feedback: Progress
updateModel (SetProgress n) m = record m { progressValue = clamp 0 100 n }
updateModel ToggleLoading m = record m { isLoading = not (isLoading m) }
-- Wizard: Stepper
updateModel NextStep m = record m { currentStep = if currentStep m <ᵇ 3 then suc (currentStep m) else 3 }
updateModel PrevStep m = record m { currentStep = if currentStep m ≡ᵇ 0 then 0 else currentStep m ∸ 1 }
  where open import Data.Nat using (_∸_)
updateModel (GoToStep n) m = record m { currentStep = clamp 0 3 n }
-- Tooltip: Popover
updateModel TogglePopover m = record m { popoverOpen = not (popoverOpen m) }

------------------------------------------------------------------------
-- View
------------------------------------------------------------------------

-- Helper
case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

------------------------------------------------------------------------
-- Tab 1: Overview
------------------------------------------------------------------------

tabOverview : Node Model Msg
tabOverview =
  div ( class "tab-content" ∷ [] )
    ( h3 [] ( text "Agdelte Controls Library" ∷ [] )
    ∷ p [] ( text "Complete UI component library with:" ∷ [] )
    ∷ elem "ul" []
        ( elem "li" [] ( text "Forms: Checkbox, RadioGroup, Slider, Dropdown" ∷ [] )
        ∷ elem "li" [] ( text "Navigation: TabBar, Pagination, Breadcrumb, Sidebar" ∷ [] )
        ∷ elem "li" [] ( text "Layout: Accordion, TreeView" ∷ [] )
        ∷ elem "li" [] ( text "Feedback: Modal, Toast, Tooltip, Progress" ∷ [] )
        ∷ elem "li" [] ( text "Data: DataGrid" ∷ [] )
        ∷ elem "li" [] ( text "Wizard: Stepper" ∷ [] )
        ∷ [] )
    ∷ p [] ( text "All styles via typed CSS (Agdelte.Css)." ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Tab 2: Forms (Checkbox, RadioGroup, Slider)
------------------------------------------------------------------------

tabForms : Node Model Msg
tabForms =
  div ( class "tab-content" ∷ [] )
    ( h3 [] ( text "Forms" ∷ [] )
    -- Checkbox section
    ∷ elem "h4" [] ( text "Checkbox" ∷ [] )
    ∷ div ( class "demo-section" ∷ [] )
        ( checkbox "Option 1" (check1 ∘ checkStates) ToggleCheck1
        ∷ checkbox "Option 2 (default on)" (check2 ∘ checkStates) ToggleCheck2
        ∷ checkbox "Option 3" (check3 ∘ checkStates) ToggleCheck3
        ∷ [] )
    -- Radio section
    ∷ elem "h4" [] ( text "RadioGroup" ∷ [] )
    ∷ radioGroupIdx "size" (just ∘ selectedRadio) SelectRadio
        ( "Small" ∷ "Medium" ∷ "Large" ∷ [] )
    ∷ div ( class "selected-display" ∷ [] )
        ( text "Size: "
        ∷ bindF (λ m → case selectedRadio m of λ where
            0 → "Small"
            1 → "Medium"
            _ → "Large")
        ∷ [] )
    -- Slider section
    ∷ elem "h4" [] ( text "Slider" ∷ [] )
    ∷ slider "Volume" "0" "100" sliderValue SetSlider
    ∷ div ( class "selected-display" ∷ [] )
        ( text "Value: " ∷ bindF sliderValue ∷ text "%" ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Tab 3: Dropdown
------------------------------------------------------------------------

tabDropdown : Node Model Msg
tabDropdown =
  div ( class "tab-content" ∷ [] )
    ( h3 [] ( text "Dropdown" ∷ [] )
    ∷ p [] ( text "Select an option:" ∷ [] )
    ∷ dropdownIdx selectedOption dropdownOpen ToggleDropdown PickOption
        ( "Apple" ∷ "Banana" ∷ "Cherry" ∷ "Date" ∷ [] )
    ∷ div ( class "selected-display" ∷ [] )
        ( text "Selected: "
        ∷ bindF (λ m → case selectedOption m of λ where
            nothing → "None"
            (just 0) → "Apple"
            (just 1) → "Banana"
            (just 2) → "Cherry"
            (just _) → "Date")
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Tab 4: Navigation (Pagination, Breadcrumb)
------------------------------------------------------------------------

tabNavigation : Node Model Msg
tabNavigation =
  div ( class "tab-content" ∷ [] )
    ( h3 [] ( text "Navigation" ∷ [] )
    -- Pagination
    ∷ elem "h4" [] ( text "Pagination" ∷ [] )
    ∷ simplePagination currentPage totalPages PrevPage NextPage
    ∷ div ( class "selected-display" ∷ [] )
        ( text "Page "
        ∷ bindF (λ m → primShowNat (currentPage m))
        ∷ text " of "
        ∷ bindF (λ m → primShowNat (totalPages m))
        ∷ [] )
    -- Breadcrumb
    ∷ elem "h4" [] ( text "Breadcrumb" ∷ [] )
    ∷ simpleBreadcrumb (const (SelectTab 3)) ( "Home" ∷ "Products" ∷ "Electronics" ∷ "Phones" ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Tab 5: Layout (Accordion, TreeView)
------------------------------------------------------------------------

tabLayout : Node Model Msg
tabLayout =
  div ( class "tab-content" ∷ [] )
    ( h3 [] ( text "Layout" ∷ [] )
    -- Accordion
    ∷ elem "h4" [] ( text "Accordion" ∷ [] )
    ∷ div ( class "demo-section" ∷ [] )
        ( collapsible "Section 1" (accordion1 ∘ layoutState) ToggleAcc1
            (p [] ( text "Content of section 1. This is the first panel." ∷ [] ))
        ∷ collapsible "Section 2" (accordion2 ∘ layoutState) ToggleAcc2
            (p [] ( text "Content of section 2. More details here." ∷ [] ))
        ∷ collapsible "Section 3" (accordion3 ∘ layoutState) ToggleAcc3
            (p [] ( text "Content of section 3. Final panel content." ∷ [] ))
        ∷ [] )
    -- TreeView
    ∷ elem "h4" [] ( text "TreeView" ∷ [] )
    ∷ div ( class "demo-section" ∷ [] )
        ( collapsible "📁 Documents" (tree1 ∘ layoutState) ToggleTree1
            (div []
              ( div ( style "padding-left" "20px" ∷ [] )
                  ( text "📄 report.pdf" ∷ [] )
              ∷ div ( style "padding-left" "20px" ∷ [] )
                  ( text "📄 notes.txt" ∷ [] )
              ∷ [] ))
        ∷ collapsible "📁 Images" (tree2 ∘ layoutState) ToggleTree2
            (div []
              ( div ( style "padding-left" "20px" ∷ [] )
                  ( text "🖼️ photo.jpg" ∷ [] )
              ∷ [] ))
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Tab 6: Data (DataGrid)
------------------------------------------------------------------------

tabData : Node Model Msg
tabData =
  div ( class "tab-content" ∷ [] )
    ( h3 [] ( text "DataGrid" ∷ [] )
    ∷ p [] ( text "Tabular data display with typed columns:" ∷ [] )
    -- Simple HTML table demo (DataGrid wraps this pattern)
    ∷ elem "table" ( class "agdelte-table" ∷ [] )
        ( elem "thead" []
            ( elem "tr" []
                ( elem "th" [] ( text "Name" ∷ [] )
                ∷ elem "th" [] ( text "Age" ∷ [] )
                ∷ elem "th" [] ( text "Role" ∷ [] )
                ∷ [] )
            ∷ [] )
        ∷ elem "tbody" []
            ( elem "tr" []
                ( elem "td" [] ( text "Alice" ∷ [] )
                ∷ elem "td" [] ( text "28" ∷ [] )
                ∷ elem "td" [] ( text "Engineer" ∷ [] )
                ∷ [] )
            ∷ elem "tr" []
                ( elem "td" [] ( text "Bob" ∷ [] )
                ∷ elem "td" [] ( text "35" ∷ [] )
                ∷ elem "td" [] ( text "Designer" ∷ [] )
                ∷ [] )
            ∷ elem "tr" []
                ( elem "td" [] ( text "Carol" ∷ [] )
                ∷ elem "td" [] ( text "42" ∷ [] )
                ∷ elem "td" [] ( text "Manager" ∷ [] )
                ∷ [] )
            ∷ [] )
        ∷ [] )
    ∷ div ( class "display-box" ∷ [] )
        ( text "DataGrid API: mkGridConfig columns rowKey onClick" ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Tab 7: Feedback (Modal, Toast, Tooltip, Progress)
------------------------------------------------------------------------

tabFeedback : Node Model Msg
tabFeedback =
  div ( class "tab-content" ∷ [] )
    ( h3 [] ( text "Feedback" ∷ [] )
    -- Modal
    ∷ elem "h4" [] ( text "Modal" ∷ [] )
    ∷ button ( class "demo-btn info" ∷ onClick OpenModal ∷ [] )
        ( text "Open Modal" ∷ [] )
    -- Toast
    ∷ elem "h4" [] ( text "Toast" ∷ [] )
    ∷ div ( class "timeout-input" ∷ [] )
        ( label [] ( text "Timeout: " ∷ [] )
        ∷ input ( type' "number"
                ∷ valueBind toastTimeoutStr
                ∷ onInput SetTimeout
                ∷ style "width" "80px"
                ∷ [] )
        ∷ text " ms"
        ∷ [] )
    ∷ div ( class "toast-buttons" ∷ [] )
        ( button ( class "demo-btn info" ∷ onClick (AddToast Info "Info message") ∷ [] )
            ( text "Info" ∷ [] )
        ∷ button ( class "demo-btn success" ∷ onClick (AddToast Success "Success!") ∷ [] )
            ( text "Success" ∷ [] )
        ∷ button ( class "demo-btn warning" ∷ onClick (AddToast Warning "Warning!") ∷ [] )
            ( text "Warning" ∷ [] )
        ∷ button ( class "demo-btn error" ∷ onClick (AddToast Error "Error!") ∷ [] )
            ( text "Error" ∷ [] )
        ∷ [] )
    -- Tooltip
    ∷ elem "h4" [] ( text "Tooltip" ∷ [] )
    ∷ div ( class "demo-section" ∷ [] )
        ( tooltip (text "Hover me") "This is a tooltip!" Top
        ∷ text "  "
        ∷ popover popoverOpen TogglePopover
            (text "Click for popover")
            (div [] ( text "Popover content here." ∷ [] ))
        ∷ [] )
    -- Progress
    ∷ elem "h4" [] ( text "Progress" ∷ [] )
    ∷ progressBarLabeled "Loading" (λ m → primShowNat (progressValue m))
    ∷ div ( class "demo-section" ∷ [] )
        ( button ( class "demo-btn" ∷ onClick ToggleLoading ∷ [] )
            ( text "Toggle Loading" ∷ [] )
        ∷ when isLoading spinner
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Tab 8: Wizard (Stepper)
------------------------------------------------------------------------

tabWizard : Node Model Msg
tabWizard =
  div ( class "tab-content" ∷ [] )
    ( h3 [] ( text "Wizard / Stepper" ∷ [] )
    ∷ clickableStepper currentStep GoToStep
        ( mkStep "Account" "Create account"
        ∷ mkStep "Profile" "Add details"
        ∷ mkStep "Payment" "Add payment"
        ∷ mkStep "Confirm" "Review order"
        ∷ [] )
    ∷ div ( class "selected-display" ∷ [] )
        ( text "Step: "
        ∷ bindF (λ m → primShowNat (suc (currentStep m)))
        ∷ text " of 4"
        ∷ [] )
    ∷ div ( class "toast-buttons" ∷ [] )
        ( button ( class "demo-btn" ∷ onClick PrevStep ∷ [] )
            ( text "← Previous" ∷ [] )
        ∷ button ( class "demo-btn info" ∷ onClick NextStep ∷ [] )
            ( text "Next →" ∷ [] )
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Main view
------------------------------------------------------------------------

view : Node Model Msg
view =
  div ( class "controls-demo" ∷ [] )
    ( h1 [] ( text "Agdelte Controls" ∷ [] )
    ∷ tabBar activeTab SelectTab
        ( mkTab "Overview" tabOverview
        ∷ mkTab "Forms" tabForms
        ∷ mkTab "Dropdown" tabDropdown
        ∷ mkTab "Navigation" tabNavigation
        ∷ mkTab "Layout" tabLayout
        ∷ mkTab "Data" tabData
        ∷ mkTab "Feedback" tabFeedback
        ∷ mkTab "Wizard" tabWizard
        ∷ [] )
    ∷ confirmDialog modalOpen
        "Confirm Action"
        "Are you sure you want to proceed?"
        "Confirm"
        "Cancel"
        ConfirmModal
        CloseModal
    ∷ toastContainer toasts DismissToast
    ∷ [] )

------------------------------------------------------------------------
-- Commands (toast auto-dismiss)
------------------------------------------------------------------------

cmdHandler : Msg → Model → Cmd Msg
cmdHandler (AddToast _ _) m =
  -- Schedule auto-dismiss for the toast we just added
  -- Use user-configured timeout from model
  let timeout = parseℕ (toastTimeoutStr m)
      actualTimeout = if timeout ≡ᵇ 0 then defaultTimeout else timeout
  in delay actualTimeout (DismissToast (nextToastId m))
cmdHandler _ _ = ε

------------------------------------------------------------------------
-- Application
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initModel updateModel view cmdHandler (const never)
