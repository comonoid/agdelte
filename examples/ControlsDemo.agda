{-# OPTIONS --without-K #-}

-- Demo of Agdelte HTML Controls Library
-- Shows TabBar, Modal, Dropdown, and Toast components
-- Uses typed CSS from Agdelte.Css

module ControlsDemo where

open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _*_; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (const; _∘_)

open import Agdelte.Reactive.Node
open import Agdelte.Core.Event using (Event; never)
open import Agdelte.Core.Cmd using (Cmd; ε; delay; _<>_)
open import Agdelte.Html.Controls

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

record Model : Set where
  constructor mkModel
  field
    activeTab       : ℕ
    modalOpen       : Bool
    dropdownOpen    : Bool
    selectedOption  : Maybe ℕ
    toasts          : List ToastData
    nextToastId     : ℕ
    toastTimeoutStr : String   -- user input for timeout

open Model public

initModel : Model
initModel = mkModel 0 false false nothing [] 0 "3000"

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  SelectTab      : ℕ → Msg
  OpenModal      : Msg
  CloseModal     : Msg
  ConfirmModal   : Msg
  ToggleDropdown : Msg
  PickOption     : ℕ → Msg
  AddToast       : ToastType → String → Msg
  DismissToast   : ℕ → Msg
  SetTimeout     : String → Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

{-# TERMINATING #-}
filterBool : ∀ {A : Set} → (A → Bool) → List A → List A
filterBool _ [] = []
filterBool p (x ∷ xs) = if p x then x ∷ filterBool p xs else filterBool p xs

removeToast : ℕ → List ToastData → List ToastData
removeToast tid = filterBool (λ t → not (toastId t ≡ᵇ tid))

updateModel : Msg → Model → Model
updateModel (SelectTab n) m = record m { activeTab = n }
updateModel OpenModal m = record m { modalOpen = true }
updateModel CloseModal m = record m { modalOpen = false }
updateModel ConfirmModal m = record m { modalOpen = false }
updateModel ToggleDropdown m = record m { dropdownOpen = not (dropdownOpen m) }
updateModel (PickOption n) m = record m { selectedOption = just n ; dropdownOpen = false }
updateModel (AddToast ttype msg) m =
  let id = nextToastId m
      newToast = mkToast id msg ttype
  in record m { toasts = toasts m ∷ʳ newToast ; nextToastId = suc id }
  where
    _∷ʳ_ : ∀ {A : Set} → List A → A → List A
    [] ∷ʳ x = x ∷ []
    (y ∷ ys) ∷ʳ x = y ∷ (ys ∷ʳ x)
updateModel (DismissToast id) m = record m { toasts = removeToast id (toasts m) }
updateModel (SetTimeout s) m = record m { toastTimeoutStr = s }

------------------------------------------------------------------------
-- View
------------------------------------------------------------------------

-- Tab content pages
tab1Content : Node Model Msg
tab1Content =
  div ( class "tab-content" ∷ [] )
    ( h3 [] ( text "Welcome to Controls Demo" ∷ [] )
    ∷ p [] ( text "This demonstrates the Agdelte HTML Controls library." ∷ [] )
    ∷ p [] ( text "Use the tabs above to navigate between sections." ∷ [] )
    ∷ p [] ( text "Styles are defined using typed CSS (Agdelte.Css)!" ∷ [] )
    ∷ [] )

tab2Content : Node Model Msg
tab2Content =
  div ( class "tab-content" ∷ [] )
    ( h3 [] ( text "Modal Demo" ∷ [] )
    ∷ p [] ( text "Click the button to open a modal dialog." ∷ [] )
    ∷ button ( class "demo-btn info" ∷ onClick OpenModal ∷ [] )
        ( text "Open Modal" ∷ [] )
    ∷ [] )

tab3Content : Node Model Msg
tab3Content =
  div ( class "tab-content" ∷ [] )
    ( h3 [] ( text "Dropdown Demo" ∷ [] )
    ∷ p [] ( text "Select an option from the dropdown below." ∷ [] )
    ∷ dropdownIdx selectedOption dropdownOpen ToggleDropdown PickOption
        ( "Option A" ∷ "Option B" ∷ "Option C" ∷ "Option D" ∷ [] )
    ∷ div ( class "selected-display" ∷ [] )
        ( text "Selected: "
        ∷ bindF (λ m → case selectedOption m of λ where
            nothing → "None"
            (just 0) → "Option A"
            (just 1) → "Option B"
            (just 2) → "Option C"
            (just _) → "Option D")
        ∷ [] )
    ∷ [] )
  where
    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x

tab4Content : Node Model Msg
tab4Content =
  div ( class "tab-content" ∷ [] )
    ( h3 [] ( text "Toast Demo" ∷ [] )
    ∷ p [] ( text "Toast notifications with configurable auto-dismiss timeout." ∷ [] )
    ∷ div ( class "timeout-input" ∷ [] )
        ( label [] ( text "Timeout (ms): " ∷ [] )
        ∷ input ( type' "number"
                ∷ valueBind toastTimeoutStr
                ∷ onInput SetTimeout
                ∷ style "width" "100px"
                ∷ style "margin-right" "16px"
                ∷ [] )
        ∷ span [] ( text "Current: " ∷ bindF toastTimeoutStr ∷ text " ms" ∷ [] )
        ∷ [] )
    ∷ div ( class "toast-buttons" ∷ [] )
        ( button ( class "demo-btn info" ∷ onClick (AddToast Info "This is an info message") ∷ [] )
            ( text "Info Toast" ∷ [] )
        ∷ button ( class "demo-btn success" ∷ onClick (AddToast Success "Operation successful!") ∷ [] )
            ( text "Success Toast" ∷ [] )
        ∷ button ( class "demo-btn warning" ∷ onClick (AddToast Warning "Warning: Check your input") ∷ [] )
            ( text "Warning Toast" ∷ [] )
        ∷ button ( class "demo-btn error" ∷ onClick (AddToast Error "Error: Something went wrong") ∷ [] )
            ( text "Error Toast" ∷ [] )
        ∷ [] )
    ∷ [] )

-- Main template
view : Node Model Msg
view =
  div ( class "controls-demo" ∷ [] )
    ( h1 [] ( text "Agdelte Controls Demo" ∷ [] )
    ∷ tabBar activeTab SelectTab
        ( mkTab "Overview" tab1Content
        ∷ mkTab "Modal" tab2Content
        ∷ mkTab "Dropdown" tab3Content
        ∷ mkTab "Toast" tab4Content
        ∷ [] )
    ∷ confirmDialog modalOpen
        "Confirm Action"
        "Are you sure you want to proceed with this action?"
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
