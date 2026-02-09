{-# OPTIONS --without-K #-}

-- Todo: classic TodoMVC example
-- Reactive approach: no Virtual DOM, direct bindings

module Todo where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_]; map; length; null)
open import Data.List.Base using (filterᵇ)
open import Data.Product using (_×_; _,_)

open import Agdelte.Reactive.Node
open import Agdelte.Css.Decl using (Style; _∶_; _<>_; toAttrs)
open import Agdelte.Css.Length using (px)
open import Agdelte.Css.Color using (hex; named)
open import Agdelte.Css.Properties using (padding'; padding2; background';
                                          color'; fontSize'; borderRadius';
                                          maxWidth'; gap'; margin')

------------------------------------------------------------------------
-- TodoItem
------------------------------------------------------------------------

record TodoItem : Set where
  constructor mkTodo
  field
    todoId    : ℕ
    todoText  : String
    completed : Bool

open TodoItem public

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    todos     : List TodoItem
    inputText : String
    nextId    : ℕ

open Model public

initialModel : Model
initialModel = mkModel [] "" 0

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  NoOp           : Msg
  UpdateInput    : String → Msg
  AddTodo        : Msg
  ToggleTodo     : ℕ → Msg
  RemoveTodo     : ℕ → Msg
  ClearCompleted : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

-- Toggle completed for task with given id
toggleItem : ℕ → TodoItem → TodoItem
toggleItem targetId item =
  if todoId item ≡ᵇ targetId
  then record item { completed = not (completed item) }
  else item
  where
    open import Data.Nat using (_≡ᵇ_)

-- Remove task with given id
removeItem : ℕ → List TodoItem → List TodoItem
removeItem targetId = filterᵇ (λ item → not (todoId item ≡ᵇ targetId))
  where
    open import Data.Nat using (_≡ᵇ_)

-- Keep only uncompleted tasks
keepActive : List TodoItem → List TodoItem
keepActive = filterᵇ (λ item → not (completed item))

-- Check for empty string (FFI-only, Agda definition not used at runtime)
postulate isEmpty : String → Bool

{-# COMPILE JS isEmpty = s => s === "" #-}

updateModel : Msg → Model → Model
updateModel NoOp m = m
updateModel (UpdateInput s) m = record m { inputText = s }
updateModel AddTodo m =
  if isEmpty (inputText m)
  then m
  else record m
    { todos  = todos m ∷ʳ mkTodo (nextId m) (inputText m) false
    ; nextId = suc (nextId m)
    }  -- inputText is preserved for quick addition of duplicates
  where
    open import Data.List using (_∷ʳ_)
updateModel (ToggleTodo id') m = record m { todos = map (toggleItem id') (todos m) }
updateModel (RemoveTodo id') m = record m { todos = removeItem id' (todos m) }
updateModel ClearCompleted m = record m { todos = keepActive (todos m) }

------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------

-- Number of uncompleted tasks
activeCount : List TodoItem → ℕ
activeCount items = length (filterᵇ (λ item → not (completed item)) items)

-- Are there any completed tasks?
hasCompleted : List TodoItem → Bool
hasCompleted items = not (null (filterᵇ completed items))

-- Format items count
itemsLeftStr : Model → String
itemsLeftStr m = show (activeCount (todos m)) ++ " items left"

-- Has todos?
hasTodos : Model → Bool
hasTodos m = not (null (todos m))

-- Has completed todos?
modelHasCompleted : Model → Bool
modelHasCompleted m = hasCompleted (todos m)

------------------------------------------------------------------------
-- Template: reactive bindings (no Virtual DOM)
------------------------------------------------------------------------

-- Reusable style fragments (typed + raw mixed freely)
accentBtn : Style
accentBtn =
    background' (hex "#b83f45")
  ∷ color' (named "white")
  ∷ "border"  ∶ "none"           -- raw escape hatch for shorthand props
  ∷ "cursor"  ∶ "pointer"
  ∷ []

-- Composed styles
appStyle : Style
appStyle =
    maxWidth' (px 500)
  ∷ "margin"      ∶ "40px auto"  -- raw: complex value with "auto"
  ∷ "font-family" ∶ "sans-serif"
  ∷ []

headerStyle : Style
headerStyle =
    "text-align"  ∶ "center"
  ∷ color' (hex "#b83f45")
  ∷ fontSize' (px 80)
  ∷ "font-weight" ∶ "200"
  ∷ []

inputSectionStyle : Style
inputSectionStyle =
    "display"       ∶ "flex"
  ∷ gap' (px 8)
  ∷ "margin-bottom" ∶ "16px"
  ∷ []

inputStyle' : Style
inputStyle' =
    "flex"   ∶ "1"
  ∷ padding' (px 12)
  ∷ fontSize' (px 16)
  ∷ "border"  ∶ "none"
  ∷ "outline" ∶ "none"
  ∷ []

addBtnStyle : Style
addBtnStyle = padding2 (px 12) (px 24) ∷ [] <> accentBtn

listStyle : Style
listStyle =
    "list-style" ∶ "none"
  ∷ padding' (px 0)
  ∷ margin' (px 0)
  ∷ []

footerStyle : Style
footerStyle =
    "display"         ∶ "flex"
  ∷ "justify-content" ∶ "space-between"
  ∷ padding' (px 12)
  ∷ color' (hex "#777")
  ∷ []

clearStyle : Style
clearStyle =
    padding2 (px 6) (px 12)
  ∷ borderRadius' (px 4)
  ∷ [] <> accentBtn

-- Key handler for input
handleKey : String → Msg
handleKey "Enter" = AddTodo
handleKey _       = NoOp

-- Item styles
itemStyle : Style
itemStyle =
    "display"     ∶ "flex"
  ∷ "align-items" ∶ "center"
  ∷ padding' (px 8)
  ∷ []

baseText : Style
baseText = "flex" ∶ "1" ∷ []

completedText : Style
completedText = baseText
  <> ( "text-decoration" ∶ "line-through"
     ∷ color' (hex "#999")
     ∷ [] )

deleteStyle : Style
deleteStyle =
    "background" ∶ "none"
  ∷ "border"     ∶ "none"
  ∷ color' (hex "#cc9a9a")
  ∷ fontSize' (px 20)
  ∷ "cursor"     ∶ "pointer"
  ∷ []

-- View single todo item (used in foreach)
viewTodoItem : TodoItem → ℕ → Node Model Msg
viewTodoItem item idx =
  li (keyAttr (show (todoId item)) ∷ class "todo-item" ∷ toAttrs itemStyle)
    ( input (type' "checkbox" ∷ checkboxAttrs ∷ onClick (ToggleTodo (todoId item)) ∷ [])
    ∷ span (toAttrs textStyle) [ text (todoText item) ]
    ∷ button (onClick (RemoveTodo (todoId item)) ∷ class "delete-btn" ∷ toAttrs deleteStyle)
        [ text "×" ]
    ∷ [] )
  where
    checkboxAttrs = if completed item then checked else class ""
    textStyle = if completed item then completedText else baseText

-- Main template
todoTemplate : Node Model Msg
todoTemplate =
  div (class "todo-app" ∷ toAttrs appStyle)
    ( h1 (toAttrs headerStyle) [ text "todos" ]
    ∷ div (class "input-section" ∷ toAttrs inputSectionStyle)
        ( input (type' "text"
               ∷ placeholder "What needs to be done?"
               ∷ valueBind inputText
               ∷ onInput UpdateInput
               ∷ onKeyDown handleKey
               ∷ toAttrs inputStyle')
        ∷ button (onClick AddTodo ∷ toAttrs addBtnStyle)
            [ text "Add" ]
        ∷ [] )
    ∷ ul (class "todo-list" ∷ toAttrs listStyle)
        [ foreachKeyed todos (λ item → show (todoId item)) viewTodoItem ]  -- keyed reactive list!
    ∷ when hasTodos (
        div (class "footer" ∷ toAttrs footerStyle)
          ( span [] [ bindF itemsLeftStr ]  -- auto-updates!
          ∷ when modelHasCompleted (
              button (onClick ClearCompleted ∷ toAttrs clearStyle)
                [ text "Clear completed" ]
            )
          ∷ [] )
      )
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = simpleApp initialModel updateModel todoTemplate
