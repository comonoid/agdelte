{-# OPTIONS --without-K #-}

-- Todo: классический TodoMVC пример

module Todo where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.String using (String; _++_; _≟_)
open import Data.List using (List; []; _∷_; map; length; null)
open import Data.List.Base using (filterᵇ)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Core.Event hiding (onKeyDown; onKeyUp)
open import Agdelte.Html.Types
open import Agdelte.Html.Elements
open import Agdelte.Html.Attributes
open import Agdelte.Html.Events
import Agdelte.App as App

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

-- Переключить completed для задачи с данным id
toggleItem : ℕ → TodoItem → TodoItem
toggleItem targetId item =
  if todoId item ≡ᵇ targetId
  then record item { completed = not (completed item) }
  else item
  where
    open import Data.Nat using (_≡ᵇ_)

-- Удалить задачу с данным id
removeItem : ℕ → List TodoItem → List TodoItem
removeItem targetId = filterᵇ (λ item → not (todoId item ≡ᵇ targetId))
  where
    open import Data.Nat using (_≡ᵇ_)

-- Оставить только незавершённые
keepActive : List TodoItem → List TodoItem
keepActive = filterᵇ (λ item → not (completed item))

-- Проверка пустой строки
isEmpty : String → Bool
isEmpty s with s ≟ ""
... | yes _ = true
... | no _  = false

{-# COMPILE JS isEmpty = s => s === "" #-}

update : Msg → Model → Model
update NoOp m = m
update (UpdateInput s) m = record m { inputText = s }
update AddTodo m =
  if isEmpty (inputText m)
  then m
  else record m
    { todos  = todos m ∷ʳ mkTodo (nextId m) (inputText m) false
    ; nextId = suc (nextId m)
    }  -- inputText сохраняется для быстрого добавления дубликатов
  where
    open import Data.List using (_∷ʳ_)
update (ToggleTodo id) m = record m { todos = map (toggleItem id) (todos m) }
update (RemoveTodo id) m = record m { todos = removeItem id (todos m) }
update ClearCompleted m = record m { todos = keepActive (todos m) }

------------------------------------------------------------------------
-- View helpers
------------------------------------------------------------------------

-- Количество незавершённых задач
activeCount : List TodoItem → ℕ
activeCount items = length (filterᵇ (λ item → not (completed item)) items)

-- Есть ли завершённые задачи?
hasCompleted : List TodoItem → Bool
hasCompleted items = not (null (filterᵇ completed items))

------------------------------------------------------------------------
-- View: отдельная задача
------------------------------------------------------------------------

viewTodo : TodoItem → Html Msg
viewTodo item =
  li (keyAttr (show (todoId item)) ∷ class "todo-item" ∷ itemStyle ∷ [])
    ( input (type' "checkbox" ∷ checkboxAttrs ∷ onClick (ToggleTodo (todoId item)) ∷ [])
    ∷ span (textStyle ∷ []) (text (todoText item) ∷ [])
    ∷ button (onClick (RemoveTodo (todoId item)) ∷ class "delete-btn" ∷ deleteStyle ∷ [])
        (text "×" ∷ [])
    ∷ [] )
  where
    itemStyle = styles "display" "flex; align-items: center; padding: 8px"
    checkboxAttrs = if completed item then checked else class ""
    textStyle = if completed item
                then styles "text-decoration" "line-through; color: #999; flex: 1"
                else styles "flex" "1"
    deleteStyle = styles "background" "none; border: none; color: #cc9a9a; font-size: 20px; cursor: pointer"

------------------------------------------------------------------------
-- View: главная
------------------------------------------------------------------------

-- View helpers для footer
clearBtn : Model → Html Msg
clearBtn m' =
  if hasCompleted (todos m')
  then button (onClick ClearCompleted ∷ clearStyle ∷ [])
         (text "Clear completed" ∷ [])
  else empty
  where
    clearStyle = styles "padding" "6px 12px; background: #b83f45; color: white; border: none; border-radius: 4px; cursor: pointer"

viewFooter : Model → Html Msg
viewFooter m' =
  if null (todos m')
  then empty
  else div (class "footer" ∷ footerStyle ∷ [])
         ( span [] (text (show (activeCount (todos m')) ++ " items left") ∷ [])
         ∷ clearBtn m'
         ∷ [] )
  where
    open import Data.List using (null)
    footerStyle = styles "display" "flex; justify-content: space-between; padding: 12px; color: #777"

view : Model → Html Msg
view m =
  div (class "todo-app" ∷ appStyle ∷ [])
    ( h1 (headerStyle ∷ []) (text "todos" ∷ [])
    ∷ div (class "input-section" ∷ inputSectionStyle ∷ [])
        ( input (type' "text"
               ∷ placeholder "What needs to be done?"
               ∷ value (inputText m)
               ∷ onInput' UpdateInput
               ∷ onKeyDown handleKey
               ∷ inputStyle
               ∷ [])
        ∷ button (onClick AddTodo ∷ addBtnStyle ∷ [])
            (text "Add" ∷ [])
        ∷ [] )
    ∷ ul (class "todo-list" ∷ listStyle ∷ [])
        (map viewTodo (todos m))
    ∷ viewFooter m
    ∷ [] )
  where
    appStyle = styles "max-width" "500px; margin: 40px auto; font-family: sans-serif"
    headerStyle = styles "text-align" "center; color: #b83f45; font-size: 80px; font-weight: 200"
    inputSectionStyle = styles "display" "flex; gap: 8px; margin-bottom: 16px"
    inputStyle = styles "flex" "1; padding: 12px; font-size: 16px; border: none; outline: none"
    addBtnStyle = styles "padding" "12px 24px; background: #b83f45; color: white; border: none; cursor: pointer"
    listStyle = styles "list-style" "none; padding: 0; margin: 0"

    handleKey : String → Msg
    handleKey "Enter" = AddTodo
    handleKey _       = NoOp  -- Ignore other keys, onInput handles text

------------------------------------------------------------------------
-- Events (без внешних событий)
------------------------------------------------------------------------

events : Model → Event Msg
events _ = never

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

todoApp : App.App Model Msg
todoApp = App.mkApp initialModel update view events

-- Export for demo-loader.js
app : App.App Model Msg
app = todoApp
