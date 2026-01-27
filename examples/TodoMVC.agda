{-# OPTIONS --without-K --guardedness #-}

-- TodoMVC: классический пример

module TodoMVC where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.String using (String; _==_) renaming (_++_ to _++ˢ_)
open import Data.List using (List; []; _∷_; [_]; map; length; null; _++_)
open import Data.List.Base using (filterᵇ; all)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (const; _∘_)

open import Agdelte.Core.Signal hiding (merge; delay)
open import Agdelte.Core.Event
open import Agdelte.Html.Types
open import Agdelte.Html.Elements
open import Agdelte.Html.Attributes hiding (id)
open import Agdelte.Html.Events
import Agdelte.App as App

------------------------------------------------------------------------
-- Todo Item
------------------------------------------------------------------------

record Todo : Set where
  constructor mkTodo
  field
    todoId      : ℕ
    todoText    : String
    completed   : Bool

open Todo public

------------------------------------------------------------------------
-- Filter
------------------------------------------------------------------------

data Filter : Set where
  All Active Completed : Filter

showFilter : Filter → String
showFilter All = "All"
showFilter Active = "Active"
showFilter Completed = "Completed"

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    todos         : List Todo
    newTodo       : String
    nextId        : ℕ
    currentFilter : Filter

open Model public

init : Model
init = mkModel [] "" 0 All

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  UpdateNewTodo : String → Msg
  AddTodo       : Msg
  ToggleTodo    : ℕ → Msg
  DeleteTodo    : ℕ → Msg
  ToggleAll     : Msg
  ClearCompleted : Msg
  SetFilter     : Filter → Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateTodo : ℕ → (Todo → Todo) → List Todo → List Todo
updateTodo _ _ [] = []
updateTodo targetId f (t ∷ ts) =
  (if todoId t ≡ᵇ targetId then f t else t) ∷ updateTodo targetId f ts
  where
    open import Data.Nat using (_≡ᵇ_)
    open import Data.Bool using (if_then_else_)

update : Msg → Model → Model
update (UpdateNewTodo s) m = record m { newTodo = s }
update AddTodo m =
  if newTodo m == ""
  then m
  else record m
    { todos = todos m ++ (mkTodo (nextId m) (newTodo m) false ∷ [])
    ; newTodo = ""
    ; nextId = suc (nextId m)
    }
  where open import Data.Bool using (if_then_else_)
update (ToggleTodo tid) m =
  record m { todos = updateTodo tid (λ t → record t { completed = not (completed t) }) (todos m) }
update (DeleteTodo tid) m =
  record m { todos = filterᵇ (λ t → not (todoId t ≡ᵇ tid)) (todos m) }
  where open import Data.Nat using (_≡ᵇ_)
update ToggleAll m =
  let allDone = all completed (todos m)
  in record m { todos = map (λ t → record t { completed = not allDone }) (todos m) }
update ClearCompleted m =
  record m { todos = filterᵇ (not ∘ completed) (todos m) }
update (SetFilter f) m = record m { currentFilter = f }

------------------------------------------------------------------------
-- View
------------------------------------------------------------------------

viewTodo : Todo → Html Msg
viewTodo t =
  li ( class (if completed t then "completed" else "")
     ∷ keyAttr (show (todoId t))
     ∷ [] )
    ( div (class "view" ∷ [])
        ( input ( type' "checkbox"
                ∷ class "toggle"
                ∷ (if completed t then checked else class "")
                ∷ onClick (ToggleTodo (todoId t))
                ∷ [] )
        ∷ label [] (text (todoText t) ∷ [])
        ∷ button (class "destroy" ∷ onClick (DeleteTodo (todoId t)) ∷ []) []
        ∷ [] )
    ∷ [] )
  where open import Data.Bool using (if_then_else_)

filterTodos : Filter → List Todo → List Todo
filterTodos All ts = ts
filterTodos Active ts = filterᵇ (not ∘ completed) ts
filterTodos Completed ts = filterᵇ completed ts

-- Сравнение фильтров
eqFilter : Filter → Filter → Bool
eqFilter All All = true
eqFilter Active Active = true
eqFilter Completed Completed = true
eqFilter _ _ = false

viewFilters : Filter → Html Msg
viewFilters current =
  ul (class "filters" ∷ [])
    ( viewFilterLink All
    ∷ viewFilterLink Active
    ∷ viewFilterLink Completed
    ∷ [] )
  where
    open import Data.Bool using (if_then_else_)

    viewFilterLink : Filter → Html Msg
    viewFilterLink f =
      li []
        ( a ( class (if eqFilter f current then "selected" else "")
            ∷ onClick (SetFilter f)
            ∷ [] )
            (text (showFilter f) ∷ [])
        ∷ [] )

view : Model → Html Msg
view m =
  section (class "todoapp" ∷ [])
    ( header (class "header" ∷ [])
        ( h1 [] (text "todos" ∷ [])
        ∷ input ( class "new-todo"
                ∷ placeholder "What needs to be done?"
                ∷ value (newTodo m)
                ∷ onInput' UpdateNewTodo
                ∷ onEnter AddTodo
                ∷ [] )
        ∷ [] )
    ∷ section (class "main" ∷ [])
        ( input ( class "toggle-all"
                ∷ type' "checkbox"
                ∷ onClick ToggleAll
                ∷ [] )
        ∷ ul (class "todo-list" ∷ [])
            (map viewTodo (filterTodos (currentFilter m) (todos m)))
        ∷ [] )
    ∷ footer (class "footer" ∷ [])
        ( span (class "todo-count" ∷ [])
            (text (show remaining ++ˢ " items left") ∷ [])
        ∷ viewFilters (currentFilter m)
        ∷ button ( class "clear-completed"
                 ∷ onClick ClearCompleted
                 ∷ [] )
            (text "Clear completed" ∷ [])
        ∷ [] )
    ∷ [] )
  where
    remaining = length (filterᵇ (not ∘ completed) (todos m))

------------------------------------------------------------------------
-- Events (нет внешних событий)
------------------------------------------------------------------------

events : Model → Event Msg
events = const never

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

todoApp : App.App Model Msg
todoApp = App.mkApp init update view events
