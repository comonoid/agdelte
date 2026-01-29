{-# OPTIONS --without-K #-}

-- TaskDemo: демонстрация монадических цепочек HTTP-запросов
-- Показывает do-нотацию для композиции Task
-- Reactive approach: no Virtual DOM, direct bindings

module TaskDemo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_; length)
open import Data.List using (List; []; _∷_; [_])
open import Function using (const)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd
open import Agdelte.Core.Task
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

data Status : Set where
  idle    : Status
  loading : Status
  success : String → Status
  error   : String → Status

record Model : Set where
  constructor mkModel
  field
    status    : Status
    stepInfo  : String  -- текущий шаг для отображения

initialModel : Model
initialModel = mkModel idle ""

------------------------------------------------------------------------
-- Msg
------------------------------------------------------------------------

data Msg : Set where
  FetchChain : Msg
  GotResult  : Result String String → Msg

------------------------------------------------------------------------
-- Task: цепочка запросов
------------------------------------------------------------------------

-- Показывает длину строки
showLen : String → String
showLen s = show (length s)

-- Цепочка из трёх запросов с do-нотацией
fetchChain : Task String
fetchChain = do
  post1 ← http "https://jsonplaceholder.typicode.com/posts/1"
  post2 ← http "https://jsonplaceholder.typicode.com/posts/2"
  post3 ← http "https://jsonplaceholder.typicode.com/posts/3"
  pure ("Fetched 3 posts!\n\nPost 1: " ++ showLen post1 ++ " chars" ++
        "\nPost 2: " ++ showLen post2 ++ " chars" ++
        "\nPost 3: " ++ showLen post3 ++ " chars")

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel FetchChain m = mkModel loading "Starting chain..."
updateModel (GotResult (ok d)) m = mkModel (success d) "Done!"
updateModel (GotResult (err e)) m = mkModel (error e) "Error!"

------------------------------------------------------------------------
-- Command
------------------------------------------------------------------------

cmd : Msg → Model → Cmd Msg
cmd FetchChain _ = attempt fetchChain GotResult
cmd _ _ = ε

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

getBtnText : Status → String
getBtnText idle = "Fetch Chain (3 requests)"
getBtnText loading = "Loading..."
getBtnText (success _) = "Fetch Again"
getBtnText (error _) = "Retry"

getStatusText : Status → String
getStatusText idle = "Click to fetch data from 3 endpoints sequentially"
getStatusText loading = "Fetching..."
getStatusText (success d) = d
getStatusText (error e) = "Error: " ++ e

-- Model to string functions
btnTextFromModel : Model → String
btnTextFromModel m = getBtnText (Model.status m)

statusTextFromModel : Model → String
statusTextFromModel m = getStatusText (Model.status m)

stepInfoFromModel : Model → String
stepInfoFromModel m = "Step: " ++ Model.stepInfo m

------------------------------------------------------------------------
-- Template: reactive bindings (no Virtual DOM)
------------------------------------------------------------------------

taskTemplate : Node Model Msg
taskTemplate =
  div [ class "task-demo" ]
    ( h1 [] [ text "Task Chain Demo" ]
    ∷ p [] [ text "Demonstrates monadic HTTP request chains" ]
    ∷ button (onClick FetchChain ∷ class "fetch-btn" ∷ [])
        [ bindF btnTextFromModel ]    -- auto-updates!
    ∷ div [ class "status" ]
        [ pre [] [ bindF statusTextFromModel ] ]  -- auto-updates!
    ∷ div [ class "step-info" ]
        [ bindF stepInfoFromModel ]   -- auto-updates!
    ∷ [] )

------------------------------------------------------------------------
-- Subs (none for this demo)
------------------------------------------------------------------------

subs : Model → Event Msg
subs = const never

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel taskTemplate

-- cmd and subs are exported separately (see above)
