{-# OPTIONS --without-K #-}

-- TaskDemo: демонстрация монадических цепочек HTTP-запросов
-- Показывает do-нотацию для композиции Task

module TaskDemo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_; length)
open import Data.List using (List; []; _∷_)
open import Function using (const)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd
open import Agdelte.Core.Task
open import Agdelte.Html.Types
open import Agdelte.Html.Elements
open import Agdelte.Html.Attributes
open import Agdelte.Html.Events
import Agdelte.App as App

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

update : Msg → Model → Model
update FetchChain m = mkModel loading "Starting chain..."
update (GotResult (ok d)) m = mkModel (success d) "Done!"
update (GotResult (err e)) m = mkModel (error e) "Error!"

------------------------------------------------------------------------
-- Command
------------------------------------------------------------------------

command : Msg → Model → Cmd Msg
command FetchChain _ = attempt fetchChain GotResult
command _ _ = ε

------------------------------------------------------------------------
-- View
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

view : Model → Html Msg
view m =
  div (class "task-demo" ∷ [])
    ( h1 [] (text "Task Chain Demo" ∷ [])
    ∷ p [] (text "Demonstrates monadic HTTP request chains" ∷ [])
    ∷ button
        (onClick FetchChain ∷ class "fetch-btn" ∷ [])
        (text (getBtnText (Model.status m)) ∷ [])
    ∷ div (class "status" ∷ [])
        (pre [] (text (getStatusText (Model.status m)) ∷ []) ∷ [])
    ∷ div (class "step-info" ∷ [])
        (text ("Step: " ++ Model.stepInfo m) ∷ [])
    ∷ [] )

------------------------------------------------------------------------
-- Subs
------------------------------------------------------------------------

subs : Model → Event Msg
subs = const never

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : App.App Model Msg
app = App.mkCmdApp initialModel update view subs command

