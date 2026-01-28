{-# OPTIONS --without-K #-}

-- RouterDemo: демонстрация SPA роутинга
-- Простое приложение с несколькими "страницами"

module RouterDemo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Agda.Builtin.String using (primStringEquality)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd
import Agdelte.App as App
open import Agdelte.Html.Types
open import Agdelte.Html.Elements
open import Agdelte.Html.Attributes
open import Agdelte.Html.Events
open import Agdelte.Html.Navigation using (navLink)

------------------------------------------------------------------------
-- Routes
------------------------------------------------------------------------

data Route : Set where
  Home    : Route
  About   : Route
  Contact : Route
  NotFound : Route

parseRoute : String → Route
parseRoute "/" = Home
parseRoute "/about" = About
parseRoute "/contact" = Contact
parseRoute _ = NotFound

routeToPath : Route → String
routeToPath Home = "/"
routeToPath About = "/about"
routeToPath Contact = "/contact"
routeToPath NotFound = "/"

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    currentRoute : Route
    visitCount   : ℕ

open Model public

initialModel : Model
initialModel = mkModel Home zero

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  Navigate    : Route → Msg
  UrlChanged  : String → Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

update : Msg → Model → Model
update (Navigate r) m = record m
  { currentRoute = r
  ; visitCount = suc (visitCount m)
  }
update (UrlChanged path) m = record m
  { currentRoute = parseRoute path
  ; visitCount = suc (visitCount m)
  }

------------------------------------------------------------------------
-- Command
------------------------------------------------------------------------

command : Msg → Model → Cmd Msg
command (Navigate r) _ = pushUrl (routeToPath r)
command _ _ = ε

------------------------------------------------------------------------
-- View
------------------------------------------------------------------------

routeEq : Route → Route → Bool
routeEq Home Home = true
routeEq About About = true
routeEq Contact Contact = true
routeEq NotFound NotFound = true
routeEq _ _ = false

routeName : Route → String
routeName Home = "Home"
routeName About = "About"
routeName Contact = "Contact"
routeName NotFound = "404"

navItem : Route → Route → Html Msg
navItem current target =
  let activeClass = if routeEq current target then "nav-link active" else "nav-link"
  in navLink (routeToPath target) (Navigate target) (class activeClass ∷ [])
       (text (routeName target) ∷ [])

navigation : Route → Html Msg
navigation r = nav (class "main-nav" ∷ [])
  ( navItem r Home
  ∷ navItem r About
  ∷ navItem r Contact
  ∷ [])

pageContent : Route → Html Msg
pageContent Home = div (class "page home" ∷ [])
  ( h2 [] (text "Welcome Home" ∷ [])
  ∷ p [] (text "This is the home page of our SPA demo." ∷ [])
  ∷ p [] (text "Click the navigation links to change pages." ∷ [])
  ∷ [])
pageContent About = div (class "page about" ∷ [])
  ( h2 [] (text "About Us" ∷ [])
  ∷ p [] (text "Agdelte is a reactive UI framework with dependent types." ∷ [])
  ∷ p [] (text "Built with Elm Architecture + Polynomial Functors theory." ∷ [])
  ∷ [])
pageContent Contact = div (class "page contact" ∷ [])
  ( h2 [] (text "Contact" ∷ [])
  ∷ p [] (text "GitHub: github.com/example/agdelte" ∷ [])
  ∷ p [] (text "Email: hello@agdelte.dev" ∷ [])
  ∷ [])
pageContent NotFound = div (class "page not-found" ∷ [])
  ( h2 [] (text "404 - Page Not Found" ∷ [])
  ∷ p [] (text "The page you're looking for doesn't exist." ∷ [])
  ∷ button (onClick (Navigate Home) ∷ []) (text "Go Home" ∷ [])
  ∷ [])

view : Model → Html Msg
view m = div (class "router-demo" ∷ [])
  ( h1 [] (text "Router Demo" ∷ [])
  ∷ p (class "stats" ∷ [])
      (text ("Page visits: " ++ show (visitCount m)) ∷ [])
  ∷ navigation (currentRoute m)
  ∷ div (class "content" ∷ [])
      (pageContent (currentRoute m) ∷ [])
  ∷ [])

------------------------------------------------------------------------
-- Subscriptions
------------------------------------------------------------------------

subs : Model → Event Msg
subs _ = onUrlChange UrlChanged

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : App.App Model Msg
app = App.mkCmdApp initialModel update view subs command
