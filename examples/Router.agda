{-# OPTIONS --without-K #-}

-- Router: demonstration of SPA routing
-- Simple application with multiple "pages"
-- Reactive approach: no Virtual DOM, direct bindings

module Router where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_])
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Agda.Builtin.String using (primStringEquality)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd
open import Agdelte.Reactive.Node

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

updateModel : Msg → Model → Model
updateModel (Navigate r) m = record m
  { currentRoute = r
  ; visitCount = suc (visitCount m)
  }
updateModel (UrlChanged path) m = record m
  { currentRoute = parseRoute path
  ; visitCount = suc (visitCount m)
  }

------------------------------------------------------------------------
-- Command
------------------------------------------------------------------------

cmd' : Msg → Model → Cmd Msg
cmd' (Navigate r) _ = pushUrl (routeToPath r)
cmd' _ _ = ε

------------------------------------------------------------------------
-- Helpers
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

visitCountText : Model → String
visitCountText m = "Page visits: " ++ show (visitCount m)

------------------------------------------------------------------------
-- Template: reactive bindings (no Virtual DOM)
------------------------------------------------------------------------

-- Navigation item
navItem : Route → Route → Node Model Msg
navItem current target =
  let activeClass = if routeEq current target then "nav-link active" else "nav-link"
  in a (href (routeToPath target)
       ∷ onClick (Navigate target)
       ∷ class activeClass
       ∷ [])
       [ text (routeName target) ]

-- Page content based on route
pageContent : Route → Node Model Msg
pageContent Home =
  div [ class "page home" ]
    ( h2 [] [ text "Welcome Home" ]
    ∷ p [] [ text "This is the home page of our SPA demo." ]
    ∷ p [] [ text "Click the navigation links to change pages." ]
    ∷ [] )
pageContent About =
  div [ class "page about" ]
    ( h2 [] [ text "About Us" ]
    ∷ p [] [ text "Agdelte is a reactive UI framework with dependent types." ]
    ∷ p [] [ text "Built with Svelte-style direct DOM updates + Polynomial Functors theory." ]
    ∷ [] )
pageContent Contact =
  div [ class "page contact" ]
    ( h2 [] [ text "Contact" ]
    ∷ p [] [ text "GitHub: github.com/example/agdelte" ]
    ∷ p [] [ text "Email: hello@agdelte.dev" ]
    ∷ [] )
pageContent NotFound =
  div [ class "page not-found" ]
    ( h2 [] [ text "404 - Page Not Found" ]
    ∷ p [] [ text "The page you're looking for doesn't exist." ]
    ∷ button [ onClick (Navigate Home) ] [ text "Go Home" ]
    ∷ [] )

-- Navigation component (static, doesn't need bindings for active state since we rebuild on route change)
-- Note: In a real app, you might want dynamic class bindings for active state
navigation : Route → Node Model Msg
navigation r =
  nav [ class "main-nav" ]
    ( navItem r Home
    ∷ navItem r About
    ∷ navItem r Contact
    ∷ [] )

-- Main template
-- Note: Route-dependent content is rebuilt when route changes via foreach/when
-- For simplicity, we use a helper approach
routerTemplate : Node Model Msg
routerTemplate =
  div [ class "router-demo" ]
    ( h1 [] [ text "Router Demo" ]
    ∷ p [ class "stats" ] [ bindF visitCountText ]  -- auto-updates!

    -- Navigation (needs route-dependent active class)
    -- Since we can't easily bind route-dependent children, we use a simpler approach
    ∷ nav [ class "main-nav" ]
        ( a (href "/" ∷ onClick (Navigate Home) ∷ class "nav-link" ∷ [])
            [ text "Home" ]
        ∷ a (href "/about" ∷ onClick (Navigate About) ∷ class "nav-link" ∷ [])
            [ text "About" ]
        ∷ a (href "/contact" ∷ onClick (Navigate Contact) ∷ class "nav-link" ∷ [])
            [ text "Contact" ]
        ∷ [] )

    -- Content area - conditionally show based on route
    ∷ div [ class "content" ]
        ( when (λ m → routeEq (currentRoute m) Home) (pageContent Home)
        ∷ when (λ m → routeEq (currentRoute m) About) (pageContent About)
        ∷ when (λ m → routeEq (currentRoute m) Contact) (pageContent Contact)
        ∷ when (λ m → routeEq (currentRoute m) NotFound) (pageContent NotFound)
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Subscriptions
------------------------------------------------------------------------

subs' : Model → Event Msg
subs' _ = onUrlChange UrlChanged

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel routerTemplate cmd' subs'
