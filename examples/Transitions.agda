{-# OPTIONS --without-K #-}

-- Transitions: whenT with CSS enter/leave transitions (Phase 3)
-- Demonstrates conditional rendering with animations

module Transitions where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_])

open import Agdelte.Core.Event
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    panelOpen    : Bool
    notifVisible : Bool
    notifCount   : ℕ

open Model public

initialModel : Model
initialModel = mkModel false false 0

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  TogglePanel : Msg
  ShowNotif   : Msg
  HideNotif   : Msg
  AutoDismiss : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel TogglePanel m = record m { panelOpen = not (panelOpen m) }
updateModel ShowNotif   m = record m { notifVisible = true ; notifCount = suc (notifCount m) }
updateModel HideNotif   m = record m { notifVisible = false }
updateModel AutoDismiss m = record m { notifVisible = false }

------------------------------------------------------------------------
-- Subscriptions: auto-dismiss notification after 3s
------------------------------------------------------------------------

subs : Model → Event Msg
subs m = if notifVisible m
  then timeout 3000 AutoDismiss
  else never

------------------------------------------------------------------------
-- Template with whenT transitions
------------------------------------------------------------------------

toggleText : Model → String
toggleText m = if panelOpen m then "Hide Panel" else "Show Panel"

notifCountText : Model → String
notifCountText m = "Notifications shown: " ++ show (notifCount m)

panelTrans : Transition
panelTrans = mkTransition "panel-enter" "panel-leave" 300

notifTrans : Transition
notifTrans = mkTransition "notif-enter" "notif-leave" 400

transitionsTemplate : Node Model Msg
transitionsTemplate =
  div [ class "transitions-demo" ]
    ( h1 [] [ text "Transitions" ]
    ∷ p [ class "description" ]
        [ text "whenT: conditional rendering with CSS enter/leave animations" ]

    -- Panel section: toggle visibility with slide transition
    ∷ div [ class "section" ]
        ( button (onClick TogglePanel ∷ class "btn" ∷ [])
            [ bindF toggleText ]
        ∷ whenT panelOpen panelTrans
            (div [ class "panel" ]
              ( h3 [] [ text "Expandable Panel" ]
              ∷ p [] [ text "This panel appears with a CSS transition." ]
              ∷ p [] [ text "enterClass is added on show, leaveClass on hide." ]
              ∷ p [] [ text "The runtime waits for duration before removing the DOM node." ]
              ∷ [] ))
        ∷ [] )

    -- Notification section: toast with auto-dismiss
    ∷ div [ class "section" ]
        ( button (onClick ShowNotif ∷ class "btn notif-btn" ∷ [])
            [ text "Show Notification" ]
        ∷ whenT notifVisible notifTrans
            (div [ class "notification" ]
              ( span [ class "notif-text" ] [ text "Action completed successfully!" ]
              ∷ button (onClick HideNotif ∷ class "dismiss-btn" ∷ []) [ text "×" ]
              ∷ [] ))
        ∷ p [ class "counter-text" ] [ bindF notifCountText ]
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel transitionsTemplate

-- subs exported separately (auto-dismiss)
