{-# OPTIONS --without-K #-}

-- WebSocket: demonstration of WebSocket
-- Echo client with sending and receiving messages
-- Reactive approach: no Virtual DOM, direct bindings

module WebSocket where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_]; length) renaming (_++_ to _++L_)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

data ConnectionStatus : Set where
  Disconnected : ConnectionStatus
  Connecting   : ConnectionStatus
  Connected    : ConnectionStatus
  Error        : String → ConnectionStatus

-- Chat message: sent or received
data ChatMsg : Set where
  Sent     : String → ChatMsg
  Received : String → ChatMsg

record Model : Set where
  constructor mkModel
  field
    wantConnected : Bool              -- intention: do we want to be connected
    connStatus    : ConnectionStatus  -- current connection status
    messages      : List ChatMsg
    inputText     : String
    msgCount      : ℕ

open Model public

initialModel : Model
initialModel = mkModel false Disconnected [] "" zero

wsUrl : String
wsUrl = "ws://localhost:8080/echo"

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  Connect      : Msg
  Disconnect   : Msg
  WsEvent      : WsMsg → Msg
  UpdateInput  : String → Msg
  SendMessage  : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel Connect m = record m { wantConnected = true ; connStatus = Connecting }
updateModel Disconnect m = record m { wantConnected = false ; connStatus = Disconnected ; messages = [] }
updateModel (WsEvent WsConnected) m = record m { connStatus = Connected }
updateModel (WsEvent (WsMessage s)) m = record m
  { messages = messages m ++L [ Received s ]
  ; msgCount = suc (msgCount m)
  }
updateModel (WsEvent WsClosed) m = record m { connStatus = Disconnected ; wantConnected = false }
updateModel (WsEvent (WsError e)) m = record m { connStatus = Error e ; wantConnected = false }
updateModel (UpdateInput s) m = record m { inputText = s }
updateModel SendMessage m = record m
  { messages = messages m ++L [ Sent (inputText m) ]
  ; inputText = ""
  }

------------------------------------------------------------------------
-- Command
------------------------------------------------------------------------

cmd' : Msg → Model → Cmd Msg
cmd' SendMessage m with connStatus m
... | Connected = wsSend wsUrl (inputText m)
... | _ = ε
cmd' _ _ = ε

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

statusClass : ConnectionStatus → String
statusClass Disconnected = "disconnected"
statusClass Connecting = "connecting"
statusClass Connected = "connected"
statusClass (Error _) = "error"

statusText : ConnectionStatus → String
statusText Disconnected = "Disconnected"
statusText Connecting = "Connecting..."
statusText Connected = "Connected"
statusText (Error e) = "Error: " ++ e

isConnected : ConnectionStatus → Bool
isConnected Connected = true
isConnected _ = false

modelIsConnected : Model → Bool
modelIsConnected m = isConnected (connStatus m)

modelStatusClass : Model → String
modelStatusClass m = "status " ++ statusClass (connStatus m)

modelStatusText : Model → String
modelStatusText m = statusText (connStatus m)

msgCountText : Model → String
msgCountText m = "Messages (" ++ show (msgCount m) ++ ")"

------------------------------------------------------------------------
-- Template: reactive bindings (no Virtual DOM)
------------------------------------------------------------------------

-- View single message (used in foreach)
viewMessage : ChatMsg → ℕ → Node Model Msg
viewMessage (Sent s) _ =
  li [ class "message sent" ]
    ( span [ class "label" ] [ text "You" ]
    ∷ span [ class "text" ] [ text s ]
    ∷ [] )
viewMessage (Received s) _ =
  li [ class "message received" ]
    ( span [ class "label" ] [ text "Echo" ]
    ∷ span [ class "text" ] [ text s ]
    ∷ [] )

wsTemplate : Node Model Msg
wsTemplate =
  div [ class "ws-demo" ]
    ( h1 [] [ text "WebSocket Demo" ]
    ∷ p [] [ text ("Echo server: " ++ wsUrl) ]

    -- Status
    ∷ div [ classBind modelStatusClass ]
        [ bindF modelStatusText ]  -- auto-updates!

    -- Connect/Disconnect buttons (conditional)
    ∷ when modelIsConnected (
        button (onClick Disconnect ∷ class "disconnect-btn" ∷ [])
          [ text "Disconnect" ]
      )
    ∷ when (not ∘ modelIsConnected) (
        button (onClick Connect ∷ class "connect-btn" ∷ [])
          [ text "Connect" ]
      )

    -- Message input (only when connected)
    ∷ when modelIsConnected (
        div [ class "input-section" ]
          ( input (type' "text"
                 ∷ valueBind inputText
                 ∷ onInput UpdateInput
                 ∷ placeholder "Type a message..."
                 ∷ [])
          ∷ button (onClick SendMessage ∷ class "send-btn" ∷ [])
              [ text "Send" ]
          ∷ [] )
      )

    -- Messages list
    ∷ div [ class "messages-section" ]
        ( h3 [] [ bindF msgCountText ]  -- auto-updates!
        ∷ ul [ class "messages" ]
            [ foreach messages viewMessage ]  -- reactive list!
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Subscriptions
------------------------------------------------------------------------

subs' : Model → Event Msg
subs' m = if wantConnected m then wsConnect wsUrl WsEvent else never

------------------------------------------------------------------------
-- App (full TEA with cmd and subs integrated)
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel wsTemplate cmd' subs'
