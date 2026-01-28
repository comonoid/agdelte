{-# OPTIONS --without-K #-}

-- WebSocketDemo: демонстрация WebSocket
-- Echo-клиент с отправкой и получением сообщений

module WebSocketDemo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd
import Agdelte.App as App
open import Agdelte.Html.Types
open import Agdelte.Html.Elements
open import Agdelte.Html.Attributes
open import Agdelte.Html.Events

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

data ConnectionStatus : Set where
  Disconnected : ConnectionStatus
  Connecting   : ConnectionStatus
  Connected    : ConnectionStatus
  Error        : String → ConnectionStatus

-- Сообщение в чате: отправленное или полученное
data ChatMsg : Set where
  Sent     : String → ChatMsg
  Received : String → ChatMsg

record Model : Set where
  constructor mkModel
  field
    wantConnected : Bool              -- намерение: хотим ли быть подключены
    connStatus    : ConnectionStatus  -- текущий статус соединения
    messages      : List ChatMsg
    inputText     : String
    msgCount      : ℕ

open Model public

initialModel : Model
initialModel = mkModel false Disconnected [] "" zero

wsUrl : String
wsUrl = "wss://echo.websocket.org"

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

update : Msg → Model → Model
update Connect m = record m { wantConnected = true ; connStatus = Connecting }
update Disconnect m = record m { wantConnected = false ; connStatus = Disconnected ; messages = [] }
update (WsEvent WsConnected) m = record m { connStatus = Connected }
update (WsEvent (WsMessage s)) m = record m
  { messages = Received s ∷ messages m
  ; msgCount = suc (msgCount m)
  }
update (WsEvent WsClosed) m = record m { connStatus = Disconnected ; wantConnected = false }
update (WsEvent (WsError e)) m = record m { connStatus = Error e ; wantConnected = false }
update (UpdateInput s) m = record m { inputText = s }
update SendMessage m = record m
  { messages = Sent (inputText m) ∷ messages m
  ; inputText = ""
  }

------------------------------------------------------------------------
-- Command
------------------------------------------------------------------------

command : Msg → Model → Cmd Msg
command SendMessage m with connStatus m
... | Connected = wsSend wsUrl (inputText m)
... | _ = ε
command _ _ = ε

------------------------------------------------------------------------
-- View
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

viewMessage : ChatMsg → Html Msg
viewMessage (Sent s) = li (class "message sent" ∷ [])
  ( span (class "label" ∷ []) (text "You" ∷ [])
  ∷ span (class "text" ∷ []) (text s ∷ [])
  ∷ [])
viewMessage (Received s) = li (class "message received" ∷ [])
  ( span (class "label" ∷ []) (text "Echo" ∷ [])
  ∷ span (class "text" ∷ []) (text s ∷ [])
  ∷ [])

view : Model → Html Msg
view m = div (class "ws-demo" ∷ [])
  ( h1 [] (text "WebSocket Demo" ∷ [])
  ∷ p [] (text ("Echo server: " ++ wsUrl) ∷ [])

  -- Status
  ∷ div (class ("status " ++ statusClass (connStatus m)) ∷ [])
      (text (statusText (connStatus m)) ∷ [])

  -- Connect/Disconnect button
  ∷ (if isConnected (connStatus m)
      then button (onClick Disconnect ∷ class "disconnect-btn" ∷ [])
             (text "Disconnect" ∷ [])
      else button (onClick Connect ∷ class "connect-btn" ∷ [])
             (text "Connect" ∷ []))

  -- Message input (only when connected)
  ∷ (if isConnected (connStatus m)
      then div (class "input-section" ∷ [])
        ( input (type' "text"
               ∷ value (inputText m)
               ∷ onInput UpdateInput
               ∷ placeholder "Type a message..."
               ∷ [])
        ∷ button (onClick SendMessage ∷ class "send-btn" ∷ [])
            (text "Send" ∷ [])
        ∷ [])
      else div [] [])

  -- Messages list
  ∷ div (class "messages-section" ∷ [])
      ( h3 [] (text ("Messages (" ++ show (msgCount m) ++ ")") ∷ [])
      ∷ ul (class "messages" ∷ [])
          (Data.List.map viewMessage (messages m))
      ∷ [])
  ∷ [])

------------------------------------------------------------------------
-- Subscriptions
------------------------------------------------------------------------

subs : Model → Event Msg
subs m = if wantConnected m then wsConnect wsUrl WsEvent else never

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : App.App Model Msg
app = App.mkCmdApp initialModel update view subs command
