{-# OPTIONS --without-K #-}

-- VideoDemo: demonstrates embedding the video player in a larger app
-- via the standard zoom pattern (getter + wrapper).

module VideoDemo where

open import Data.String using (String)
open import Data.List using ([]; _∷_)
open import Data.Bool using (if_then_else_)
open import Function using (const)

open import Agdelte.Reactive.Node
open import Agdelte.Core.Cmd as Cmd using (Cmd; ε; _<>_; mapCmd)
open import Agdelte.Core.Event as Event using (Event; never; mapE)
open import Agdelte.Html.Controls.Video.Player

------------------------------------------------------------------------
-- App Model: wraps VideoModel + app-specific state
------------------------------------------------------------------------

record AppModel : Set where
  constructor mkAppModel
  field
    videoState : VideoModel
    title      : String

open AppModel

------------------------------------------------------------------------
-- App Msg: wraps VideoMsg + app-specific messages
------------------------------------------------------------------------

data AppMsg : Set where
  VideoAction : VideoMsg → AppMsg
  SetTitle    : String → AppMsg

------------------------------------------------------------------------
-- Config: defined once, used by update, cmd, and template
------------------------------------------------------------------------

appVideoConfig : PlayerConfig AppModel AppMsg
appVideoConfig = defaultPlayerConfig
  "https://example.com/video/manifest.m3u8"
  videoState
  VideoAction

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateApp : AppMsg → AppModel → AppModel
updateApp (VideoAction vm) m =
  record m { videoState = mkUpdateVideo appVideoConfig vm (videoState m) }
updateApp (SetTitle t) m = record m { title = t }

------------------------------------------------------------------------
-- Cmd
------------------------------------------------------------------------

cmdApp : AppMsg → AppModel → Cmd AppMsg
cmdApp (VideoAction vm) m =
  mapCmd VideoAction (mkVideoCmd appVideoConfig vm (videoState m))
    <> mkGestureCmd appVideoConfig vm (videoState m)
cmdApp _ _ = ε

------------------------------------------------------------------------
-- Subscriptions
------------------------------------------------------------------------

subsApp : AppModel → Event AppMsg
subsApp m = mapE VideoAction (videoSubs (videoState m))

------------------------------------------------------------------------
-- Template
------------------------------------------------------------------------

appTemplate : Node AppModel AppMsg
appTemplate =
  div ( class "app" ∷ [] )
    ( h1 [] ( bindF title ∷ [] )
    ∷ videoPlayer appVideoConfig
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp AppModel AppMsg
app = mkReactiveApp
  (mkAppModel (initVideoModel appVideoConfig) "Video Demo")
  updateApp
  appTemplate
  cmdApp
  subsApp
