{-# OPTIONS --without-K #-}

-- File upload component with drag-and-drop support.
-- CSS classes: .agdelte-upload, .agdelte-upload__dropzone,
--              .agdelte-upload__dropzone--active, .agdelte-upload__file-list

module Agdelte.Html.Controls.FileUpload where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Upload messages
------------------------------------------------------------------------

data UploadMsg : Set where
  FilesSelected  : String → UploadMsg   -- JSON file list from input
  UploadStarted  : UploadMsg
  UploadProgress : ℕ → UploadMsg        -- percentage 0–100
  UploadDone     : String → UploadMsg   -- server response (URL)
  UploadError    : String → UploadMsg   -- error message
  CancelUpload   : UploadMsg

------------------------------------------------------------------------
-- Upload state
------------------------------------------------------------------------

data UploadStatus : Set where
  Idle Uploading Done Error : UploadStatus

record UploadState : Set where
  constructor mkUploadState
  field
    usStatus    : UploadStatus
    usProgress  : ℕ               -- 0–100
    usFileName  : String
    usError     : String
    usResultUrl : String

open UploadState public

emptyUploadState : UploadState
emptyUploadState = mkUploadState Idle 0 "" "" ""

------------------------------------------------------------------------
-- Upload UI
------------------------------------------------------------------------

-- | File upload dropzone with file input and progress display.
fileUpload : ∀ {M A}
           → (M → UploadState)
           → (UploadMsg → A)
           → String                -- accepted file types ("video/mp4,image/*")
           → Node M A
fileUpload getState wrapMsg acceptTypes =
  div (class "agdelte-upload" ∷ [])
    ( div (class "agdelte-upload__dropzone" ∷ [])
        ( elem "input" ( attr "type" "file"
                       ∷ attr "accept" acceptTypes
                       ∷ class "agdelte-upload__input"
                       ∷ onInput (λ v → wrapMsg (FilesSelected v))
                       ∷ [] ) []
        ∷ span [] ( text "Перетащите файл сюда или нажмите для выбора" ∷ [] )
        ∷ [] )
    ∷ div (class "agdelte-upload__status" ∷ [])
        ( bindF (λ m → usFileName (getState m)) ∷ [] )
    ∷ div (class "agdelte-upload__progress" ∷
           styleBind "width" (stringBinding (λ m →
             primShowNat (usProgress (getState m)) ++ "%")) ∷ [])
        []
    ∷ bindF (λ m → usError (getState m))
    ∷ [])
  where
    open import Agda.Builtin.String using (primShowNat)
