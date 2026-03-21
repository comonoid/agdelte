{-# OPTIONS --without-K --guardedness #-}

-- Threaded comments for lessons.
-- CSS classes: .agdelte-comments, .agdelte-comment, .agdelte-comment--reply,
--              .agdelte-comment__author, .agdelte-comment__text,
--              .agdelte-comment__date, .agdelte-comment__actions

module Agdelte.Html.Controls.Comments where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.List.Base using (filterᵇ)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; is-just)

open import Agda.Builtin.String using (primShowNat)
open import Agdelte.Reactive.Node
open import Agdelte.Storage.AppStore using
  ( CommentRecord; cmId; cmUserId; cmLessonId; cmText; cmDate; cmParentId
  ; CommentId; UserId; LessonId )

------------------------------------------------------------------------
-- Comment messages
------------------------------------------------------------------------

data CommentMsg : Set where
  SubmitComment : String → CommentMsg            -- text
  ReplyTo       : CommentId → String → CommentMsg  -- parentId, text
  DeleteComment : CommentId → CommentMsg

------------------------------------------------------------------------
-- Single comment view
------------------------------------------------------------------------

-- | Render a single comment (with known ID).
commentView : ∀ {M A}
            → CommentId              -- this comment's ID
            → (M → String)           -- author name
            → (M → String)           -- comment text
            → Bool                   -- is reply?
            → A                      -- on reply click
            → A                      -- on delete click
            → Node M A
commentView cid getAuthor getText isReply onReplyMsg onDeleteMsg =
  div (class (if isReply then "agdelte-comment agdelte-comment--reply" else "agdelte-comment") ∷ [])
    ( span (class "agdelte-comment__author" ∷ [])
        ( bindF getAuthor ∷ [] )
    ∷ div (class "agdelte-comment__text" ∷ [])
        ( bindF getText ∷ [] )
    ∷ div (class "agdelte-comment__actions" ∷ [])
        ( button (class "agdelte-comment__reply-btn" ∷ onClick onReplyMsg ∷ [])
            ( text "Ответить" ∷ [] )
        ∷ button (class "agdelte-comment__delete-btn" ∷ onClick onDeleteMsg ∷ [])
            ( text "Удалить" ∷ [] )
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Comment input form
------------------------------------------------------------------------

-- | Text area + submit button for writing a comment.
commentForm : ∀ {M A}
            → (M → String)         -- current draft text
            → (String → A)         -- on text change
            → A                    -- on submit
            → Node M A
commentForm getDraft onDraftChange onSubmit =
  div (class "agdelte-comment-form" ∷ [])
    ( elem "textarea" ( class "agdelte-comment-form__input"
                      ∷ attr "placeholder" "Написать комментарий..."
                      ∷ valueBind getDraft
                      ∷ onInput onDraftChange
                      ∷ [] ) []
    ∷ button ( class "agdelte-comment-form__submit"
             ∷ onClick onSubmit
             ∷ [] )
        ( text "Отправить" ∷ [] )
    ∷ [])
