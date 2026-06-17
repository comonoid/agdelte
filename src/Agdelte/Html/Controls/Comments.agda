{-# OPTIONS --without-K #-}

-- Threaded-comment UI tools: a single comment view (author / text / reply +
-- delete actions) and a compose form. Domain-neutral — parametric in (M A), ids
-- are plain ℕ, the data is supplied via getters, so any app/domain plugs its own
-- model in. Emits BEM classes .agdelte-comment(__author|__text|__actions|…) and
-- .agdelte-comment-form(__input|__submit); styling is the consumer's.

module Agdelte.Html.Controls.Comments where

open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Comment messages (an id vocabulary the host's Msg can embed)
------------------------------------------------------------------------

CommentId : Set
CommentId = ℕ

data CommentMsg : Set where
  SubmitComment : String → CommentMsg              -- text
  ReplyTo       : CommentId → String → CommentMsg  -- parentId, text
  DeleteComment : CommentId → CommentMsg

------------------------------------------------------------------------
-- Single comment view
------------------------------------------------------------------------

-- | Render one comment: author + text + reply/delete buttons. `isReply` toggles
-- the --reply modifier. The reply/delete messages are supplied pre-built (the
-- caller bakes in whichever id it wants).
commentView : ∀ {M A}
            → (M → String)           -- author name
            → (M → String)           -- comment text
            → Bool                   -- is reply?
            → A                      -- on reply click
            → A                      -- on delete click
            → Node M A
commentView getAuthor getText isReply onReplyMsg onDeleteMsg =
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
