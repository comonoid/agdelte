{-# OPTIONS --without-K #-}

-- Search bar with debounced input.
-- CSS classes: .agdelte-search, .agdelte-search__input, .agdelte-search__clear

module Agdelte.Html.Controls.SearchBar where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Search bar
------------------------------------------------------------------------

-- | Search bar with text input and clear button.
-- getQuery: extract current query from model.
-- onInput: message when user types.
-- onClear: message to clear the query.
searchBar : ∀ {M A}
          → (M → String)        -- current query
          → (String → A)        -- on input change
          → A                   -- on clear
          → Node M A
searchBar getQuery inputMsg clearMsg =
  div (class "agdelte-search" ∷ [])
    ( input ( class "agdelte-search__input"
            ∷ attr "type" "text"
            ∷ attr "placeholder" "Поиск..."
            ∷ valueBind getQuery
            ∷ onInput inputMsg
            ∷ [] )
    ∷ button ( class "agdelte-search__clear"
             ∷ onClick clearMsg
             ∷ [] )
        ( text "✕" ∷ [] )
    ∷ [])
