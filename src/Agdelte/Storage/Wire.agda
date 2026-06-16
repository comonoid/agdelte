{-# OPTIONS --without-K #-}

-- Pure wire codec for the WAL: encode (A → String) / decode (String → Maybe A),
-- pure Agda → compiles to BOTH GHC and JS (Agdelte.Json / FFI.Shared are JS-only).
--
-- Format: a record is a concatenation of length-prefixed fields `<len>:<payload>`.
-- length-prefix means a payload may contain any character (no delimiter clashes)
-- and gives the framing the WAL needs (atomicity / torn-tail, §18).
module Agdelte.Storage.Wire where

open import Agda.Builtin.Char using (primCharToNat; primCharEquality)
open import Data.Char using (Char; isDigit)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; splitAt; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList) renaming (length to strLen; _++_ to _<>_)

------------------------------------------------------------------------
-- Pure readℕ (string of digits → ℕ; empty / non-digit → nothing)
------------------------------------------------------------------------

private
  digitVal : Char → Maybe ℕ
  digitVal c = if isDigit c then just (primCharToNat c ∸ primCharToNat '0') else nothing

  readDigits : ℕ → List Char → Maybe ℕ
  readDigits acc []       = just acc
  readDigits acc (c ∷ cs) with digitVal c
  ... | just d  = readDigits (acc * 10 + d) cs
  ... | nothing = nothing

readℕ : String → Maybe ℕ
readℕ s with toList s
... | []         = nothing
... | cs@(_ ∷ _) = readDigits 0 cs

------------------------------------------------------------------------
-- Length-prefixed field framing
------------------------------------------------------------------------

-- wrap an already-encoded field string as `<len>:<s>`
lp : String → String
lp s = showℕ (strLen s) <> ":" <> s

private
  takeDigits : List Char → (List Char × List Char)
  takeDigits []       = ([] , [])
  takeDigits (c ∷ cs) with isDigit c
  ... | true  = let r = takeDigits cs in (c ∷ proj₁ r , proj₂ r)
  ... | false = ([] , c ∷ cs)

-- read one `<len>:<payload>` from the front → (payload, rest).
-- splitAt silently clamps when n > length rest, so we REQUIRE the payload to be
-- exactly n chars (length ≡ᵇ n) — an over-declared length is fail-closed (nothing)
-- here instead of being silently delegated to the value codec (L9).
readField : List Char → Maybe (String × List Char)
readField cs with takeDigits cs
... | ([] , _)                  = nothing               -- no length digits
... | (d ∷ ds , [])             = nothing               -- no separator
... | (d ∷ ds , sep ∷ rest)     with primCharEquality sep ':' | readDigits 0 (d ∷ ds)
...   | true | just n           = let sp = splitAt n rest in
                                    if length (proj₁ sp) ≡ᵇ n
                                    then just (fromList (proj₁ sp) , proj₂ sp)
                                    else nothing          -- declared length not fully present
...   | _    | _                = nothing

------------------------------------------------------------------------
-- Reader monad over the remaining input (for sequential field decode)
------------------------------------------------------------------------

R : Set → Set
R A = List Char → Maybe (A × List Char)

returnR : ∀ {A} → A → R A
returnR a cs = just (a , cs)

infixl 1 _>>=R_
_>>=R_ : ∀ {A B} → R A → (A → R B) → R B
(m >>=R f) cs with m cs
... | nothing        = nothing
... | just (a , rest) = f a rest

-- read one length-prefixed field and decode its payload with `dec`
fieldR : ∀ {A} → (String → Maybe A) → R A
fieldR dec cs with readField cs
... | nothing             = nothing
... | just (payload , rest) with dec payload
...   | nothing = nothing
...   | just a  = just (a , rest)

-- run a record decoder; requires ALL input consumed
runR : ∀ {A} → R A → String → Maybe A
runR m s with m (toList s)
... | just (a , []) = just a
... | _             = nothing

------------------------------------------------------------------------
-- Primitive codecs
------------------------------------------------------------------------

encℕ : ℕ → String
encℕ = showℕ
decℕ : String → Maybe ℕ
decℕ = readℕ

encStr : String → String
encStr s = s
decStr : String → Maybe String
decStr s = just s

-- Maybe codecs: "n" = nothing, "j<payload>" = just …. Concrete (ℕ / String) to
-- avoid universe-level metas from a polymorphic ∀{A} (Maybe is level-polymorphic).
encMaybeℕ : Maybe ℕ → String
encMaybeℕ nothing  = "n"
encMaybeℕ (just n) = "j" <> showℕ n
decMaybeℕ : String → Maybe (Maybe ℕ)
decMaybeℕ s with toList s
... | []         = nothing
... | (c ∷ rest) with primCharEquality c 'j' | primCharEquality c 'n'
...   | true | _    with readℕ (fromList rest)
...     | just n  = just (just n)
...     | nothing = nothing
decMaybeℕ s | (c ∷ rest) | _ | true = just nothing
decMaybeℕ s | (c ∷ rest) | _ | _    = nothing

encMaybeStr : Maybe String → String
encMaybeStr nothing  = "n"
encMaybeStr (just s) = "j" <> s
decMaybeStr : String → Maybe (Maybe String)
decMaybeStr s with toList s
... | []         = nothing
... | (c ∷ rest) with primCharEquality c 'j' | primCharEquality c 'n'
...   | true | _ = just (just (fromList rest))
...   | _ | true = just nothing
...   | _ | _    = nothing
