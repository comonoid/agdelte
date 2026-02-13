{-# OPTIONS --without-K #-}

-- Optics hierarchy for widget composition and network navigation
--
-- Concrete types (Lens, Prism, Traversal, Affine) for API contracts:
--   zoomNode : Lens M M' → Prism Msg Msg' → ...
--
-- Unified Optic for composition and Big Optic:
--   _∘O_ : Optic B C → Optic A B → Optic A C
--
-- TotalOptic ≅ Poly.Lens for monomial case: see Theory.OpticPolyOptic

module Agdelte.Reactive.Optic where

open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.List using (List; []; _∷_; map)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id; const)

-- Re-export Lens (already exists, keep as-is)
open import Agdelte.Reactive.Lens public

private
  variable
    A B C S : Set

------------------------------------------------------------------------
-- Prism: navigation into a sum type
------------------------------------------------------------------------

record Prism (S A : Set) : Set where
  constructor mkPrism
  field
    match : S → Maybe A
    build : A → S

open Prism public

_∘P_ : Prism B C → Prism A B → Prism A C
inner ∘P outer = mkPrism
  (λ a → match outer a >>= match inner)
  (build outer ∘ build inner)

idPrism : Prism A A
idPrism = mkPrism just id

------------------------------------------------------------------------
-- Traversal: navigation into a collection
------------------------------------------------------------------------

record Traversal (S A : Set) : Set where
  constructor mkTraversal
  field
    toList  : S → List A
    overAll : (A → A) → S → S

open Traversal public

------------------------------------------------------------------------
-- Affine (Optional): Lens ∘ Prism — access that may fail
------------------------------------------------------------------------

record Affine (S A : Set) : Set where
  constructor mkAffine
  field
    preview : S → Maybe A
    set     : A → S → S

open Affine public

_∘A_ : ∀ {A B C} → Affine B C → Affine A B → Affine A C
_∘A_ {A} inner outer = mkAffine
  (λ a → preview outer a >>= preview inner)
  setC
  where
    setC : _ → A → A
    setC c a with preview outer a
    ... | nothing = a
    ... | just b  = set outer (set inner c b) a

------------------------------------------------------------------------
-- Conversions: Lens/Prism → Affine
------------------------------------------------------------------------

lensToAffine : Lens S A → Affine S A
lensToAffine l = mkAffine (just ∘ get l) (λ a s → Lens.set l a s)

prismToAffine : Prism S A → Affine S A
prismToAffine p = mkAffine (match p) setA
  where
    setA : _ → _ → _
    setA a s with match p s
    ... | nothing = s
    ... | just _  = build p a

------------------------------------------------------------------------
-- Unified Optic: for composition and Big Optic
------------------------------------------------------------------------

record Optic (S A : Set) : Set where
  constructor mkOptic
  field
    peek : S → Maybe A           -- read (may fail for Prism/Traversal)
    over : (A → A) → S → S       -- modify in place

open Optic public

_∘O_ : Optic B C → Optic A B → Optic A C
inner ∘O outer = mkOptic
  (λ a → peek outer a >>= peek inner)
  (λ f → over outer (over inner f))

infixr 9 _∘O_

idOptic : Optic A A
idOptic = mkOptic just id

------------------------------------------------------------------------
-- Projections into unified Optic
------------------------------------------------------------------------

fromLens : Lens S A → Optic S A
fromLens l = mkOptic (just ∘ get l) (modify l)

fromPrism : Prism S A → Optic S A
fromPrism p = mkOptic (match p) overP
  where
    overP : (_ → _) → _ → _
    overP f s with match p s
    ... | nothing = s
    ... | just a  = build p (f a)

fromAffine : Affine S A → Optic S A
fromAffine af = mkOptic (Affine.preview af) overA
  where
    overA : (_ → _) → _ → _
    overA f s with Affine.preview af s
    ... | nothing = s
    ... | just x  = Affine.set af (f x) s

fromTraversal : Traversal S A → Optic S A
fromTraversal t = mkOptic firstOf (overAll t)
  where
    firstOf : _ → Maybe _
    firstOf s with toList t s
    ... | []     = nothing
    ... | x ∷ _ = just x

------------------------------------------------------------------------
-- routeMsg: automatic message routing via Prism + Lens
------------------------------------------------------------------------

routeMsg : ∀ {M M' Msg Msg'} →
           Prism Msg Msg' → Lens M M' →
           (Msg' → M' → M') →
           Msg → M → M
routeMsg p l childUpdate msg model with match p msg
... | nothing       = model
... | just childMsg = Lens.set l (childUpdate childMsg (get l model)) model

------------------------------------------------------------------------
-- Convenience: Lens + Prism → Optic
------------------------------------------------------------------------

_∘LP_ : Prism B C → Lens A B → Optic A C
p ∘LP l = fromPrism p ∘O fromLens l

_∘LO_ : Lens B C → Lens A B → Optic A C
inner ∘LO outer = fromLens (inner ∘L outer)

------------------------------------------------------------------------
-- List traversal and indexed access
------------------------------------------------------------------------

listTraversal : (S → List A) → ((A → A) → S → S) → Traversal S A
listTraversal = mkTraversal

ixList : ℕ → Affine (List A) A
ixList n = mkAffine (go n) (setAt n)
  where
    go : ℕ → List _ → Maybe _
    go _       []       = nothing
    go zero    (x ∷ _)  = just x
    go (suc n) (_ ∷ xs) = go n xs

    setAt : ℕ → _ → List _ → List _
    setAt _       _ []       = []
    setAt zero    a (_ ∷ xs) = a ∷ xs
    setAt (suc n) a (x ∷ xs) = x ∷ setAt n a xs
