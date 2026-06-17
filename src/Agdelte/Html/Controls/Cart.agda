{-# OPTIONS --without-K #-}

-- Shopping-cart tools: a pure cart state (add/remove/total/count) + a mini-cart
-- badge and a total view. Domain-neutral — items are identified by a plain ℕ; the
-- host persists/holds the CartState however it likes (e.g. localStorage). Emits BEM
-- classes .agdelte-cart__{mini,badge,total}; styling is the consumer's.

module Agdelte.Html.Controls.Cart where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Base using (filterᵇ)
open import Data.Nat using (ℕ; zero; _≡ᵇ_; _+_)
open import Data.Bool using (not)

open import Agda.Builtin.String using (primShowNat)
open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Cart state
------------------------------------------------------------------------

ItemId : Set
ItemId = ℕ

record CartItem : Set where
  constructor mkCartItem
  field
    ciItemId : ItemId
    ciTitle  : String
    ciPrice  : ℕ             -- minor units (e.g. kopecks)

open CartItem public

record CartState : Set where
  constructor mkCartState
  field
    csItems : List CartItem

open CartState public

emptyCart : CartState
emptyCart = mkCartState []

------------------------------------------------------------------------
-- Cart operations (pure)
------------------------------------------------------------------------

addToCart : CartItem → CartState → CartState
addToCart item cart = mkCartState (item ∷ csItems cart)

removeFromCart : ItemId → CartState → CartState
removeFromCart iid cart =
  mkCartState (filterᵇ (λ i → not (ciItemId i ≡ᵇ iid)) (csItems cart))

cartTotal : CartState → ℕ
cartTotal cart = sumPrices (csItems cart)
  where
    sumPrices : List CartItem → ℕ
    sumPrices [] = zero
    sumPrices (i ∷ is) = ciPrice i + sumPrices is

cartCount : CartState → ℕ
cartCount cart = length (csItems cart)

------------------------------------------------------------------------
-- Cart UI
------------------------------------------------------------------------

-- | Mini cart icon with item-count badge (for a header).
miniCart : ∀ {M A}
         → (M → CartState)
         → A                      -- on click (open cart page)
         → Node M A
miniCart getCart openCartMsg =
  div (class "agdelte-cart__mini" ∷ onClick openCartMsg ∷ [])
    ( text "🛒"
    ∷ span (class "agdelte-cart__badge" ∷ [])
        ( bindF (λ m → primShowNat (cartCount (getCart m))) ∷ [] )
    ∷ [])

-- | Format minor units (kopecks/cents) as a major-unit string: 1500 → "15.00"
postulate formatPriceImpl : ℕ → String
{-# COMPILE JS formatPriceImpl = function(kopecks) {
  var k = Number(kopecks);
  var rubles = Math.floor(k / 100);
  var kop = k % 100;
  return rubles + '.' + (kop < 10 ? '0' + kop : '' + kop);
} #-}

formatPrice : ℕ → String
formatPrice = formatPriceImpl

-- | Cart total display. `currency` is the suffix (e.g. "₽"); `label` the prefix.
cartTotalView : ∀ {M A}
              → String              -- label prefix (e.g. "Итого:")
              → String              -- currency suffix (e.g. "₽")
              → (M → CartState)
              → Node M A
cartTotalView label currency getCart =
  div (class "agdelte-cart__total" ∷ [])
    ( bindF (λ m → label ++ " " ++ formatPrice (cartTotal (getCart m)) ++ " " ++ currency)
    ∷ [])
