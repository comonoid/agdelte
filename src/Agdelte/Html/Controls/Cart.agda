{-# OPTIONS --without-K #-}

-- Shopping cart: client-side state with localStorage persistence.
-- CSS classes: .agdelte-cart, .agdelte-cart__mini, .agdelte-cart__badge,
--              .agdelte-cart__item, .agdelte-cart__total

module Agdelte.Html.Controls.Cart where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Base using (filterᵇ)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _+_)
open import Data.Bool using (Bool; true; false; not)

open import Agda.Builtin.String using (primShowNat)
open import Agdelte.Reactive.Node
open import Agdelte.Storage.AppStore using (CourseId)

------------------------------------------------------------------------
-- Cart state
------------------------------------------------------------------------

record CartItem : Set where
  constructor mkCartItem
  field
    ciCourseId : CourseId
    ciTitle    : String
    ciPrice    : ℕ             -- kopecks

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

removeFromCart : CourseId → CartState → CartState
removeFromCart cid cart =
  mkCartState (filterᵇ (λ i → not (ciCourseId i ≡ᵇ cid)) (csItems cart))

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

-- | Mini cart icon with item count badge (for header).
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

-- | Format price in kopecks as rubles string: 1500 → "15.00"
postulate formatPriceImpl : ℕ → String
{-# COMPILE JS formatPriceImpl = function(kopecks) {
  var rubles = Math.floor(kopecks / 100);
  var kop = kopecks % 100;
  return rubles + '.' + (kop < 10 ? '0' + kop : '' + kop);
} #-}

formatPrice : ℕ → String
formatPrice = formatPriceImpl

-- | Cart total display.
cartTotalView : ∀ {M A}
              → (M → CartState)
              → Node M A
cartTotalView getCart =
  div (class "agdelte-cart__total" ∷ [])
    ( bindF (λ m → "Итого: " ++ formatPrice (cartTotal (getCart m)) ++ " ₽")
    ∷ [])
