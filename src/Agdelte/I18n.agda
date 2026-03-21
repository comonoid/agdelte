{-# OPTIONS --without-K #-}

-- Internationalization (i18n) module.
-- Locale-aware translations, currency and date formatting.

module Agdelte.I18n where

open import Data.String using (String; _++_; _≟_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

open import Agda.Builtin.String using (primShowNat)

------------------------------------------------------------------------
-- Locale
------------------------------------------------------------------------

data Locale : Set where
  Ru : Locale
  En : Locale

showLocale : Locale → String
showLocale Ru = "ru"
showLocale En = "en"

------------------------------------------------------------------------
-- Translation table
------------------------------------------------------------------------

-- | Translations: list of (key, value) pairs.
Translations = List (String × String)

-- | Look up a key in translations, returning the key itself if not found.
t : Translations → String → String
t [] key = key
t ((k , v) ∷ rest) key with k ≟ key
... | yes _ = v
... | no _  = t rest key

------------------------------------------------------------------------
-- Currency formatting
------------------------------------------------------------------------

-- | Format kopecks as currency string.
postulate
  formatCurrencyImpl : String → ℕ → String

{-# COMPILE JS formatCurrencyImpl = function(locale) { return function(kopecks) {
  var rubles = kopecks / 100;
  if (locale === 'ru') return rubles.toFixed(2).replace('.', ',') + ' \u20BD';
  return rubles.toFixed(2).replace('.', ',') + ' RUB';
}; } #-}

formatCurrency : Locale → ℕ → String
formatCurrency locale = formatCurrencyImpl (showLocale locale)

------------------------------------------------------------------------
-- Date formatting
------------------------------------------------------------------------

-- | Format unix timestamp as localized date string.
postulate
  formatDateImpl : String → ℕ → String

{-# COMPILE JS formatDateImpl = function(locale) { return function(ts) {
  var d = new Date(ts * 1000);
  return d.toLocaleDateString(locale === 'ru' ? 'ru-RU' : 'en-US');
}; } #-}

formatDate : Locale → ℕ → String
formatDate locale = formatDateImpl (showLocale locale)

------------------------------------------------------------------------
-- Plural forms (Russian)
------------------------------------------------------------------------

-- | Russian plural: "1 урок", "2 урока", "5 уроков"
postulate
  pluralRu : ℕ → String → String → String → String

{-# COMPILE JS pluralRu = function(n) { return function(one) { return function(few) { return function(many) {
  var mod10 = n % 10, mod100 = n % 100;
  if (mod10 === 1 && mod100 !== 11) return n + ' ' + one;
  if (mod10 >= 2 && mod10 <= 4 && (mod100 < 12 || mod100 > 14)) return n + ' ' + few;
  return n + ' ' + many;
}; }; }; } #-}
