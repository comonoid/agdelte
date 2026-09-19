{-# OPTIONS --without-K --guardedness #-}

-- Offline tests for the Stripe client's PURE functions (the network call needs a
-- real account, run in deployment). verifyWebhookSig = HMAC-SHA256(secret, t <> "." <>
-- body) vs ANY v1 in the Stripe-Signature header + freshness drift ≤ 300s — we check
-- accept/reject/multi-v1/freshness; parseWebhookFields is exercised on a real
-- checkout.session.completed-shaped body + on garbage.
module StripeTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Char using (Char; primCharEquality)
open import Agda.Builtin.String using (primStringToList)
open import Data.Bool using (Bool; not; _∨_; true; false; _∧_)
open import Data.List using (List; []; _∷_; concatMap)
open import Data.Maybe using (Maybe; just; nothing; is-nothing; is-just; maybe′)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.FFI.Crypto using (hmacSHA256)
open import Agdelte.Payment.Stripe
  using (verifyWebhookSig; parseWebhookFieldsRaw; parseWebhookFields; StripeEvent
        ; SessionCompleted; Unrecognized; RawPair; rpFst; rpSnd
        ; Currency; mkCurrency; curCode; Positive; mkPositive; amountOf)
open import Agdelte.Payment.StripeForm using (formEncS)
open import Agdelte.Payment.StripeVectors using (vectors)

postulate
  putStrLn : String → IO ⊤
  _seq_    : IO ⊤ → IO ⊤ → IO ⊤
  formEncHS : String → String   -- Haskell-версия энкодера из Agdelte.Payment.Stripe
infixr 1 _seq_
{-# FOREIGN GHC
  import qualified Data.Text.IO as TIO
  import qualified Data.Text as T
  seqIO :: IO () -> IO () -> IO ()
  seqIO = (>>)
  formEncHS' :: T.Text -> T.Text
  formEncHS' = T.pack . MAlonzo.Code.Agdelte.Payment.Stripe.formEnc
  #-}
{-# COMPILE GHC putStrLn = TIO.putStrLn #-}
{-# COMPILE GHC _seq_    = seqIO #-}
{-# COMPILE GHC formEncHS = formEncHS' #-}

_==ˢ_ : String → String → Bool
a ==ˢ b = primStringEquality a b

eqℕ : ℕ → ℕ → Bool
eqℕ a b = a ≡ᵇ b

secret : String
secret = "whsec-test"

t : String          -- unix seconds of the event (fresh vs now = 1_700_000_000)
t = "1700000000"

now : String
now = show 1700000000

body : String
body = "{\"id\":\"evt_1\",\"type\":\"checkout.session.completed\","
       <> "\"data\":{\"object\":{\"id\":\"cs_test_77\",\"payment_status\":\"paid\"}}}"

sig : String → String           -- well-formed header with a given (wrong or right) v1
sig v1 = "t=" <> t <> ",v1=" <> v1

goodV1 : String
goodV1 = hmacSHA256 secret (t <> "." <> body)

-- extract event / id from a parse result (defaulting on nothing)
evOf : Maybe RawPair → String
evOf (just pr) = rpFst pr
evOf nothing   = ""
idOf : Maybe RawPair → String
idOf (just pr) = rpSnd pr
idOf nothing   = ""

-- typed-event view (Level 2): classifier + projection for Boolean checks
isCompleted : StripeEvent → Bool
isCompleted (SessionCompleted _) = true
isCompleted Unrecognized         = false
sidOf : StripeEvent → String
sidOf (SessionCompleted s) = s
sidOf Unrecognized         = ""

-- в закодированном теле не должно быть сырых разделителей (' ', '=', '&', '+')
isSepChar : Char → Bool
isSepChar c = primCharEquality c '=' ∨ primCharEquality c '&'
              ∨ primCharEquality c ' ' ∨ primCharEquality c '+'

noSep : List Char → Bool
noSep []       = true
noSep (c ∷ cs) = and (not (isSepChar c)) (noSep cs)
  where
    and : Bool → Bool → Bool
    and true  b = b
    and false _ = false

chk : String → Bool → String × Bool
chk n b = n , b

checks : List (String × Bool)
checks =
  -- signature verification (HMAC-SHA256 over t <> "." <> body, ANY v1, freshness)
  chk "verify-accept-valid"     (verifyWebhookSig now secret (sig goodV1) body) ∷
  chk "verify-accept-any-v1"    (verifyWebhookSig now secret (sig goodV1 <> ",v1=deadbeef") body) ∷
  chk "verify-reject-badv1"     (not (verifyWebhookSig now secret (sig "deadbeef") body)) ∷
  chk "verify-reject-badsecret" (not (verifyWebhookSig now secret ("t=" <> t <> ",v1="
                                     <> hmacSHA256 "wrong-secret" (t <> "." <> body)) body)) ∷
  chk "verify-reject-tampered"  (not (verifyWebhookSig now secret (sig goodV1) (body <> "x"))) ∷
  chk "verify-reject-stale"     (not (verifyWebhookSig (show 1700001000) secret (sig goodV1) body)) ∷
  chk "verify-reject-future"    (not (verifyWebhookSig (show 1699998600) secret (sig goodV1) body)) ∷
  chk "verify-reject-no-t"      (not (verifyWebhookSig now secret ("v1=" <> goodV1) body)) ∷
  -- webhook field parsing (nested JSON, injection-safe)
  chk "parse-event"   (evOf (parseWebhookFieldsRaw body) ==ˢ "checkout.session.completed") ∷
  chk "parse-id"      (idOf (parseWebhookFieldsRaw body) ==ˢ "cs_test_77") ∷
  chk "parse-garbage" (is-nothing (parseWebhookFieldsRaw "not even json")) ∷
  -- typed StripeEvent (Ур.2): распознанное событие несёт session id, чужой тип
  -- и мусор = Unrecognized (диспетчер на сервере исчерпывающий по построению)
  chk "event-completed"     (isCompleted (parseWebhookFields body)
                             ∧ sidOf (parseWebhookFields body) ==ˢ "cs_test_77") ∷
  chk "event-unknown-type"  (not (isCompleted (parseWebhookFields
                                 "{\"type\":\"invoice.paid\",\"data\":{\"object\":{\"id\":\"in_1\"}}}"))) ∷
  chk "event-garbage"       (not (isCompleted (parseWebhookFields "not even json"))) ∷
  chk "event-no-obj-id"     (not (isCompleted (parseWebhookFields
                                 "{\"type\":\"checkout.session.completed\",\"data\":{}}"))) ∷
  -- typed currency/amount (Ур.1): mkCurrency/mkPositive отклоняют невалидные конфиги
  chk "cur-ok-lower"    (is-just (mkCurrency "eur")) ∷
  chk "cur-rej-upper"   (is-nothing (mkCurrency "USD")) ∷
  chk "cur-rej-empty"   (is-nothing (mkCurrency "")) ∷
  chk "cur-rej-mixed"   (is-nothing (mkCurrency "u1d")) ∷
  chk "cur-rej-len-2"   (is-nothing (mkCurrency "eu")) ∷
  chk "cur-rej-len-4"   (is-nothing (mkCurrency "euro")) ∷
  chk "cur-code-stable" (maybe′ (λ c → curCode c ==ˢ "eur") false (mkCurrency "eur")) ∷
  chk "amt-ok-one"      (maybe′ (λ a → eqℕ 1 (amountOf a)) false (mkPositive 1)) ∷
  chk "amt-rej-zero"    (is-nothing (mkPositive 0)) ∷
  -- form-urlencoded энкодер: Agda-версия ≡ Haskell-версии (зеркало), выход без
  -- разделителей тела (' ', '=', '&', '+') — класс бага «index too large» на кириллице
  chk "form-mirror-ascii"    (formEncS "a b=c&d+e" ==ˢ formEncHS "a b=c&d+e") ∷
  chk "form-mirror-cyrillic" (formEncS "Путь в точку — 10 встреч"
                                ==ˢ formEncHS "Путь в точку — 10 встреч") ∷
  chk "form-agda-cyr-expected"    (formEncS "Путь в точку — 10 встреч" ==ˢ "%D0%9F%D1%83%D1%82%D1%8C%20%D0%B2%20%D1%82%D0%BE%D1%87%D0%BA%D1%83%20%E2%80%94%2010%20%D0%B2%D1%81%D1%82%D1%80%D0%B5%D1%87") ∷
  chk "form-hs-cyr-expected"      (formEncHS "Путь в точку — 10 встреч" ==ˢ "%D0%9F%D1%83%D1%82%D1%8C%20%D0%B2%20%D1%82%D0%BE%D1%87%D0%BA%D1%83%20%E2%80%94%2010%20%D0%B2%D1%81%D1%82%D1%80%D0%B5%D1%87") ∷
  chk "form-mirror-percent"  (formEncS "10%" ==ˢ formEncHS "10%") ∷
  chk "form-mirror-empty"    (formEncS "" ==ˢ formEncHS "") ∷
  chk "form-exact-escape"    (formEncS "a b=c&d+e" ==ˢ "a%20b%3Dc%26d%2Be") ∷
  chk "form-no-sep-cyrillic" (noSep (primStringToList (formEncS "Путь в точку — 10 встреч"))) ∷
  chk "form-no-sep-mixed"    (noSep (primStringToList (formEncS "a b=c&d+e % Путь"))) ∷
  []

-- ─── Ур.4: векторы из OpenAPI-спеки (Agdelte.Payment.StripeVectors) ───────
-- Для каждого вектора (имя, вход, ожидание) три чека: expected (formEncS =
-- ожидание, посчитанное генератором по RFC 3986), mirror (Agda = Haskell),
-- no-sep (нет сырых ' ' '=' '&' '+'). Имена чеков — по вектору.
vecChecks : List (String × Bool)
vecChecks = concatMap v vectors
  where
    v : String × String × String → List (String × Bool)
    v (name , input , expected) =
      chk (name <> "-expected") (formEncS input ==ˢ expected) ∷
      chk (name <> "-mirror")   (formEncS input ==ˢ formEncHS input) ∷
      chk (name <> "-no-sep")   (noSep (primStringToList (formEncS input))) ∷
      []

report : String → Bool → IO ⊤
report name true  = putStrLn ("PASS " <> name)
report name false = putStrLn ("FAIL " <> name)

runAll : List (String × Bool) → IO ⊤
runAll []             = putStrLn "stripe done"
runAll ((n , b) ∷ xs) = report n b seq runAll xs

_++ℓ_ : List (String × Bool) → List (String × Bool) → List (String × Bool)
_++ℓ_ []       ys = ys
_++ℓ_ (x ∷ xs) ys = x ∷ _++ℓ_ xs ys

main : IO ⊤
main = runAll (checks ++ℓ vecChecks)
