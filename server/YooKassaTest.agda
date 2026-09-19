{-# OPTIONS --without-K --guardedness #-}

-- Offline tests for the ЮKassa client's PURE functions (the network call needs a
-- real merchant + the sandbox, run in deployment). verifyWebhookSig = HMAC-SHA256
-- of the raw body — accept/reject; parseWebhookFields on a real ЮKassa-shaped
-- body + garbage; typed YooKassaEvent (Ур.2); typed Currency/Positive (Ур.1);
-- форматтер суммы fmtAmount: зеркало с Haskell fmtKop + векторы из OpenAPI-спеки
-- ЮKassa (Ур.4, Agdelte.Payment.YooKassaVectors).
module YooKassaTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.String using (primStringToList)
open import Data.Nat using (_∸_)
open import Agda.Builtin.Char using (Char; primCharEquality)
open import Data.Bool using (Bool; not; _∧_; _∨_; true; false)
open import Data.Char using (toℕ)
open import Data.List using (List; []; _∷_; concatMap)
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing; maybe′)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.FFI.Crypto using (hmacSHA256)
open import Agdelte.Payment.YooKassa
  using (verifyWebhookSig; parseWebhookFieldsRaw; parseWebhookFields
        ; YooKassaEvent; PaymentSucceeded; PaymentCanceled; Unrecognized
        ; RawPair; rpFst; rpSnd; fmtKopHS
        ; Currency; curCode; rub; eur; usd; kzt; byn; uah; uzs; try; inr; mdl; azn; amd
        ; Positive; posNat; mkPositive; amountOf; fmtAmount)
open import Agdelte.Payment.YooKassaVectors using (vectors)

postulate
  putStrLn : String → IO ⊤
  _seq_    : IO ⊤ → IO ⊤ → IO ⊤
infixr 1 _seq_
{-# FOREIGN GHC
  import qualified Data.Text.IO as TIO
  seqIO :: IO () -> IO () -> IO ()
  seqIO = (>>)
  #-}
{-# COMPILE GHC putStrLn = TIO.putStrLn #-}
{-# COMPILE GHC _seq_    = seqIO #-}

_==ˢ_ : String → String → Bool
a ==ˢ b = primStringEquality a b

eqℕ : ℕ → ℕ → Bool
eqℕ a b = a ≡ᵇ b

-- Полный Positive из ℕ (входы тестов всегда ≥ 1; ноль непредставим — берём 1)
mkPos : ℕ → Positive
mkPos (suc n) = posNat (suc n) λ ()
mkPos zero    = posNat 1 λ ()

secret : String
secret = "whsec-test"

body : String
body = "{\"event\":\"payment.succeeded\",\"object\":{\"id\":\"yk-77\",\"status\":\"succeeded\"}}"

goodSig : String
goodSig = hmacSHA256 secret body

-- extract event / id from a parse result (defaulting on nothing)
evOf : Maybe RawPair → String
evOf (just pr) = rpFst pr
evOf nothing   = ""
idOf : Maybe RawPair → String
idOf nothing   = ""
idOf (just pr) = rpSnd pr

-- typed-event view (Ур.2): classifier + projections for Boolean checks
isSucceeded : YooKassaEvent → Bool
isSucceeded (PaymentSucceeded _) = true
isSucceeded _                    = false

isCanceled : YooKassaEvent → Bool
isCanceled (PaymentCanceled _) = true
isCanceled _                   = false

pidOf : YooKassaEvent → String
pidOf (PaymentSucceeded p) = p
pidOf (PaymentCanceled p)  = p
pidOf Unrecognized         = ""

canceledBody : String
canceledBody = "{\"event\":\"payment.canceled\",\"object\":{\"id\":\"yk-78\"}}"

-- вход вектора: десятичная строка копеек → ℕ (входы генератора — только цифры)
natOf : String → ℕ
natOf s = go 0 (primStringToList s)
  where
    dig : Char → ℕ
    dig c = toℕ c ∸ 48
    go : ℕ → List Char → ℕ
    go acc []       = acc
    go acc (c ∷ cs) = go (acc * 10 + dig c) cs

-- в выводе форматтера не должно быть сырых JSON-враждебных символов ('"', '\')
isBadChar : Char → Bool
isBadChar c = primCharEquality c '"' ∨ primCharEquality c '\\'

noBad : List Char → Bool
noBad []       = true
noBad (c ∷ cs) = and (not (isBadChar c)) (noBad cs)
  where
    and : Bool → Bool → Bool
    and true  b = b
    and false _ = false

chk : String → Bool → String × Bool
chk n b = n , b

checks : List (String × Bool)
checks =
  -- signature verification (HMAC-SHA256 of the raw body)
  chk "verify-accept-valid"     (verifyWebhookSig secret goodSig body) ∷
  chk "verify-reject-badsig"    (not (verifyWebhookSig secret "deadbeef" body)) ∷
  chk "verify-reject-badsecret" (not (verifyWebhookSig "wrong-secret" goodSig body)) ∷
  chk "verify-reject-tampered"  (not (verifyWebhookSig secret goodSig (body <> "x"))) ∷
  -- webhook field parsing (nested JSON, injection-safe)
  chk "parse-event"   (evOf (parseWebhookFieldsRaw body) ==ˢ "payment.succeeded") ∷
  chk "parse-id"      (idOf (parseWebhookFieldsRaw body) ==ˢ "yk-77") ∷
  chk "parse-garbage" (is-nothing (parseWebhookFieldsRaw "not even json")) ∷
  chk "parse-no-obj"  (is-nothing (parseWebhookFieldsRaw "{\"event\":\"payment.succeeded\"}")) ∷
  -- typed YooKassaEvent (Ур.2): распознанное событие несёт payment id, чужой
  -- event и мусор = Unrecognized (диспетчер на сервере исчерпывающий)
  chk "event-succeeded"    (isSucceeded (parseWebhookFields body)
                             ∧ pidOf (parseWebhookFields body) ==ˢ "yk-77") ∷
  chk "event-canceled"     (isCanceled (parseWebhookFields canceledBody)
                             ∧ pidOf (parseWebhookFields canceledBody) ==ˢ "yk-78") ∷
  chk "event-unknown-type" (not (isSucceeded (parseWebhookFields
                                 "{\"event\":\"refund.succeeded\",\"object\":{\"id\":\"r-1\"}}"))) ∷
  chk "event-garbage"      (not (isSucceeded (parseWebhookFields "not even json"))) ∷
  -- typed currency/amount (Ур.1): enum из спеки, mkPositive отклоняет ноль
  chk "cur-rub"      (curCode rub ==ˢ "RUB") ∷
  chk "cur-eur"      (curCode eur ==ˢ "EUR") ∷
  chk "cur-try"      (curCode try ==ˢ "TRY") ∷
  chk "cur-amd"      (curCode amd ==ˢ "AMD") ∷
  chk "amt-ok-one"   (maybe′ (λ a → eqℕ 1 (amountOf a)) false (mkPositive 1)) ∷
  chk "amt-rej-zero" (is-nothing (mkPositive 0)) ∷
  -- форматтер суммы: Agda fmtAmount ≡ Haskell fmtKop (зеркало) + правила спеки
  chk "fmt-mirror-1"     (fmtAmount (mkPos 1)     ==ˢ fmtKopHS "1") ∷
  chk "fmt-agda-1"       (fmtAmount (mkPos 1)     ==ˢ "0.01") ∷
  chk "fmt-agda-10"      (fmtAmount (mkPos 10)    ==ˢ "0.10") ∷
  chk "fmt-agda-100"     (fmtAmount (mkPos 100)   ==ˢ "1.00") ∷
  chk "fmt-agda-12345"   (fmtAmount (mkPos 12345) ==ˢ "123.45") ∷
  chk "fmt-hs-12345"     (fmtKopHS "12345" ==ˢ "123.45") ∷
  chk "fmt-agda-100000"  (fmtAmount (mkPos 100000) ==ˢ "1000.00") ∷
  chk "fmt-no-bad-12345" (noBad (primStringToList (fmtAmount (mkPos 12345)))) ∷
  []

-- ─── Ур.4: векторы из OpenAPI-спеки (Agdelte.Payment.YooKassaVectors) ─────
-- Для каждого вектора (имя, копейки, ожидание "R.KK") три чека: expected
-- (fmtAmount = ожидание, посчитанное генератором по спеке), mirror (Agda =
-- Haskell fmtKop), no-raw-json (нет сырых '"' и '\'). Имена чеков — по вектору.
vecChecks : List (String × Bool)
vecChecks = concatMap v vectors
  where
    v : String × String × String → List (String × Bool)
    v (name , kop , expected) =
      chk (name <> "-expected")    (fmtAmount (mkPos (natOf kop)) ==ˢ expected) ∷
      chk (name <> "-mirror")      (fmtAmount (mkPos (natOf kop)) ==ˢ fmtKopHS kop) ∷
      chk (name <> "-no-raw-json") (noBad (primStringToList (fmtAmount (mkPos (natOf kop))))) ∷
      []

report : String → Bool → IO ⊤
report name true  = putStrLn ("PASS " <> name)
report name false = putStrLn ("FAIL " <> name)

runAll : List (String × Bool) → IO ⊤
runAll []             = putStrLn "yookassa done"
runAll ((n , b) ∷ xs) = report n b seq runAll xs

_++ℓ_ : List (String × Bool) → List (String × Bool) → List (String × Bool)
_++ℓ_ []       ys = ys
_++ℓ_ (x ∷ xs) ys = x ∷ _++ℓ_ xs ys

main : IO ⊤
main = runAll (checks ++ℓ vecChecks)
