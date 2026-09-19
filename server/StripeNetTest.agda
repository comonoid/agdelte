{-# OPTIONS --without-K --guardedness #-}

-- СЕТЕВОЙ смоук клиента Stripe против stripe-mock (.tmp-stripe-mock/stripe-mock).
-- Запуск ТОЛЬКО через npm run test:stripe-mock (раннер поднимает мок и
-- выставляет STRIPE_API_BASE). Против боевого API не запускать!
--
-- stripe-mock валидирует форму против OpenAPI-схемы (сам запрос должен быть
-- корректным) и возвращает фикстуры, поэтому проверки — про КЛИЕНТА:
--  * createCheckoutSession доходит до /v1/checkout/sessions и разбирается
--    в CheckoutOk (инвариант непустого url на живом пути);
--  * типизированные Currency/Positive принимаются моком (валидация схемы);
--  * Idempotency-Key проходит (повтор — тоже Ok);
--  * отказ авторизации (пустой секрет → 401) классифицируется как
--    CheckoutError 401, а НЕ маскируется в успех (класс бага «0 double-books»).
module StripeNetTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primStringEquality)
open import Data.Bool using (Bool; not; _∧_; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Nat using (ℕ; suc; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.Payment.Common using (HttpManager; newHttpManager; _>>=_; pure)
open import Agdelte.Payment.Stripe
  using (createCheckoutSession; PaymentResult; CheckoutOk; CheckoutError
        ; Currency; isoCur; mkCurrency; Positive; posNat)

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

eqℕ : ℕ → ℕ → Bool
eqℕ a b = a ≡ᵇ b

pos : ℕ → Positive
pos (suc n) = posNat (suc n) λ ()
pos zero    = posNat 1 λ ()

-- полный Currency из валидного кода (входы тестов — только "eur"/"usd")
cur : String → Currency
cur s = fromJust (mkCurrency s)
  where
    fromJust : Maybe Currency → Currency
    fromJust (just c) = c
    fromJust nothing  = isoCur "eur" λ ()   -- недостижимо для валидных входов

account : String
account = ""

secret : String
secret = "sk_test_mock"

desc : String
desc = "net smoke"

successUrl : String
successUrl = "https://example.com/success?sid={CHECKOUT_SESSION_ID}"

cancelUrl : String
cancelUrl = "https://example.com/cancel"

isOk : PaymentResult → Bool
isOk (CheckoutOk _ _ _)  = true
isOk (CheckoutError _ _) = false

errNat : PaymentResult → ℕ
errNat (CheckoutOk _ _ _)  = 0
errNat (CheckoutError n _) = n

ok : HttpManager → String → Currency → ℕ → String → IO PaymentResult
ok mgr key c n idem =
  createCheckoutSession mgr account key c (pos n) desc successUrl cancelUrl idem "" idem

chk : String → Bool → String × Bool
chk n b = n , b

report : String → Bool → IO ⊤
report name true  = putStrLn ("PASS " <> name)
report name false = putStrLn ("FAIL " <> name)

runAll : List (String × Bool) → IO ⊤
runAll []             = putStrLn "stripe-net done"
runAll ((n , b) ∷ xs) = report n b seq runAll xs

main : IO ⊤
main = newHttpManager >>= λ mgr →
  ok mgr secret (cur "eur") 1099 "net-idem-1" >>= λ r1 →
  ok mgr secret (cur "usd") 250  "net-idem-2" >>= λ r2 →
  ok mgr secret (cur "eur") 1099 "net-idem-1" >>= λ r3 →
  ok mgr ""      (cur "eur") 1099 "net-idem-3" >>= λ r4 →
  runAll
    ( chk "net-ok-eur"      (isOk r1) ∷
      chk "net-ok-usd"      (isOk r2) ∷
      chk "net-idempotent"  (isOk r3) ∷
      chk "net-auth-401"    (not (isOk r4) ∧ eqℕ 401 (errNat r4)) ∷
      [] )
