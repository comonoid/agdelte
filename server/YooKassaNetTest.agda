{-# OPTIONS --without-K --guardedness #-}

-- СЕТЕВОЙ смоук клиента ЮKassa против мока (scripts/yookassa-mock.mjs).
-- Запуск ТОЛЬКО через npm run test:yk-mock (раннер поднимает мок и
-- выставляет YOOKASSA_API_BASE). Против боевого API не запускать!
--
-- Проверяет сетевой путь, который офлайн-тесты не трогают:
--  * createPayment доходит до /v3/payments, ответ разбирается в PaymentOk;
--  * валюта из enum Currency РЕАЛЬНО попадает в тело (мок отвечает 400
--    «currency mismatch» при расхождении — пин на баг «всегда RUB»);
--  * Идемпотентность: тот же Idempotency-Key → тот же платёж;
--  * пустой confirmation_url от сервера ⇒ PaymentError (не PaymentOk) —
--    инвариант PaymentOk работает на живом пути;
--  * getPaymentStatusRaw возвращает статус платежа.
module YooKassaNetTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.String using (primStringToList; primStringFromList)
open import Data.Bool using (Bool; not; _∧_; true; false)
open import Data.List using (List; []; _∷_; take)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.Payment.Common using (HttpManager; newHttpManager; _>>=_; pure)
open import Agdelte.Payment.YooKassa
  using (createPayment; getPaymentStatusRaw; PaymentResult
        ; PaymentOk; PaymentError; Currency; rub; eur; Positive; posNat; rtNat; rtFst)

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

pos : ℕ → Positive
pos (suc n) = posNat (suc n) λ ()
pos zero    = posNat 1 λ ()

shopId : String
shopId = "54401"

shopKey : String
shopKey = "test_key"

returnUrl : String
returnUrl = "https://example.com/return"

isOk : PaymentResult → Bool
isOk (PaymentOk _ _ _)  = true
isOk (PaymentError _ _) = false

urlOf : PaymentResult → String
urlOf (PaymentOk _ url _) = url
urlOf _                   = ""

extOf : PaymentResult → String
extOf (PaymentOk ext _ _) = ext
extOf _                 = ""

-- url начинается с https://mock.yk/pay/ (первые 19 символов)
urlOk : PaymentResult → Bool
urlOk (PaymentOk _ url _) =
  _==ˢ_ (primStringFromList (take 20 (primStringToList url))) "https://mock.yk/pay/"
urlOk (PaymentError _ _) = false

chk : String → Bool → String × Bool
chk n b = n , b

report : String → Bool → IO ⊤
report name true  = putStrLn ("PASS " <> name)
report name false = putStrLn ("FAIL " <> name)

runAll : List (String × Bool) → IO ⊤
runAll []             = putStrLn "yookassa-net done"
runAll ((n , b) ∷ xs) = report n b seq runAll xs

main : IO ⊤
main = newHttpManager >>= λ mgr →
  createPayment mgr shopId shopKey rub (pos 1099) "EXPECTCUR=RUB" returnUrl "net-idem-rub" "" >>= λ r1 →
  createPayment mgr shopId shopKey eur (pos 250)  "EXPECTCUR=EUR" returnUrl "net-idem-eur" "" >>= λ r2 →
  createPayment mgr shopId shopKey rub (pos 500)  "DUP"           returnUrl "net-idem-dup" "" >>= λ r3a →
  createPayment mgr shopId shopKey rub (pos 500)  "DUP"           returnUrl "net-idem-dup" "" >>= λ r3b →
  createPayment mgr shopId shopKey rub (pos 100)  "EMPTY_URL"     returnUrl "net-idem-empty" "" >>= λ r4 →
  getPaymentStatusRaw mgr shopId shopKey (extOf r1) >>= λ st →
  runAll
    ( chk "net-ok-rub"        (isOk r1 ∧ urlOk r1) ∷
      chk "net-cur-eur"       (isOk r2 ∧ urlOk r2) ∷
      chk "net-idempotent"    (isOk r3a ∧ extOf r3a ==ˢ extOf r3b) ∷
      chk "net-empty-url-err" (not (isOk r4)) ∷
      chk "net-status"        (eqℕ 0 (rtNat st) ∧ rtFst st ==ˢ "succeeded") ∷
      [] )
