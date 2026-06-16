{-# OPTIONS --without-K --guardedness #-}

-- Course-platform payment HANDLERS (domain wiring), server-side only (GHC).
-- The provider-agnostic ЮKassa REST client (createPayment / getPaymentStatusRaw /
-- parseWebhookFields / verifyWebhookSig) lives in the `agdelte-payments` library
-- (Agdelte.Payment.YooKassa); this module wires it to the course AppStore + Auth.
--
-- Flow:
-- 1. Client → POST /api/purchase or /api/subscribe
-- 2. Server → ЮKassa POST /v3/payments → confirmation_url
-- 3. Client redirects to ЮKassa payment page
-- 4. ЮKassa → POST /api/payment-webhook (payment.succeeded / payment.canceled)
-- 5. Server re-fetches the authoritative status and updates WAL state

module Agdelte.Payment where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Bool using (if_then_else_)
open import Data.String using (_++_; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Relation.Nullary using (yes; no)

open import Agdelte.FFI.Server using
  ( HttpRequest; HttpResponse
  ; reqBody; reqHeaders; mkResponse; mkResponseH
  ; lookupHeader
  ; _>>=_; _>>_; pure
  )
open import Agdelte.FFI.Json using (jsonGetField; jsonGetNat; escapeJsonString)
open import Agdelte.Auth.Middleware using (corsHeaders; AuthRequest; authPayload; authRaw; authenticate)
open import Agdelte.Auth.Guard using (extractSub)
open import Agdelte.Storage.WAL using (WalHandle; walRead; walStep; walModify)
open import Agdelte.Storage.AppStore
open import Agdelte.FFI.Time using (getCurrentTime)
open import Agdelte.I18n using (Locale; Ru; En)
open import Agdelte.Util using (case_of_)

-- the provider-agnostic ЮKassa client (agdelte-payments library)
open import Agdelte.Payment.YooKassa using
  ( HttpManager
  ; PaymentResult; PaymentOk; PaymentError
  ; createPayment; getPaymentStatusRaw; rtNat; rtFst
  ; parseWebhookFields; rpSnd
  ; verifyWebhookSig )

------------------------------------------------------------------------
-- ЮKassa configuration (course-platform bundle: credentials + locale + manager)
------------------------------------------------------------------------

record YooKassaConfig : Set where
  constructor mkYooKassaConfig
  field
    ykShopId   : String      -- магазин ID
    ykSecretKey : String     -- секретный ключ API
    ykReturnUrl : String     -- URL возврата после оплаты
    ykWebhookSecret : String -- секрет для проверки webhook-подписи
    ykLocale   : Locale      -- для описаний платежей
    ykManager  : HttpManager -- TLS connection manager (create once via newHttpManager)

open YooKassaConfig public

-- | Localized payment description for a course.
coursePaymentDesc : Locale → String → String
coursePaymentDesc Ru title = "Курс: " ++ title
coursePaymentDesc En title = "Course: " ++ title

-- | Localized payment description for a subscription plan.
subPaymentDesc : Locale → String → String
subPaymentDesc Ru name = "Подписка: " ++ name
subPaymentDesc En name = "Subscription: " ++ name

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  resp400 : String → HttpResponse
  resp400 msg = mkResponseH 400 ("{\"error\":\"" ++ escapeJsonString msg ++ "\"}") corsHeaders

  resp200 : String → HttpResponse
  resp200 body = mkResponseH 200 body corsHeaders

  resp200ok : HttpResponse
  resp200ok = mkResponseH 200 "{\"ok\":true}" corsHeaders

  -- | Map ЮKassa error status to appropriate HTTP response.
  -- 0 → 503 (network), 401/403 → 500 (config), 422 → 400 (bad data), 429 → 503 (rate limit), else → 502.
  paymentErrorResp : ℕ → String → HttpResponse
  paymentErrorResp st msg =
    if st ≡ᵇ 0                       then mkResponseH 503 "{\"error\":\"Payment gateway unavailable\"}" corsHeaders
    else if (st ≡ᵇ 401) ∨ (st ≡ᵇ 403) then mkResponseH 500 "{\"error\":\"Payment gateway configuration error\"}" corsHeaders
    else if st ≡ᵇ 422                  then mkResponseH 400 ("{\"error\":\"" ++ escapeJsonString msg ++ "\"}") corsHeaders
    else if st ≡ᵇ 429                  then mkResponseH 503 "{\"error\":\"Payment gateway busy, try later\"}" corsHeaders
    else mkResponseH 502 ("{\"error\":\"Payment gateway error: " ++ escapeJsonString msg ++ "\"}") corsHeaders
    where open import Data.Nat using (_≡ᵇ_)
          open import Data.Bool using (_∨_; if_then_else_)

------------------------------------------------------------------------
-- POST /api/purchase — initiate individual course purchase
------------------------------------------------------------------------

-- Body: {"courseId": N}
-- Requires authentication (JWT).
-- Returns: {"confirmationUrl": "..."}
handlePurchase : YooKassaConfig → String → WalHandle AppState AppOp
              → HttpRequest → IO HttpResponse
handlePurchase yk jwtSecret wal req =
  getCurrentTime >>= λ now → helper now (authenticate jwtSecret now req)
  where
    helper : ℕ → Maybe String → IO HttpResponse
    helper _   nothing        = pure (mkResponseH 401 "{\"error\":\"Unauthorized\"}" corsHeaders)
    helper now (just payload) with extractSub payload
    ... | nothing = pure (mkResponseH 401 "{\"error\":\"Invalid token\"}" corsHeaders)
    ... | just uid =
      let body = reqBody req
      in case jsonGetNat "courseId" body of λ where
        nothing → pure (resp400 "Missing courseId")
        (just cid) →
          walRead wal >>= λ state →
          case findCourseById cid state of λ where
            nothing → pure (mkResponseH 404 "{\"error\":\"Course not found\"}" corsHeaders)
            (just course) →
              -- Check if already purchased
              if userHasCourse uid cid state
              then pure (resp400 "Already purchased")
              else
                let pid   = allocPurchaseId state
                    amt   = crPrice course
                    desc  = coursePaymentDesc (ykLocale yk) (crTitle course)
                    idemKey = "purchase-" ++ show uid ++ "-" ++ show cid
                    meta  = "{\"type\":\"purchase\",\"userId\":" ++ show uid
                         ++ ",\"courseId\":" ++ show cid ++ "}"
                in createPayment (ykManager yk) (ykShopId yk) (ykSecretKey yk)
                     (show amt) desc (ykReturnUrl yk) idemKey meta >>= λ where
                     (PaymentError st msg) → pure (paymentErrorResp st msg)
                     (PaymentOk paymentId confirmUrl) →
                       let purch = mkPurchaseRecord pid uid cid amt now paymentId PurchPending
                       in walStep wal (AddPurchase purch) >>= λ _ →
                          pure (resp200 ("{\"confirmationUrl\":\"" ++ escapeJsonString confirmUrl ++ "\"}"))

------------------------------------------------------------------------
-- POST /api/subscribe — initiate subscription
------------------------------------------------------------------------

-- Body: {"planId": N}
-- Requires authentication (JWT).
-- Returns: {"confirmationUrl": "..."}
handleSubscribe : YooKassaConfig → String → WalHandle AppState AppOp
               → HttpRequest → IO HttpResponse
handleSubscribe yk jwtSecret wal req =
  getCurrentTime >>= λ now → helper now (authenticate jwtSecret now req)
  where
    open Data.Nat using (_+_; _*_)
    helper : ℕ → Maybe String → IO HttpResponse
    helper _   nothing        = pure (mkResponseH 401 "{\"error\":\"Unauthorized\"}" corsHeaders)
    helper now (just payload) with extractSub payload
    ... | nothing = pure (mkResponseH 401 "{\"error\":\"Invalid token\"}" corsHeaders)
    ... | just uid =
      let body = reqBody req
      in case jsonGetNat "planId" body of λ where
        nothing → pure (resp400 "Missing planId")
        (just planId) →
          walRead wal >>= λ state →
          case findPlanById planId state of λ where
            nothing → pure (mkResponseH 404 "{\"error\":\"Plan not found\"}" corsHeaders)
            (just plan) →
              -- Check if already has active or pending subscription
              if hasActiveSubscription uid now state
              then pure (resp400 "Already subscribed")
              else if hasPendingSubscription uid state
              then pure (resp400 "Payment already in progress")
              else
                let sid     = allocSubId state
                    amt     = plPrice plan
                    desc    = subPaymentDesc (ykLocale yk) (plName plan)
                    idemKey = "sub-" ++ show uid ++ "-" ++ show planId
                    meta    = "{\"type\":\"subscription\",\"userId\":" ++ show uid
                           ++ ",\"planId\":" ++ show planId ++ "}"
                in createPayment (ykManager yk) (ykShopId yk) (ykSecretKey yk)
                     (show amt) desc (ykReturnUrl yk) idemKey meta >>= λ where
                     (PaymentError st msg) → pure (paymentErrorResp st msg)
                     (PaymentOk paymentId confirmUrl) →
                       let endDate = now + plDays plan * 86400
                           sub = mkSubscriptionRecord sid uid planId SubPending now endDate true paymentId
                       in walStep wal (AddSubscription sub) >>= λ _ →
                          pure (resp200 ("{\"confirmationUrl\":\"" ++ escapeJsonString confirmUrl ++ "\"}"))

------------------------------------------------------------------------
-- POST /api/payment-webhook — ЮKassa callback
------------------------------------------------------------------------

-- ЮKassa sends: {"event":"payment.succeeded", "object":{"id":"...", "metadata":{...}}}
-- We verify signature, re-fetch the authoritative status, then update WAL state.
handlePaymentWebhook : YooKassaConfig → WalHandle AppState AppOp
                     → HttpRequest → IO HttpResponse
handlePaymentWebhook yk wal req =
  let body = reqBody req
      sigOk = case lookupHeader "X-Signature" (reqHeaders req) of λ where
                nothing  → false
                (just sig) → verifyWebhookSig (ykWebhookSecret yk) sig body
  in if sigOk then handleVerified body
     else pure (mkResponseH 403 "{\"error\":\"Invalid webhook signature\"}" corsHeaders)
  where
    open Data.Nat using (zero; suc)
    purchOp : String → PurchaseRecord → Maybe AppOp
    purchOp status p with status ≟ "succeeded"
    ... | yes _ = just (UpdatePurchStatus (prId p) PurchPaid)
    ... | no _ with status ≟ "canceled"
    ...   | yes _ = just (UpdatePurchStatus (prId p) PurchRefunded)
    ...   | no _  = nothing

    subOp : String → SubscriptionRecord → Maybe AppOp
    subOp status sub with status ≟ "succeeded"
    ... | yes _ = just (UpdateSubStatus (sbId sub) SubActive)
    ... | no _ with status ≟ "canceled"
    ...   | yes _ = just (UpdateSubStatus (sbId sub) SubExpired)
    ...   | no _  = nothing

    resolveOp : String → String → AppState → Maybe AppOp
    resolveOp status payId state with findPurchaseByPaymentId payId state
    ... | just p  = purchOp status p
    ... | nothing with findSubByPaymentId payId state
    ...   | just sub = subOp status sub
    ...   | nothing  = nothing

    -- Act on ЮKassa's authoritative status: 0 = fetched OK (apply the op);
    -- non-zero = couldn't confirm → leave state unchanged (never grant access).
    confirm : ℕ → String → String → IO HttpResponse
    confirm zero    status payId =
      walModify wal (resolveOp status payId) >>= λ _ → pure resp200ok
    confirm (suc _) _      _     = pure resp200ok

    -- The webhook body is NOT trusted: we re-fetch the payment's TRUE status.
    handleVerified : String → IO HttpResponse
    handleVerified body = case parseWebhookFields body of λ where
      nothing → pure (resp400 "Malformed webhook body")
      (just rp) →
        getPaymentStatusRaw (ykManager yk) (ykShopId yk) (ykSecretKey yk) (rpSnd rp) >>= λ r →
        confirm (rtNat r) (rtFst r) (rpSnd rp)
