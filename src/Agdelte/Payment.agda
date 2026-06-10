{-# OPTIONS --without-K --guardedness #-}

-- Payment processing via ЮKassa (YooKassa) REST API.
-- Server-side only (GHC backend).
--
-- Flow:
-- 1. Client → POST /api/purchase or /api/subscribe
-- 2. Server → ЮKassa POST /v3/payments → confirmation_url
-- 3. Client redirects to ЮKassa payment page
-- 4. ЮKassa → POST /api/payment-webhook (payment.succeeded / payment.canceled)
-- 5. Server verifies webhook, updates WAL state

module Agdelte.Payment where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Bool using (if_then_else_)
open import Data.String using (_++_; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
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

------------------------------------------------------------------------
-- HTTP manager (opaque, created once at startup)
------------------------------------------------------------------------

postulate
  HttpManager : Set
  newHttpManager : IO HttpManager

{-# FOREIGN GHC
  import qualified Network.HTTP.Client as HC
  import qualified Network.HTTP.Client.TLS as TLS
  import Network.HTTP.Types.Status (statusCode)

  type HttpManagerT = HC.Manager

  newHttpManagerHS :: IO HC.Manager
  newHttpManagerHS = TLS.newTlsManager
  #-}

{-# COMPILE GHC HttpManager = type HttpManagerT #-}
{-# COMPILE GHC newHttpManager = newHttpManagerHS #-}

------------------------------------------------------------------------
-- ЮKassa configuration
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
-- ЮKassa API (Haskell FFI)
------------------------------------------------------------------------

-- | Result of ЮKassa API call.
data PaymentResult : Set where
  PaymentOk    : String → String → PaymentResult  -- paymentId, confirmationUrl
  PaymentError : ℕ → String → PaymentResult        -- HTTP status, error text

-- FFI boundary tuple types. Agda's Σ/_×_ cannot appear in a COMPILE GHC type
-- (MAlonzo can't translate Σ), so triples/pairs crossing the FFI are bound to
-- Haskell tuples here and read back with the projections below.
private
  postulate
    RawTriple : Set
    rtNat     : RawTriple → ℕ
    rtFst     : RawTriple → String
    rtSnd     : RawTriple → String
    RawPair   : Set
    rpFst     : RawPair → String
    rpSnd     : RawPair → String
{-# FOREIGN GHC
  import qualified Data.Text as T
  type RawTripleH = (Integer, T.Text, T.Text)
  type RawPairH   = (T.Text, T.Text)
  #-}
{-# COMPILE GHC RawTriple = type RawTripleH #-}
{-# COMPILE GHC rtNat = (\ t -> case t of (n,_,_) -> n :: Integer) #-}
{-# COMPILE GHC rtFst = (\ t -> case t of (_,a,_) -> a :: T.Text) #-}
{-# COMPILE GHC rtSnd = (\ t -> case t of (_,_,b) -> b :: T.Text) #-}
{-# COMPILE GHC RawPair = type RawPairH #-}
{-# COMPILE GHC rpFst = (fst :: RawPairH -> T.Text) #-}
{-# COMPILE GHC rpSnd = (snd :: RawPairH -> T.Text) #-}

-- | Raw FFI: returns (httpStatus, field1, field2).
-- Success: (0, paymentId, confirmationUrl)
-- Error:   (statusCode, errorText, "")
private
  postulate
    createPaymentRaw : HttpManager → String → String → String → String → String → String → String
                     → IO RawTriple

-- | Create a payment in ЮKassa.
createPayment : HttpManager → String → String → String → String → String → String → String
              → IO PaymentResult
createPayment mgr shopId key amt desc ret idem meta =
  createPaymentRaw mgr shopId key amt desc ret idem meta >>= λ r →
  resolve (rtNat r) (rtFst r) (rtSnd r)
  where
    open Data.Nat using (zero; suc)
    resolve : ℕ → String → String → IO PaymentResult
    resolve zero    payId url = pure (PaymentOk payId url)
    resolve (suc n) err   _   = pure (PaymentError (suc n) err)

{-# FOREIGN GHC
  import qualified Data.Text as T
  import qualified Data.Text.Encoding as TE
  import qualified Data.ByteString.Lazy as LBS
  import qualified Data.ByteString.Char8 as BS8
  import qualified Data.ByteString.Base64 as B64
  import Data.Aeson (Value(..), object, (.=), encode, decode)
  import qualified Data.Aeson.KeyMap as KM
  import qualified Data.Aeson.Key as K
  import Control.Exception (try, SomeException)

  -- Returns (0, paymentId, confirmUrl) on success,
  --         (httpStatus, errorText, "") on error.
  createPaymentRawHS :: HC.Manager -> T.Text -> T.Text -> T.Text -> T.Text -> T.Text -> T.Text -> T.Text
                     -> IO (Integer, T.Text, T.Text)
  createPaymentRawHS mgr shopId secretKey amount desc returnUrl idemKey metadata = do
    let amountRub = case reads (T.unpack amount) :: [(Integer, String)] of
          [(k, _)] -> let r = k `div` 100
                          kop = k `mod` 100
                      in T.pack $ show r ++ "." ++ (if kop < 10 then "0" else "") ++ show kop
          _        -> "0.00"
        body = encode $ object
          [ "amount" .= object
              [ "value" .= amountRub
              , "currency" .= ("RUB" :: T.Text)
              ]
          , "confirmation" .= object
              [ "type" .= ("redirect" :: T.Text)
              , "return_url" .= returnUrl
              ]
          , "capture" .= True
          , "description" .= desc
          , "metadata" .= case decode (LBS.fromStrict $ TE.encodeUtf8 metadata) of
              Just v  -> (v :: Value)
              Nothing -> object []
          ]
        authHeader = "Basic " <> B64.encode (TE.encodeUtf8 shopId <> ":" <> TE.encodeUtf8 secretKey)
    initReq <- HC.parseRequest "POST https://api.yookassa.ru/v3/payments"
    let req = initReq
              { HC.requestBody = HC.RequestBodyLBS body
              , HC.requestHeaders =
                  [ ("Content-Type", "application/json")
                  , ("Idempotency-Key", TE.encodeUtf8 idemKey)
                  , ("Authorization", authHeader)
                  ]
              }
    result <- try (HC.httpLbs req mgr) :: IO (Either SomeException (HC.Response LBS.ByteString))
    case result of
      Left ex -> pure (0, T.pack $ "Network error: " ++ show ex, T.empty)
      Right resp -> do
        let status = fromIntegral (statusCode (HC.responseStatus resp)) :: Integer
            respBody = HC.responseBody resp
        if status >= 200 && status < 300
          then case decode respBody :: Maybe Value of
            Just (Object obj) -> do
              let mId = case KM.lookup (K.fromText "id") obj of
                    Just (String s) -> Just s
                    _               -> Nothing
                  mUrl = case KM.lookup (K.fromText "confirmation") obj of
                    Just (Object conf) -> case KM.lookup (K.fromText "confirmation_url") conf of
                      Just (String s) -> Just s
                      _               -> Nothing
                    _ -> Nothing
              case (mId, mUrl) of
                (Just pid, Just curl) -> pure (0, pid, curl)
                _ -> pure (status, T.pack "Missing id or confirmation_url in response", T.empty)
            _ -> pure (status, T.pack "Invalid JSON response", T.empty)
          else pure (status, TE.decodeUtf8 $ LBS.toStrict respBody, T.empty)
  #-}

{-# COMPILE GHC createPaymentRaw = createPaymentRawHS #-}

-- | Authoritatively fetch a payment's status from ЮKassa (GET /v3/payments/{id}).
-- Returns (0, status, "") on success where `status` is ЮKassa's own
-- "succeeded"/"canceled"/"pending"/… ; (httpStatus, errText, "") on error.
-- This is the source of truth for the webhook — the webhook body is NOT trusted.
private
  postulate
    getPaymentStatusRaw : HttpManager → String → String → String → IO RawTriple

{-# FOREIGN GHC
  getPaymentStatusRawHS :: HC.Manager -> T.Text -> T.Text -> T.Text
                        -> IO (Integer, T.Text, T.Text)
  getPaymentStatusRawHS mgr shopId secretKey paymentId = do
    let authHeader = "Basic " <> B64.encode (TE.encodeUtf8 shopId <> ":" <> TE.encodeUtf8 secretKey)
    result <- try (do
      initReq <- HC.parseRequest (T.unpack ("GET https://api.yookassa.ru/v3/payments/" <> paymentId))
      let req = initReq { HC.requestHeaders = [ ("Authorization", authHeader) ] }
      HC.httpLbs req mgr) :: IO (Either SomeException (HC.Response LBS.ByteString))
    case result of
      Left ex -> pure (0, T.pack ("Network error: " ++ show ex), T.empty)
      Right resp -> do
        let status = fromIntegral (statusCode (HC.responseStatus resp)) :: Integer
            respBody = HC.responseBody resp
        if status >= 200 && status < 300
          then case decode respBody :: Maybe Value of
            Just (Object obj) -> case KM.lookup (K.fromText "status") obj of
              Just (String s) -> pure (0, s, T.empty)
              _               -> pure (status, T.pack "Missing status in payment", T.empty)
            _ -> pure (status, T.pack "Invalid JSON response", T.empty)
          else pure (status, TE.decodeUtf8 $ LBS.toStrict respBody, T.empty)
  #-}

{-# COMPILE GHC getPaymentStatusRaw = getPaymentStatusRawHS #-}

-- | Parse a ЮKassa webhook body with a real JSON parser, returning
-- (event, object.id). Uses nested lookup (object → id) so it cannot be fooled
-- by an attacker injecting a top-level "id" the flat string scanner would grab.
private
  postulate
    parseWebhookFields : String → Maybe RawPair

{-# FOREIGN GHC
  parseWebhookFieldsHS :: T.Text -> Maybe (T.Text, T.Text)
  parseWebhookFieldsHS body =
    case decode (LBS.fromStrict (TE.encodeUtf8 body)) :: Maybe Value of
      Just (Object o) -> do
        ev <- case KM.lookup (K.fromText "event") o of
                Just (String s) -> Just s
                _               -> Nothing
        obj <- case KM.lookup (K.fromText "object") o of
                Just (Object x) -> Just x
                _               -> Nothing
        pid <- case KM.lookup (K.fromText "id") obj of
                Just (String s) -> Just s
                _               -> Nothing
        Just (ev, pid)
      _ -> Nothing
  #-}

{-# COMPILE GHC parseWebhookFields = parseWebhookFieldsHS #-}

-- | Verify ЮKassa webhook signature (HMAC-SHA256 of request body).
-- NOTE: defense-in-depth only. ЮKassa does not authenticate webhooks with a
-- body-HMAC header; the authoritative check is re-fetching the payment via
-- getPaymentStatusRaw (see handleVerified). Do not rely on this alone.
postulate
  verifyWebhookSig : String → String → String → Bool
  -- ^ secret, signature header, request body → valid?

{-# FOREIGN GHC
  import Crypto.MAC.HMAC (hmac, hmacGetDigest)
  import Crypto.Hash (SHA256)
  import qualified Data.ByteArray as BA

  verifyWebhookSigHS :: T.Text -> T.Text -> T.Text -> Bool
  verifyWebhookSigHS secret sigHeader body =
    let expected = T.pack $ show (hmacGetDigest
          (hmac (TE.encodeUtf8 secret) (TE.encodeUtf8 body) :: HMAC SHA256) :: BA.Bytes)
    in BA.constEq (TE.encodeUtf8 expected) (TE.encodeUtf8 sigHeader)
  #-}

{-# COMPILE GHC verifyWebhookSig = verifyWebhookSigHS #-}

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
-- We verify signature, then update WAL state.
handlePaymentWebhook : YooKassaConfig → WalHandle AppState AppOp
                     → HttpRequest → IO HttpResponse
handlePaymentWebhook yk wal req =
  let body = reqBody req
      -- Verify webhook signature (ЮKassa sends it in HTTP header)
      sigOk = case lookupHeader "X-Signature" (reqHeaders req) of λ where
                nothing  → false
                (just sig) → verifyWebhookSig (ykWebhookSecret yk) sig body
  in if sigOk then handleVerified body
     else pure (mkResponseH 403 "{\"error\":\"Invalid webhook signature\"}" corsHeaders)
  where
    open Data.Nat using (zero; suc)
    -- Resolve the AUTHORITATIVE ЮKassa payment status (fetched server-side,
    -- never taken from the webhook body) + paymentId into an atomic WAL op.
    -- Prevents TOCTOU race between walRead and walStep.
    purchOp : String → PurchaseRecord → Maybe AppOp
    purchOp status p with status ≟ "succeeded"
    ... | yes _ = just (UpdatePurchStatus (prId p) PurchPaid)
    ... | no _ with status ≟ "canceled"
    ...   | yes _ = just (UpdatePurchStatus (prId p) PurchRefunded)
    ...   | no _  = nothing

    -- "canceled" = payment failed/not confirmed → SubExpired.
    -- SubCancelled is for user-initiated cancellation of an active sub.
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

    -- Confirm the payment with ЮKassa and act on its authoritative status.
    -- A forged/replayed body can at most cause us to re-confirm a payment's
    -- TRUE status for an id we look up — it can never grant unpaid access.
    handleVerified : String → IO HttpResponse
    handleVerified body = case parseWebhookFields body of λ where
      nothing → pure (resp400 "Malformed webhook body")
      (just rp) →
        getPaymentStatusRaw (ykManager yk) (ykShopId yk) (ykSecretKey yk) (rpSnd rp) >>= λ r →
        confirm (rtNat r) (rtFst r) (rpSnd rp)
