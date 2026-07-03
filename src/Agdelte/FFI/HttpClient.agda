{-# OPTIONS --without-K --guardedness #-}

-- Generic OUTBOUND HTTP client (GHC-only FFI). The framework-level primitive for delivery
-- adapters (webhooks, callbacks): POST a body to a URL with custom headers, return the HTTP
-- status (0 = network/connect failure — no exceptions escape). Deliberately minimal and
-- domain-agnostic; retry/backoff policy belongs to the caller.
module Agdelte.FFI.HttpClient where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List)

open import Agdelte.FFI.Server using (StrPair)

postulate
  HttpClientManager    : Set
  newHttpClientManager : IO HttpClientManager
  -- POST url body headers → status (0 on network failure)
  httpPostStatus       : HttpClientManager → String → String → List StrPair → IO Nat

{-# FOREIGN GHC
  import qualified Data.Text as T
  import qualified Data.Text.Encoding as TE
  import qualified Data.ByteString.Lazy as LBS
  import qualified Data.CaseInsensitive as CI
  import qualified Network.HTTP.Client as HC
  import qualified Network.HTTP.Client.TLS as TLS
  import qualified Network.HTTP.Types.Status as HS
  import qualified Control.Exception as Ex

  newHttpClientManagerHS :: IO HC.Manager
  newHttpClientManagerHS = TLS.newTlsManager

  httpPostStatusHS :: HC.Manager -> T.Text -> T.Text -> [(T.Text, T.Text)] -> IO Integer
  httpPostStatusHS mgr url body hdrs = do
    r <- Ex.try (do
           req0 <- HC.parseRequest (T.unpack url)
           let req = req0 { HC.method = "POST"
                          , HC.requestBody = HC.RequestBodyLBS (LBS.fromStrict (TE.encodeUtf8 body))
                          , HC.requestHeaders =
                              ("Content-Type", "application/json")
                                : [ (CI.mk (TE.encodeUtf8 k), TE.encodeUtf8 v) | (k, v) <- hdrs ]
                          }
           resp <- HC.httpLbs req mgr
           return (fromIntegral (HS.statusCode (HC.responseStatus resp))))
    case r of
      Right code -> return code
      Left (_ :: Ex.SomeException) -> return 0
  #-}

{-# COMPILE GHC HttpClientManager    = type HC.Manager #-}
{-# COMPILE GHC newHttpClientManager = newHttpClientManagerHS #-}
{-# COMPILE GHC httpPostStatus       = httpPostStatusHS #-}
