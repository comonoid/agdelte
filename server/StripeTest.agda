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
open import Data.Bool using (Bool; not)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; is-nothing)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.FFI.Crypto using (hmacSHA256)
open import Agdelte.Payment.Stripe using (verifyWebhookSig; parseWebhookFields; RawPair; rpFst; rpSnd)

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
  chk "parse-event"   (evOf (parseWebhookFields body) ==ˢ "checkout.session.completed") ∷
  chk "parse-id"      (idOf (parseWebhookFields body) ==ˢ "cs_test_77") ∷
  chk "parse-garbage" (is-nothing (parseWebhookFields "not even json")) ∷
  []

report : String → Bool → IO ⊤
report name true  = putStrLn ("PASS " <> name)
report name false = putStrLn ("FAIL " <> name)

runAll : List (String × Bool) → IO ⊤
runAll []             = putStrLn "stripe done"
runAll ((n , b) ∷ xs) = report n b seq runAll xs

main : IO ⊤
main = runAll checks
