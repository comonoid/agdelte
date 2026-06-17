{-# OPTIONS --without-K --guardedness #-}

-- Offline tests for the ЮKassa client's PURE functions (the network calls need a real
-- merchant + the sandbox, run in deployment). verifyWebhookSig uses the same HMAC-SHA256
-- as FFI.Crypto, so a valid signature = hmacSHA256 secret body — we check accept/reject;
-- parseWebhookFields is exercised on a real ЮKassa-shaped body + on garbage.
module YooKassaTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String; primStringEquality)
open import Data.Bool using (Bool; not)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using () renaming (_++_ to _<>_)

open import Agdelte.FFI.Crypto using (hmacSHA256)
open import Agdelte.Payment.YooKassa using (verifyWebhookSig; parseWebhookFields; RawPair; rpFst; rpSnd)

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

body : String
body = "{\"event\":\"payment.succeeded\",\"object\":{\"id\":\"yk-77\",\"status\":\"succeeded\"}}"

goodSig : String
goodSig = hmacSHA256 secret body

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
  -- signature verification (HMAC-SHA256 of the body)
  chk "verify-accept-valid"   (verifyWebhookSig secret goodSig body) ∷
  chk "verify-reject-badsig"  (not (verifyWebhookSig secret "deadbeef" body)) ∷
  chk "verify-reject-badsecret" (not (verifyWebhookSig "wrong-secret" goodSig body)) ∷
  chk "verify-reject-tampered" (not (verifyWebhookSig secret goodSig (body <> "x"))) ∷
  -- webhook field parsing (nested JSON, injection-safe)
  chk "parse-event"   (evOf (parseWebhookFields body) ==ˢ "payment.succeeded") ∷
  chk "parse-id"      (idOf (parseWebhookFields body) ==ˢ "yk-77") ∷
  chk "parse-garbage" (is-nothing (parseWebhookFields "not even json")) ∷
  []

report : String → Bool → IO ⊤
report name true  = putStrLn ("PASS " <> name)
report name false = putStrLn ("FAIL " <> name)

runAll : List (String × Bool) → IO ⊤
runAll []             = putStrLn "yookassa done"
runAll ((n , b) ∷ xs) = report n b seq runAll xs

main : IO ⊤
main = runAll checks
