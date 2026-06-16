{-# OPTIONS --without-K --guardedness #-}

-- Round-trip test for Crm.Wire codecs (#N6): decode (encode x) ≡ just x', and the
-- re-encoded string equals the original (string compare avoids needing record Eq).
-- Pure-Agda codecs → compiles + runs on GHC. Tricky values: ':'/'|' in payloads
-- (length-prefix robustness), nothing/just, every enum.
module CrmWireTest where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String; primStringEquality)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using () renaming (_++_ to _<>_)

open import Crm.Identity
open import Crm.Wire

infixr 1 _seq_
postulate
  putStrLn : String → IO ⊤
  _seq_    : IO ⊤ → IO ⊤ → IO ⊤
{-# FOREIGN GHC
  import qualified Data.Text.IO as TIO
  seqIO :: IO () -> IO () -> IO ()
  seqIO = (>>)
  #-}
{-# COMPILE GHC putStrLn = TIO.putStrLn #-}
{-# COMPILE GHC _seq_    = seqIO #-}

check : String → Bool → IO ⊤
check name ok = putStrLn (if ok then ("PASS " <> name) else ("FAIL " <> name))

rtParty : Party → Bool
rtParty p with decParty (encParty p)
... | just p' = primStringEquality (encParty p') (encParty p)
... | nothing = false

rtEng : Engagement → Bool
rtEng e with decEngagement (encEngagement e)
... | just e' = primStringEquality (encEngagement e') (encEngagement e)
... | nothing = false

rtAct : Activity → Bool
rtAct a with decActivity (encActivity a)
... | just a' = primStringEquality (encActivity a') (encActivity a)
... | nothing = false

rtPart : Participation → Bool
rtPart p with decParticipation (encParticipation p)
... | just p' = primStringEquality (encParticipation p') (encParticipation p)
... | nothing = false

rtAcc : Account → Bool
rtAcc a with decAccount (encAccount a)
... | just a' = primStringEquality (encAccount a') (encAccount a)
... | nothing = false

p1 = mkParty 7 Person "Полунин: с двоеточием" "Europe/Moscow" 1700000000 nothing
p2 = mkParty 8 Org "Орг|пайп" "UTC" 1700000001 (just 1700009999)
e1 = mkEngagement 3 2 5 (just "Заголовок: и | спецсимволы") 1700000000 nothing
e2 = mkEngagement 4 2 6 nothing 1700000000 (just 1700001)
a1 = mkActivity 9 3 1700005000 Scheduled 1700000000 nothing
a2 = mkActivity 10 3 1700006000 NoShow 1700000000 (just 1700002)
pp = mkParticipation 11 3 7 "provider" 1700000000
ac = mkAccount 5 1000 1700000000

main : IO ⊤
main =
  check "party-nothing"  (rtParty p1) seq
  check "party-just"     (rtParty p2) seq
  check "eng-just-title" (rtEng e1)   seq
  check "eng-nothing"    (rtEng e2)   seq
  check "act-scheduled"  (rtAct a1)   seq
  check "act-noshow"     (rtAct a2)   seq
  check "participation"  (rtPart pp)  seq
  check "account"        (rtAcc ac)
