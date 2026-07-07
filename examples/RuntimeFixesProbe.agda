{-# OPTIONS --without-K #-}

-- RuntimeFixesProbe — probe app for test/runtime-fixes.test.js (аудит cxm-ui №6/2026-07-07):
-- regression coverage IN THIS REPO for four runtime fixes that were previously guarded only by
-- a downstream smoke (cxm-ui): (1) foreachKeyed re-renders a row whose ITEM changed under the
-- same key; (2) value-binding diffs against the LIVE input value (intra-batch round-trip);
-- (3) httpPostH delivers the non-2xx response BODY to the error callback; (4) Agda 2.9
-- object-encoded pairs flow through agdaHeadersToObj (the header list below compiles to them).
module RuntimeFixesProbe where

open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_])
open import Data.Product using (_×_; _,_)

open import Agdelte.Core.Cmd using (Cmd; ε; httpPostH)
open import Agdelte.Core.Event using (never)
open import Agdelte.Reactive.Node

record Item : Set where
  constructor mkItem
  field iid : ℕ ; ilabel : String
open Item public

record Model : Set where
  constructor mkModel
  field
    items      : List Item
    txt        : String
    httpResult : String
open Model public

init0 : Model
init0 = mkModel (mkItem 1 "a" ∷ mkItem 2 "b" ∷ []) "" ""

data Msg : Set where
  Bump   : Msg               -- same keys, row 1 gets new content (keyed re-render probe)
  SetTxt : String → Msg
  Submit : Msg               -- txt round-trip → "" (value-binding probe)
  Fire   : Msg               -- httpPostH with a header (error-body + object-pairs probe)
  GotOk  : String → Msg
  GotErr : String → Msg

update0 : Msg → Model → Model
update0 Bump m       = record m { items = mkItem 1 "A!" ∷ mkItem 2 "b" ∷ [] }
update0 (SetTxt s) m = record m { txt = s }
update0 Submit m     = record m { txt = "" }
update0 Fire m       = m
update0 (GotOk s) m  = record m { httpResult = "ok:" ++ s }
update0 (GotErr s) m = record m { httpResult = "err:" ++ s }

cmd0 : Msg → Model → Cmd Msg
cmd0 Fire _ = httpPostH "http://probe.test/x" (("X-Probe" , "1") ∷ []) "{}" GotOk GotErr
cmd0 _    _ = ε

private
  row : Item → ℕ → Node Model Msg
  row it _ = li (class "row" ∷ []) [ text (ilabel it) ]

template0 : Node Model Msg
template0 = div (class "probe" ∷ [])
  ( button (onClick Bump ∷ class "bump" ∷ []) [ text "bump" ]
  ∷ button (onClick Submit ∷ class "submit" ∷ []) [ text "submit" ]
  ∷ button (onClick Fire ∷ class "fire" ∷ []) [ text "fire" ]
  ∷ input (valueBind txt ∷ onInput SetTxt ∷ class "inp" ∷ [])
  ∷ span (class "res" ∷ []) [ bindF httpResult ]
  ∷ ul [] ( foreachKeyed items (λ it → show (iid it)) row ∷ [] )
  ∷ [] )

app : ReactiveApp Model Msg
app = mkReactiveApp init0 update0 template0 cmd0 (λ _ → never)
