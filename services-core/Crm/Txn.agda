{-# OPTIONS --without-K #-}

-- Crm.Txn — the CRM transaction monad: a thin instantiation of the generic
-- store monad `Agdelte.Storage.Txn` at the CRM's (Base, CrmOp, Err, apply).
-- All combinators (returnT / _>>=T_ / _>>T_ / getBase / abort / emit / require /
-- requireJust / guardT / forEachT / runTxn) come from there, re-exported here so
-- domain commands (Crm.Commands) and the API (Crm.Api) import them from Crm.Txn.
module Crm.Txn where

open import Crm.Store using (Base; CrmOp; Err; apply)

open import Agdelte.Storage.Txn Base CrmOp Err apply public
