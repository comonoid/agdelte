{-# OPTIONS --without-K --guardedness #-}

-- Application state and operations for the video course platform.
-- Defines AppState, AppOp, serialization, and WAL config.

module Agdelte.Storage.AppStore where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.String using (_++_; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (yes; no)

open import Agdelte.Storage.WAL using (WalConfig; mkWalConfig; WalHandle; walOpen; walStep; walRead)

------------------------------------------------------------------------
-- Domain records
------------------------------------------------------------------------

record UserRecord : Set where
  constructor mkUserRecord
  field
    urId       : String
    urEmail    : String
    urPassHash : String

open UserRecord public

record CourseRecord : Set where
  constructor mkCourseRecord
  field
    crId          : String
    crTitle       : String
    crDescription : String
    crPrice       : String    -- price as string (avoid Float issues)

open CourseRecord public

record PurchaseRecord : Set where
  constructor mkPurchaseRecord
  field
    prUserId   : String
    prCourseId : String

open PurchaseRecord public

record ProgressRecord : Set where
  constructor mkProgressRecord
  field
    pgUserId   : String
    pgLessonId : String
    pgPosition : String      -- seconds as string
    pgCompleted : Bool

open ProgressRecord public

------------------------------------------------------------------------
-- Application state (in-memory)
------------------------------------------------------------------------

record AppState : Set where
  constructor mkAppState
  field
    asUsers     : List UserRecord
    asCourses   : List CourseRecord
    asPurchases : List PurchaseRecord
    asProgress  : List ProgressRecord

open AppState public

emptyAppState : AppState
emptyAppState = mkAppState [] [] [] []

------------------------------------------------------------------------
-- Operations (WAL log entries)
------------------------------------------------------------------------

data AppOp : Set where
  AddUser       : UserRecord → AppOp
  AddCourse     : CourseRecord → AppOp
  AddPurchase   : PurchaseRecord → AppOp
  SetProgress   : ProgressRecord → AppOp

------------------------------------------------------------------------
-- Apply operation to state
------------------------------------------------------------------------

private
  -- Replace or add progress entry (upsert by userId + lessonId)
  upsertProgress : ProgressRecord → List ProgressRecord → List ProgressRecord
  upsertProgress p [] = p ∷ []
  upsertProgress p (old ∷ rest) with pgUserId p ≟ pgUserId old
  ... | no _  = old ∷ upsertProgress p rest
  ... | yes _ with pgLessonId p ≟ pgLessonId old
  ...   | yes _ = p ∷ rest      -- replace
  ...   | no _  = old ∷ upsertProgress p rest

applyOp : AppOp → AppState → AppState
applyOp (AddUser u) s      = record s { asUsers = u ∷ asUsers s }
applyOp (AddCourse c) s    = record s { asCourses = c ∷ asCourses s }
applyOp (AddPurchase p) s  = record s { asPurchases = p ∷ asPurchases s }
applyOp (SetProgress p) s  = record s { asProgress = upsertProgress p (asProgress s) }

------------------------------------------------------------------------
-- Serialization (one JSON line per operation)
------------------------------------------------------------------------

-- Minimal JSON serialization for WAL. Not using full Json module
-- to keep server-side code free of JS-only postulates.
postulate
  serializeOp   : AppOp → String
  deserializeOp : String → Maybe AppOp
  serializeState   : AppState → String
  deserializeState : String → AppState

{-# FOREIGN GHC
  import qualified Data.Text as T

  -- Placeholder: real implementation uses aeson
  -- For now, use a simple delimited format:
  --   ADD_USER|id|email|hash
  --   ADD_COURSE|id|title|desc|price
  --   ADD_PURCHASE|userId|courseId
  --   SET_PROGRESS|userId|lessonId|position|completed

  -- These will be replaced with proper aeson-based JSON serialization
  -- when the hs/Agdelte/Store.hs module is implemented.
  #-}

-- TODO: COMPILE GHC pragmas for serialization.
-- For now these are postulates without compilation — the module
-- type-checks but needs hs/Agdelte/Store.hs for runtime.

------------------------------------------------------------------------
-- WAL config for the app
------------------------------------------------------------------------

appWalConfig : String → String → WalConfig AppState AppOp
appWalConfig logPath snapPath = mkWalConfig
  logPath snapPath
  applyOp serializeOp deserializeOp
  serializeState deserializeState
  emptyAppState

------------------------------------------------------------------------
-- Queries (pure, over in-memory state)
------------------------------------------------------------------------

-- Queries operate on lists, not AppState (avoids termination issues)

private
  findInList : {A : Set} → (A → Bool) → List A → Maybe A
  findInList _ [] = nothing
  findInList p (x ∷ xs) with p x
  ... | true  = just x
  ... | false = findInList p xs

  anyInList : {A : Set} → (A → Bool) → List A → Bool
  anyInList _ [] = false
  anyInList p (x ∷ xs) with p x
  ... | true  = true
  ... | false = anyInList p xs

  open import Data.Bool using (_∧_)
  eqS : String → String → Bool
  eqS a b with a ≟ b
  ... | yes _ = true
  ... | no _  = false

findUserByEmail : String → AppState → Maybe UserRecord
findUserByEmail email s = findInList (λ u → eqS email (urEmail u)) (asUsers s)

findUserById : String → AppState → Maybe UserRecord
findUserById uid s = findInList (λ u → eqS uid (urId u)) (asUsers s)

userHasCourse : String → String → AppState → Bool
userHasCourse uid cid s = anyInList (λ p → eqS uid (prUserId p) ∧ eqS cid (prCourseId p)) (asPurchases s)

getProgress : String → String → AppState → Maybe ProgressRecord
getProgress uid lid s = findInList (λ p → eqS uid (pgUserId p) ∧ eqS lid (pgLessonId p)) (asProgress s)
