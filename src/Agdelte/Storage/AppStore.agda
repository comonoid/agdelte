{-# OPTIONS --without-K --guardedness #-}

-- Application state and operations for the video course platform.
-- Defines AppState, AppOp, serialization, and WAL config.
-- Uses numeric IDs (ℕ) and NatMap for O(log n) lookups.

module Agdelte.Storage.AppStore where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Bool using (if_then_else_)
open import Data.String using (_++_; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Auth.Role using (Role; Student)
open import Agdelte.Storage.NatMap as NM using (NatMap)
open import Agdelte.Storage.WAL using (WalConfig; mkWalConfig; WalHandle; walOpen; walStep; walRead; splitLines)

------------------------------------------------------------------------
-- ID types (all ℕ)
------------------------------------------------------------------------

UserId         = ℕ
CourseId        = ℕ
LessonId        = ℕ
PlanId          = ℕ
SubscriptionId  = ℕ
PurchaseId      = ℕ

------------------------------------------------------------------------
-- Domain records
------------------------------------------------------------------------

record UserRecord : Set where
  constructor mkUserRecord
  field
    urId       : UserId
    urEmail    : String
    urPassHash : String
    urRole     : Role

open UserRecord public

record CourseRecord : Set where
  constructor mkCourseRecord
  field
    crId          : CourseId
    crAuthorId    : UserId
    crTitle       : String
    crDescription : String
    crPrice       : ℕ           -- price in kopecks
    crCategory    : String
    crLevel       : String      -- "beginner" | "intermediate" | "advanced"
    crTags        : List String

open CourseRecord public

------------------------------------------------------------------------
-- Subscription plans
------------------------------------------------------------------------

record PlanRecord : Set where
  constructor mkPlanRecord
  field
    plId     : PlanId
    plName   : String         -- "Базовый", "Про"
    plPrice  : ℕ              -- kopecks per period
    plDays   : ℕ              -- period length: 30 (month), 365 (year)

open PlanRecord public

------------------------------------------------------------------------
-- Subscription status
------------------------------------------------------------------------

data SubStatus : Set where
  SubPending   : SubStatus    -- payment initiated, awaiting confirmation
  SubActive    : SubStatus
  SubCancelled : SubStatus    -- user cancelled, active until endDate
  SubExpired   : SubStatus

record SubscriptionRecord : Set where
  constructor mkSubscriptionRecord
  field
    sbId        : SubscriptionId
    sbUserId    : UserId
    sbPlanId    : PlanId
    sbStatus    : SubStatus
    sbStartDate : ℕ           -- unix timestamp
    sbEndDate   : ℕ           -- unix timestamp
    sbAutoRenew : Bool
    sbPaymentId : String      -- ЮKassa payment ID

open SubscriptionRecord public

------------------------------------------------------------------------
-- Purchase status & record (individual course purchase)
------------------------------------------------------------------------

data PurchaseStatus : Set where
  PurchPending  : PurchaseStatus
  PurchPaid     : PurchaseStatus
  PurchRefunded : PurchaseStatus

record PurchaseRecord : Set where
  constructor mkPurchaseRecord
  field
    prId        : PurchaseId
    prUserId    : UserId
    prCourseId  : CourseId
    prAmount    : ℕ            -- kopecks
    prDate      : ℕ            -- unix timestamp
    prPaymentId : String       -- ЮKassa payment ID
    prStatus    : PurchaseStatus

open PurchaseRecord public

record ProgressRecord : Set where
  constructor mkProgressRecord
  field
    pgUserId      : UserId
    pgLessonId    : LessonId
    pgPosition    : ℕ           -- seconds
    pgCompleted   : Bool
    pgLastWatched : ℕ           -- unix timestamp

open ProgressRecord public

ReviewId  = ℕ
CommentId = ℕ

record ReviewRecord : Set where
  constructor mkReviewRecord
  field
    rvId       : ReviewId
    rvUserId   : UserId
    rvCourseId : CourseId
    rvRating   : ℕ             -- 1–5
    rvText     : String
    rvDate     : ℕ             -- unix timestamp

open ReviewRecord public

record CommentRecord : Set where
  constructor mkCommentRecord
  field
    cmId       : CommentId
    cmUserId   : UserId
    cmLessonId : LessonId
    cmText     : String
    cmDate     : ℕ             -- unix timestamp
    cmParentId : Maybe CommentId  -- nothing = top-level

open CommentRecord public

------------------------------------------------------------------------
-- Application state (in-memory)
------------------------------------------------------------------------

record AppState : Set where
  constructor mkAppState
  field
    asUsers           : NatMap UserRecord
    asCourses         : NatMap CourseRecord
    asPlans           : NatMap PlanRecord
    asSubscriptions   : NatMap SubscriptionRecord
    asPurchases       : NatMap PurchaseRecord
    asProgress        : List ProgressRecord
    asReviews         : NatMap ReviewRecord
    asComments        : NatMap CommentRecord
    asNextUserId      : ℕ
    asNextCourseId    : ℕ
    asNextPlanId      : ℕ
    asNextSubId       : ℕ
    asNextPurchaseId  : ℕ
    asNextReviewId    : ℕ
    asNextCommentId   : ℕ

open AppState public

emptyAppState : AppState
emptyAppState = mkAppState
  NM.empty NM.empty NM.empty NM.empty NM.empty
  [] NM.empty NM.empty
  0 0 0 0 0 0 0

------------------------------------------------------------------------
-- Operations (WAL log entries)
------------------------------------------------------------------------

data AppOp : Set where
  AddUser          : UserRecord → AppOp
  AddCourse        : CourseRecord → AppOp
  AddPlan          : PlanRecord → AppOp
  AddSubscription  : SubscriptionRecord → AppOp
  UpdateSubStatus  : SubscriptionId → SubStatus → AppOp
  AddPurchase      : PurchaseRecord → AppOp
  UpdatePurchStatus : PurchaseId → PurchaseStatus → AppOp
  SetProgress      : ProgressRecord → AppOp
  AddReview        : ReviewRecord → AppOp
  AddComment       : CommentRecord → AppOp
  DeleteComment    : CommentId → AppOp
  ExpirePendingSubs : ℕ → AppOp       -- expire SubPending older than N seconds (pass currentTime)

------------------------------------------------------------------------
-- Apply operation to state
------------------------------------------------------------------------

private
  -- Replace or add progress entry (upsert by userId + lessonId)
  upsertProgress : ProgressRecord → List ProgressRecord → List ProgressRecord
  upsertProgress p [] = p ∷ []
  upsertProgress p (old ∷ rest) with pgUserId p ≡ᵇ pgUserId old
    where open Data.Nat using (_≡ᵇ_)
  ... | false = old ∷ upsertProgress p rest
  ... | true with pgLessonId p ≡ᵇ pgLessonId old
    where open Data.Nat using (_≡ᵇ_)
  ...   | true  = p ∷ rest      -- replace
  ...   | false = old ∷ upsertProgress p rest

  -- Update a field in a NatMap record by ID.
  updateSub : SubscriptionId → SubStatus → NatMap SubscriptionRecord → NatMap SubscriptionRecord
  updateSub sid st subs with NM.lookup sid subs
  ... | nothing  = subs
  ... | just sub = NM.insert sid (record sub { sbStatus = st }) subs

  updatePurch : PurchaseId → PurchaseStatus → NatMap PurchaseRecord → NatMap PurchaseRecord
  updatePurch pid st ps with NM.lookup pid ps
  ... | nothing = ps
  ... | just p  = NM.insert pid (record p { prStatus = st }) ps

applyOp : AppOp → AppState → AppState
applyOp (AddUser u) s =
  record s { asUsers = NM.insert (urId u) u (asUsers s)
           ; asNextUserId = suc (urId u) ⊔ asNextUserId s
           }
applyOp (AddCourse c) s =
  record s { asCourses = NM.insert (crId c) c (asCourses s)
           ; asNextCourseId = suc (crId c) ⊔ asNextCourseId s
           }
applyOp (AddPlan p) s =
  record s { asPlans = NM.insert (plId p) p (asPlans s)
           ; asNextPlanId = suc (plId p) ⊔ asNextPlanId s
           }
applyOp (AddSubscription sub) s =
  record s { asSubscriptions = NM.insert (sbId sub) sub (asSubscriptions s)
           ; asNextSubId = suc (sbId sub) ⊔ asNextSubId s
           }
applyOp (UpdateSubStatus sid st) s =
  record s { asSubscriptions = updateSub sid st (asSubscriptions s) }
applyOp (AddPurchase p) s =
  record s { asPurchases = NM.insert (prId p) p (asPurchases s)
           ; asNextPurchaseId = suc (prId p) ⊔ asNextPurchaseId s
           }
applyOp (UpdatePurchStatus pid st) s =
  record s { asPurchases = updatePurch pid st (asPurchases s) }
applyOp (SetProgress p) s =
  record s { asProgress = upsertProgress p (asProgress s) }
applyOp (AddReview r) s =
  record s { asReviews = NM.insert (rvId r) r (asReviews s)
           ; asNextReviewId = suc (rvId r) ⊔ asNextReviewId s
           }
applyOp (AddComment c) s =
  record s { asComments = NM.insert (cmId c) c (asComments s)
           ; asNextCommentId = suc (cmId c) ⊔ asNextCommentId s
           }
applyOp (DeleteComment cid) s =
  record s { asComments = NM.foldl rmChild (NM.delete cid cms) cms }
  where
    open Data.Nat using (_≡ᵇ_)
    cms = asComments s
    rmChild : NatMap CommentRecord → ℕ → CommentRecord → NatMap CommentRecord
    rmChild acc k c with cmParentId c
    ... | nothing  = acc
    ... | just pid = if pid ≡ᵇ cid then NM.delete k acc else acc
applyOp (ExpirePendingSubs now) s =
  record s { asSubscriptions = expirePending now (asSubscriptions s) }
  where
    -- 30 minutes timeout for pending subscriptions
    pendingTimeout : ℕ
    pendingTimeout = 1800

    expirePending : ℕ → NatMap SubscriptionRecord → NatMap SubscriptionRecord
    expirePending now subs = NM.foldl go subs subs
      where
        open Data.Nat using (_+_; _<ᵇ_)
        go : NatMap SubscriptionRecord → ℕ → SubscriptionRecord → NatMap SubscriptionRecord
        go acc _ sub with sbStatus sub
        ... | SubPending = if (sbStartDate sub + pendingTimeout) <ᵇ now
                           then NM.insert (sbId sub) (record sub { sbStatus = SubExpired }) acc
                           else acc
        ... | _ = acc

------------------------------------------------------------------------
-- Serialization (pipe-delimited, one line per operation)
------------------------------------------------------------------------

-- Format: TAG|field1|field2|...|fieldN
-- Free-text fields are escaped: \ → \\, | → \p, newline → \n, , → \c
-- List String fields: comma-separated escaped values.
-- State snapshots: all records as Add ops, replayed on restore.

private
  postulate
    readNat       : String → Maybe ℕ
    splitPipe     : String → List String
    escapeField   : String → String
    unescapeField : String → String
    joinComma     : List String → String
    splitComma    : String → List String

{-# FOREIGN GHC
  import qualified Data.Text as T
  import qualified Data.Text.Read as TR

  readNatHS :: T.Text -> Maybe Integer
  readNatHS t = case TR.decimal t of
    Right (n, rest) | T.null rest, n >= (0 :: Integer) -> Just n
    _ -> Nothing

  splitPipeHS :: T.Text -> [T.Text]
  splitPipeHS = T.splitOn (T.singleton '|')

  escapeFieldHS :: T.Text -> T.Text
  escapeFieldHS = T.concatMap $ \c -> case c of
    '\\' -> T.pack "\\\\"
    '|'  -> T.pack "\\p"
    '\n' -> T.pack "\\n"
    ','  -> T.pack "\\c"
    _    -> T.singleton c

  unescapeFieldHS :: T.Text -> T.Text
  unescapeFieldHS t = case T.uncons t of
    Nothing -> T.empty
    Just ('\\', rest) -> case T.uncons rest of
      Just ('\\', r) -> T.cons '\\' (unescapeFieldHS r)
      Just ('p', r)  -> T.cons '|' (unescapeFieldHS r)
      Just ('n', r)  -> T.cons '\n' (unescapeFieldHS r)
      Just ('c', r)  -> T.cons ',' (unescapeFieldHS r)
      Just (c, r)    -> T.cons '\\' (T.cons c (unescapeFieldHS r))
      Nothing        -> T.singleton '\\'
    Just (c, rest) -> T.cons c (unescapeFieldHS rest)

  joinCommaHS :: [T.Text] -> T.Text
  joinCommaHS = T.intercalate (T.singleton ',')

  splitCommaHS :: T.Text -> [T.Text]
  splitCommaHS t | T.null t  = []
                 | otherwise = T.splitOn (T.singleton ',') t
  #-}

{-# COMPILE GHC readNat       = readNatHS #-}
{-# COMPILE GHC splitPipe     = splitPipeHS #-}
{-# COMPILE GHC escapeField   = escapeFieldHS #-}
{-# COMPILE GHC unescapeField = unescapeFieldHS #-}
{-# COMPILE GHC joinComma     = joinCommaHS #-}
{-# COMPILE GHC splitComma    = splitCommaHS #-}

private
  open import Data.Nat.Show using () renaming (show to showℕ)
  open import Data.List using (map) renaming (_++_ to _++L_)
  open import Data.Bool using (if_then_else_)
  open import Agdelte.Auth.Role using (showRole; parseRole)

  esc : String → String
  esc = escapeField

  unesc : String → String
  unesc = unescapeField

  infixl 1 _>>=ₘ_
  _>>=ₘ_ : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  nothing >>=ₘ _ = nothing
  just a  >>=ₘ f = f a

  infixr 5 _∣_
  _∣_ : String → String → String
  a ∣ b = a ++ "|" ++ b

  showBool : Bool → String
  showBool true  = "1"
  showBool false = "0"

  parseBool : String → Maybe Bool
  parseBool s with s ≟ "1"
  ... | yes _ = just true
  ... | no _ with s ≟ "0"
  ...   | yes _ = just false
  ...   | no _  = nothing

  showSubStatus : SubStatus → String
  showSubStatus SubPending   = "pending"
  showSubStatus SubActive    = "active"
  showSubStatus SubCancelled = "cancelled"
  showSubStatus SubExpired   = "expired"

  parseSubStatus : String → Maybe SubStatus
  parseSubStatus s with s ≟ "pending"
  ... | yes _ = just SubPending
  ... | no _ with s ≟ "active"
  ...   | yes _ = just SubActive
  ...   | no _ with s ≟ "cancelled"
  ...     | yes _ = just SubCancelled
  ...     | no _ with s ≟ "expired"
  ...       | yes _ = just SubExpired
  ...       | no _  = nothing

  showPurchStatus : PurchaseStatus → String
  showPurchStatus PurchPending  = "pending"
  showPurchStatus PurchPaid     = "paid"
  showPurchStatus PurchRefunded = "refunded"

  parsePurchStatus : String → Maybe PurchaseStatus
  parsePurchStatus s with s ≟ "pending"
  ... | yes _ = just PurchPending
  ... | no _ with s ≟ "paid"
  ...   | yes _ = just PurchPaid
  ...   | no _ with s ≟ "refunded"
  ...     | yes _ = just PurchRefunded
  ...     | no _  = nothing

  showMaybeNat : Maybe ℕ → String
  showMaybeNat nothing  = "none"
  showMaybeNat (just n) = showℕ n

  parseMaybeNat : String → Maybe (Maybe ℕ)
  parseMaybeNat s with s ≟ "none"
  ... | yes _ = just nothing
  ... | no _  with readNat s
  ...   | nothing = nothing
  ...   | just n  = just (just n)

  _≡ˢ_ : String → String → Bool
  s₁ ≡ˢ s₂ with s₁ ≟ s₂
  ... | yes _ = true
  ... | no _  = false

serializeOp : AppOp → String
serializeOp (AddUser u) =
  "ADD_USER" ∣ showℕ (urId u) ∣ esc (urEmail u) ∣ esc (urPassHash u) ∣ showRole (urRole u)
serializeOp (AddCourse c) =
  "ADD_COURSE" ∣ showℕ (crId c) ∣ showℕ (crAuthorId c) ∣ esc (crTitle c)
  ∣ esc (crDescription c) ∣ showℕ (crPrice c) ∣ esc (crCategory c) ∣ esc (crLevel c)
  ∣ joinComma (map esc (crTags c))
serializeOp (AddPlan p) =
  "ADD_PLAN" ∣ showℕ (plId p) ∣ esc (plName p) ∣ showℕ (plPrice p) ∣ showℕ (plDays p)
serializeOp (AddSubscription sub) =
  "ADD_SUB" ∣ showℕ (sbId sub) ∣ showℕ (sbUserId sub) ∣ showℕ (sbPlanId sub)
  ∣ showSubStatus (sbStatus sub) ∣ showℕ (sbStartDate sub) ∣ showℕ (sbEndDate sub)
  ∣ showBool (sbAutoRenew sub) ∣ esc (sbPaymentId sub)
serializeOp (UpdateSubStatus sid st) =
  "UPD_SUB" ∣ showℕ sid ∣ showSubStatus st
serializeOp (AddPurchase p) =
  "ADD_PURCH" ∣ showℕ (prId p) ∣ showℕ (prUserId p) ∣ showℕ (prCourseId p)
  ∣ showℕ (prAmount p) ∣ showℕ (prDate p) ∣ esc (prPaymentId p) ∣ showPurchStatus (prStatus p)
serializeOp (UpdatePurchStatus pid st) =
  "UPD_PURCH" ∣ showℕ pid ∣ showPurchStatus st
serializeOp (SetProgress p) =
  "SET_PROG" ∣ showℕ (pgUserId p) ∣ showℕ (pgLessonId p) ∣ showℕ (pgPosition p)
  ∣ showBool (pgCompleted p) ∣ showℕ (pgLastWatched p)
serializeOp (AddReview r) =
  "ADD_REVIEW" ∣ showℕ (rvId r) ∣ showℕ (rvUserId r) ∣ showℕ (rvCourseId r)
  ∣ showℕ (rvRating r) ∣ esc (rvText r) ∣ showℕ (rvDate r)
serializeOp (AddComment c) =
  "ADD_COMMENT" ∣ showℕ (cmId c) ∣ showℕ (cmUserId c) ∣ showℕ (cmLessonId c)
  ∣ esc (cmText c) ∣ showℕ (cmDate c) ∣ showMaybeNat (cmParentId c)
serializeOp (DeleteComment cid) =
  "DEL_COMMENT" ∣ showℕ cid
serializeOp (ExpirePendingSubs now) =
  "EXPIRE_PENDING" ∣ showℕ now

deserializeOp : String → Maybe AppOp
deserializeOp line = dispatch (splitPipe line)
  where
    parseAddUser : List String → Maybe AppOp
    parseAddUser (idS ∷ emailS ∷ hashS ∷ roleS ∷ []) =
      readNat idS >>=ₘ λ i →
      parseRole roleS >>=ₘ λ r →
      just (AddUser (mkUserRecord i (unesc emailS) (unesc hashS) r))
    parseAddUser _ = nothing

    parseAddCourse : List String → Maybe AppOp
    parseAddCourse (idS ∷ authS ∷ titleS ∷ descS ∷ priceS ∷ catS ∷ lvlS ∷ tagsS ∷ []) =
      readNat idS >>=ₘ λ i →
      readNat authS >>=ₘ λ a →
      readNat priceS >>=ₘ λ p →
      just (AddCourse (mkCourseRecord i a (unesc titleS) (unesc descS) p
                         (unesc catS) (unesc lvlS) (map unesc (splitComma tagsS))))
    parseAddCourse _ = nothing

    parseAddPlan : List String → Maybe AppOp
    parseAddPlan (idS ∷ nameS ∷ priceS ∷ daysS ∷ []) =
      readNat idS >>=ₘ λ i →
      readNat priceS >>=ₘ λ p →
      readNat daysS >>=ₘ λ d →
      just (AddPlan (mkPlanRecord i (unesc nameS) p d))
    parseAddPlan _ = nothing

    parseAddSub : List String → Maybe AppOp
    parseAddSub (idS ∷ uidS ∷ pidS ∷ stS ∷ startS ∷ endS ∷ arS ∷ payS ∷ []) =
      readNat idS >>=ₘ λ i →
      readNat uidS >>=ₘ λ u →
      readNat pidS >>=ₘ λ p →
      parseSubStatus stS >>=ₘ λ st →
      readNat startS >>=ₘ λ s →
      readNat endS >>=ₘ λ e →
      parseBool arS >>=ₘ λ ar →
      just (AddSubscription (mkSubscriptionRecord i u p st s e ar (unesc payS)))
    parseAddSub _ = nothing

    parseUpdSub : List String → Maybe AppOp
    parseUpdSub (sidS ∷ stS ∷ []) =
      readNat sidS >>=ₘ λ sid →
      parseSubStatus stS >>=ₘ λ st →
      just (UpdateSubStatus sid st)
    parseUpdSub _ = nothing

    parseAddPurch : List String → Maybe AppOp
    parseAddPurch (idS ∷ uidS ∷ cidS ∷ amtS ∷ dateS ∷ payS ∷ stS ∷ []) =
      readNat idS >>=ₘ λ i →
      readNat uidS >>=ₘ λ u →
      readNat cidS >>=ₘ λ c →
      readNat amtS >>=ₘ λ a →
      readNat dateS >>=ₘ λ d →
      parsePurchStatus stS >>=ₘ λ st →
      just (AddPurchase (mkPurchaseRecord i u c a d (unesc payS) st))
    parseAddPurch _ = nothing

    parseUpdPurch : List String → Maybe AppOp
    parseUpdPurch (pidS ∷ stS ∷ []) =
      readNat pidS >>=ₘ λ pid →
      parsePurchStatus stS >>=ₘ λ st →
      just (UpdatePurchStatus pid st)
    parseUpdPurch _ = nothing

    parseSetProg : List String → Maybe AppOp
    parseSetProg (uidS ∷ lidS ∷ posS ∷ compS ∷ lwS ∷ []) =
      readNat uidS >>=ₘ λ u →
      readNat lidS >>=ₘ λ l →
      readNat posS >>=ₘ λ p →
      parseBool compS >>=ₘ λ c →
      readNat lwS >>=ₘ λ lw →
      just (SetProgress (mkProgressRecord u l p c lw))
    parseSetProg _ = nothing

    parseAddReview : List String → Maybe AppOp
    parseAddReview (idS ∷ uidS ∷ cidS ∷ ratS ∷ textS ∷ dateS ∷ []) =
      readNat idS >>=ₘ λ i →
      readNat uidS >>=ₘ λ u →
      readNat cidS >>=ₘ λ c →
      readNat ratS >>=ₘ λ r →
      readNat dateS >>=ₘ λ d →
      just (AddReview (mkReviewRecord i u c r (unesc textS) d))
    parseAddReview _ = nothing

    parseAddComment : List String → Maybe AppOp
    parseAddComment (idS ∷ uidS ∷ lidS ∷ textS ∷ dateS ∷ parentS ∷ []) =
      readNat idS >>=ₘ λ i →
      readNat uidS >>=ₘ λ u →
      readNat lidS >>=ₘ λ l →
      readNat dateS >>=ₘ λ d →
      parseMaybeNat parentS >>=ₘ λ p →
      just (AddComment (mkCommentRecord i u l (unesc textS) d p))
    parseAddComment _ = nothing

    parseDelComment : List String → Maybe AppOp
    parseDelComment (cidS ∷ []) =
      readNat cidS >>=ₘ λ c →
      just (DeleteComment c)
    parseDelComment _ = nothing

    parseExpirePending : List String → Maybe AppOp
    parseExpirePending (nowS ∷ []) =
      readNat nowS >>=ₘ λ now →
      just (ExpirePendingSubs now)
    parseExpirePending _ = nothing

    dispatch : List String → Maybe AppOp
    dispatch (tag ∷ rest) =
      if tag ≡ˢ "ADD_USER"          then parseAddUser rest
      else if tag ≡ˢ "ADD_COURSE"   then parseAddCourse rest
      else if tag ≡ˢ "ADD_PLAN"     then parseAddPlan rest
      else if tag ≡ˢ "ADD_SUB"      then parseAddSub rest
      else if tag ≡ˢ "UPD_SUB"      then parseUpdSub rest
      else if tag ≡ˢ "ADD_PURCH"    then parseAddPurch rest
      else if tag ≡ˢ "UPD_PURCH"    then parseUpdPurch rest
      else if tag ≡ˢ "SET_PROG"     then parseSetProg rest
      else if tag ≡ˢ "ADD_REVIEW"   then parseAddReview rest
      else if tag ≡ˢ "ADD_COMMENT"  then parseAddComment rest
      else if tag ≡ˢ "DEL_COMMENT"  then parseDelComment rest
      else if tag ≡ˢ "EXPIRE_PENDING" then parseExpirePending rest
      else nothing
    dispatch _ = nothing

serializeState : AppState → String
serializeState s = unlines allOps
  where
    unlines : List String → String
    unlines []       = ""
    unlines (x ∷ []) = x
    unlines (x ∷ xs) = x ++ "\n" ++ unlines xs

    allOps : List String
    allOps =
      map (λ u → serializeOp (AddUser u)) (NM.values (asUsers s))
      ++L map (λ c → serializeOp (AddCourse c)) (NM.values (asCourses s))
      ++L map (λ p → serializeOp (AddPlan p)) (NM.values (asPlans s))
      ++L map (λ sub → serializeOp (AddSubscription sub)) (NM.values (asSubscriptions s))
      ++L map (λ p → serializeOp (AddPurchase p)) (NM.values (asPurchases s))
      ++L map (λ p → serializeOp (SetProgress p)) (asProgress s)
      ++L map (λ r → serializeOp (AddReview r)) (NM.values (asReviews s))
      ++L map (λ c → serializeOp (AddComment c)) (NM.values (asComments s))

deserializeState : String → AppState
deserializeState str = replay emptyAppState (splitLines str)
  where
    replay : AppState → List String → AppState
    replay s []       = s
    replay s (l ∷ ls) with deserializeOp l
    ... | nothing = replay s ls
    ... | just op = replay (applyOp op s) ls

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

findUserById : UserId → AppState → Maybe UserRecord
findUserById uid s = NM.lookup uid (asUsers s)

findCourseById : CourseId → AppState → Maybe CourseRecord
findCourseById cid s = NM.lookup cid (asCourses s)

-- Linear scan over email (email is not a key in users map).
-- For frequent lookups, add a reverse index NatMap or StringPool later.
findUserByEmail : String → AppState → Maybe UserRecord
findUserByEmail email s = go (NM.values (asUsers s))
  where
    go : List UserRecord → Maybe UserRecord
    go [] = nothing
    go (u ∷ us) with urEmail u ≟ email
    ... | yes _ = just u
    ... | no _  = go us

open Data.Nat using (_≡ᵇ_; _<ᵇ_)
open import Data.Bool using (_∧_; _∨_)
open import Data.List.Base using (filterᵇ; any)

-- | Does user have a paid purchase for this course?
userHasCourse : UserId → CourseId → AppState → Bool
userHasCourse uid cid s = any matchPurch (NM.values (asPurchases s))
  where
    isPaid : PurchaseStatus → Bool
    isPaid PurchPaid = true
    isPaid _         = false

    matchPurch : PurchaseRecord → Bool
    matchPurch p = (prUserId p ≡ᵇ uid) ∧ (prCourseId p ≡ᵇ cid) ∧ isPaid (prStatus p)

-- | Does user have an active subscription?
-- currentTime: unix timestamp. Subscription is active if status = SubActive and endDate > currentTime.
hasActiveSubscription : UserId → ℕ → AppState → Bool
hasActiveSubscription uid now s = any matchSub (NM.values (asSubscriptions s))
  where
    isActive : SubStatus → Bool
    isActive SubPending   = false
    isActive SubActive    = true
    isActive SubCancelled = true   -- still active until endDate
    isActive SubExpired   = false

    matchSub : SubscriptionRecord → Bool
    matchSub sub = (sbUserId sub ≡ᵇ uid)
                 ∧ isActive (sbStatus sub)
                 ∧ not (sbEndDate sub <ᵇ now)
      where open Data.Bool using (not)

-- | Does user have a pending (unpaid) subscription?
hasPendingSubscription : UserId → AppState → Bool
hasPendingSubscription uid s = any matchPending (NM.values (asSubscriptions s))
  where
    matchPending : SubscriptionRecord → Bool
    matchPending sub with sbStatus sub
    ... | SubPending = sbUserId sub ≡ᵇ uid
    ... | _          = false

-- | Can user access this course? (subscription OR individual purchase)
userCanAccess : UserId → CourseId → ℕ → AppState → Bool
userCanAccess uid cid now s =
  hasActiveSubscription uid now s ∨ userHasCourse uid cid s

-- | Find user's active subscription (for display / renewal)
findUserSubscription : UserId → ℕ → AppState → Maybe SubscriptionRecord
findUserSubscription uid now s = go (NM.values (asSubscriptions s))
  where
    isActiveOrCancelled : SubStatus → Bool
    isActiveOrCancelled SubActive    = true
    isActiveOrCancelled SubCancelled = true
    isActiveOrCancelled _            = false

    go : List SubscriptionRecord → Maybe SubscriptionRecord
    go [] = nothing
    go (sub ∷ rest) with (sbUserId sub ≡ᵇ uid)
                       ∧ isActiveOrCancelled (sbStatus sub)
                       ∧ not (sbEndDate sub <ᵇ now)
      where open Data.Bool using (not)
    ... | true  = just sub
    ... | false = go rest

-- | Find purchase by ЮKassa payment ID (for webhook handling)
findPurchaseByPaymentId : String → AppState → Maybe PurchaseRecord
findPurchaseByPaymentId payId s = go (NM.values (asPurchases s))
  where
    go : List PurchaseRecord → Maybe PurchaseRecord
    go [] = nothing
    go (p ∷ ps) with prPaymentId p ≟ payId
    ... | yes _ = just p
    ... | no _  = go ps

-- | Find subscription by ЮKassa payment ID
findSubByPaymentId : String → AppState → Maybe SubscriptionRecord
findSubByPaymentId payId s = go (NM.values (asSubscriptions s))
  where
    go : List SubscriptionRecord → Maybe SubscriptionRecord
    go [] = nothing
    go (sub ∷ rest) with sbPaymentId sub ≟ payId
    ... | yes _ = just sub
    ... | no _  = go rest

-- | Find plan by ID
findPlanById : PlanId → AppState → Maybe PlanRecord
findPlanById pid s = NM.lookup pid (asPlans s)

getProgress : UserId → LessonId → AppState → Maybe ProgressRecord
getProgress uid lid s = go (asProgress s)
  where
    go : List ProgressRecord → Maybe ProgressRecord
    go [] = nothing
    go (p ∷ ps) with (pgUserId p ≡ᵇ uid) ∧ (pgLessonId p ≡ᵇ lid)
    ... | true  = just p
    ... | false = go ps

-- | Allocators
allocUserId    : AppState → UserId
allocUserId    = asNextUserId
allocCourseId  : AppState → CourseId
allocCourseId  = asNextCourseId
allocPlanId    : AppState → PlanId
allocPlanId    = asNextPlanId
allocSubId     : AppState → SubscriptionId
allocSubId     = asNextSubId
allocPurchaseId : AppState → PurchaseId
allocPurchaseId = asNextPurchaseId
allocReviewId  : AppState → ReviewId
allocReviewId  = asNextReviewId
allocCommentId : AppState → CommentId
allocCommentId = asNextCommentId

-- | Get all reviews for a course
courseReviews : CourseId → AppState → List ReviewRecord
courseReviews cid s = filterᵇ (λ r → rvCourseId r ≡ᵇ cid) (NM.values (asReviews s))

-- | Get all comments for a lesson
lessonComments : LessonId → AppState → List CommentRecord
lessonComments lid s = filterᵇ (λ c → cmLessonId c ≡ᵇ lid) (NM.values (asComments s))
