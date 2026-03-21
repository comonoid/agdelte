{-# OPTIONS --without-K #-}

-- Interned string pool: deduplicate repeated strings.
-- Strings are stored once in a Vector; references are ℕ indices.
-- Server-only (GHC backend).

module Agdelte.Storage.StringPool where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe)
open import Data.List using (List)
open import Data.Product using (_×_)

------------------------------------------------------------------------
-- String ID (index into pool)
------------------------------------------------------------------------

StringId = Nat

------------------------------------------------------------------------
-- Pool type (opaque, backed by Haskell)
------------------------------------------------------------------------

postulate
  StringPool : Set

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

postulate
  emptyPool : StringPool
  intern    : String → StringPool → StringId × StringPool
  resolve   : StringId → StringPool → Maybe String
  delete    : StringId → StringPool → StringPool
  poolSize  : StringPool → Nat

------------------------------------------------------------------------
-- GHC compilation
------------------------------------------------------------------------

{-# FOREIGN GHC
  import qualified Data.Vector as V
  import qualified Data.HashMap.Strict as HM
  import qualified Data.Text as T

  data AgdaStringPool = AgdaStringPool
    { spStrings :: !(V.Vector (Maybe T.Text))
    , spReverse :: !(HM.HashMap T.Text Integer)
    , spNextIdx :: !Integer
    }

  emptyPoolImpl :: AgdaStringPool
  emptyPoolImpl = AgdaStringPool V.empty HM.empty 0

  internImpl :: T.Text -> AgdaStringPool -> (Integer, AgdaStringPool)
  internImpl s pool =
    case HM.lookup s (spReverse pool) of
      Just idx -> (idx, pool)
      Nothing  ->
        let idx = spNextIdx pool
            strings' = V.snoc (spStrings pool) (Just s)
            reverse' = HM.insert s idx (spReverse pool)
        in (idx, AgdaStringPool strings' reverse' (idx + 1))

  resolveImpl :: Integer -> AgdaStringPool -> Maybe T.Text
  resolveImpl idx pool
    | idx >= 0 && idx < fromIntegral (V.length (spStrings pool)) =
        (spStrings pool) V.! fromIntegral idx
    | otherwise = Nothing

  deleteImpl :: Integer -> AgdaStringPool -> AgdaStringPool
  deleteImpl idx pool
    | idx >= 0 && idx < fromIntegral (V.length (spStrings pool)) =
        case (spStrings pool) V.! fromIntegral idx of
          Nothing -> pool
          Just s  ->
            let strings' = (spStrings pool) V.// [(fromIntegral idx, Nothing)]
                reverse' = HM.delete s (spReverse pool)
            in pool { spStrings = strings', spReverse = reverse' }
    | otherwise = pool

  poolSizeImpl :: AgdaStringPool -> Integer
  poolSizeImpl = fromIntegral . HM.size . spReverse
  #-}

{-# COMPILE GHC StringPool = type AgdaStringPool #-}

{-# COMPILE GHC emptyPool = emptyPoolImpl #-}
{-# COMPILE GHC intern    = internImpl    #-}
{-# COMPILE GHC resolve   = resolveImpl   #-}
{-# COMPILE GHC delete    = deleteImpl    #-}
{-# COMPILE GHC poolSize  = poolSizeImpl  #-}
