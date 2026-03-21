{-# OPTIONS --without-K #-}

-- Minimal JSON helpers: field extraction and string escaping.
-- Shared by Auth.Handler, Auth.Guard, and any other server modules.

module Agdelte.FFI.Json where

open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)

------------------------------------------------------------------------
-- Field extraction (string values, no nesting)
------------------------------------------------------------------------

postulate
  jsonGetField : String → String → Maybe String
  jsonGetNat   : String → String → Maybe ℕ

{-# FOREIGN GHC
  import qualified Data.Text as T
  import Text.Read (readMaybe)

  -- Minimal JSON field extractor (string values only, no nesting)
  jsonGetFieldImpl :: T.Text -> T.Text -> Maybe T.Text
  jsonGetFieldImpl fieldName json =
    let needle = "\"" <> fieldName <> "\""
    in case T.breakOn needle json of
         (_, rest)
           | T.null rest -> Nothing
           | otherwise ->
             let afterKey = T.drop (T.length needle) rest
                 afterColon = T.dropWhile (\c -> c == ':' || c == ' ') afterKey
             in if T.null afterColon || T.head afterColon /= '"'
                then Nothing
                else let valStart = T.tail afterColon
                         val = T.takeWhile (/= '"') valStart
                     in Just val

  jsonGetNatImpl :: T.Text -> T.Text -> Maybe Integer
  jsonGetNatImpl fieldName json =
    let needle = "\"" <> fieldName <> "\""
    in case T.breakOn needle json of
         (_, rest)
           | T.null rest -> Nothing
           | otherwise ->
             let afterKey = T.drop (T.length needle) rest
                 afterColon = T.dropWhile (\c -> c == ':' || c == ' ') afterKey
                 numText = T.takeWhile (\c -> c >= '0' && c <= '9') afterColon
             in if T.null numText
                then Nothing
                else readMaybe (T.unpack numText)
  #-}

{-# COMPILE GHC jsonGetField = jsonGetFieldImpl #-}
{-# COMPILE GHC jsonGetNat   = jsonGetNatImpl   #-}

------------------------------------------------------------------------
-- JSON string escaping
------------------------------------------------------------------------

postulate
  escapeJsonString : String → String

{-# FOREIGN GHC
  escapeJsonStringImpl :: T.Text -> T.Text
  escapeJsonStringImpl = T.concatMap escChar
    where
      escChar '"'  = "\\\""
      escChar '\\' = "\\\\"
      escChar '\n' = "\\n"
      escChar '\r' = "\\r"
      escChar '\t' = "\\t"
      escChar c    = T.singleton c
  #-}
{-# COMPILE GHC escapeJsonString = escapeJsonStringImpl #-}
