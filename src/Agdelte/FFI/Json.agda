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
  import Text.Printf (printf)
  import Data.Char (chr, digitToInt, isHexDigit, isDigit)
  import Data.List (isPrefixOf)

  -- A real (small) recursive-descent JSON parser, replacing the old substring
  -- scanner that truncated string values at the first '\"' (so {"name":"a\"b"}
  -- yielded "a\\") and could match a key inside a nested object or string. This
  -- one decodes escapes and only consults TOP-LEVEL keys.
  data JV = JNull | JBool Bool | JNum T.Text | JStr T.Text | JArr [JV] | JObj [(T.Text, JV)]

  jWs :: String -> String
  jWs = dropWhile (\c -> c == ' ' || c == '\t' || c == '\n' || c == '\r')

  jValue :: String -> Maybe (JV, String)
  jValue s0 = case jWs s0 of
    ('"':r) -> do (str, r') <- jString r; Just (JStr str, r')
    ('{':r) -> jObject r
    ('[':r) -> jArray r
    ('t':r) | "rue"  `isPrefixOf` r -> Just (JBool True,  drop 3 r)
    ('f':r) | "alse" `isPrefixOf` r -> Just (JBool False, drop 4 r)
    ('n':r) | "ull"  `isPrefixOf` r -> Just (JNull,       drop 3 r)
    s@(c:_) | c == '-' || isDigit c ->
      let (tok, r) = span (\x -> isDigit x || x `elem` ("+-.eE" :: String)) s
      in if null tok then Nothing else Just (JNum (T.pack tok), r)
    _ -> Nothing

  -- cursor is AFTER the opening quote; decode escapes
  jString :: String -> Maybe (T.Text, String)
  jString = go []
    where
      go acc ('"':r)      = Just (T.pack (reverse acc), r)
      go acc ('\\':e:r)   = case e of
        '"'  -> go ('"':acc) r ; '\\' -> go ('\\':acc) r ; '/' -> go ('/':acc) r
        'b'  -> go ('\b':acc) r ; 'f' -> go ('\f':acc) r ; 'n' -> go ('\n':acc) r
        'r'  -> go ('\r':acc) r ; 't' -> go ('\t':acc) r
        'u'  -> case r of
                  (a:b:c:d:r') | all isHexDigit [a,b,c,d] ->
                    go (chr (((digitToInt a*16+digitToInt b)*16+digitToInt c)*16+digitToInt d) : acc) r'
                  _ -> Nothing
        _    -> Nothing
      go _   ('\\':[])    = Nothing
      go acc (c:r)        = go (c:acc) r
      go _   []           = Nothing            -- unterminated string

  jArray :: String -> Maybe (JV, String)
  jArray s = case jWs s of
    (']':r) -> Just (JArr [], r)
    s'      -> go [] s'
    where
      go acc t = do
        (v, t1) <- jValue t
        case jWs t1 of
          (',':t2) -> go (v:acc) t2
          (']':t2) -> Just (JArr (reverse (v:acc)), t2)
          _        -> Nothing

  jObject :: String -> Maybe (JV, String)
  jObject s = case jWs s of
    ('}':r) -> Just (JObj [], r)
    s'      -> go [] s'
    where
      go acc t = case jWs t of
        ('"':t1) -> do
          (k, t2) <- jString t1
          case jWs t2 of
            (':':t3) -> do
              (v, t4) <- jValue t3
              case jWs t4 of
                (',':t5) -> go ((k, v):acc) t5
                ('}':t5) -> Just (JObj (reverse ((k, v):acc)), t5)
                _        -> Nothing
            _ -> Nothing
        _ -> Nothing

  -- parse a complete top-level JSON OBJECT (trailing whitespace allowed); reject anything else
  jTopObject :: T.Text -> Maybe [(T.Text, JV)]
  jTopObject t = case jValue (T.unpack t) of
    Just (JObj kvs, rest) | null (jWs rest) -> Just kvs
    _ -> Nothing

  jsonGetFieldImpl :: T.Text -> T.Text -> Maybe T.Text
  jsonGetFieldImpl fieldName json = do
    kvs <- jTopObject json
    v   <- lookup fieldName kvs
    case v of { JStr s -> Just s ; _ -> Nothing }    -- string-valued top-level field

  jsonGetNatImpl :: T.Text -> T.Text -> Maybe Integer
  jsonGetNatImpl fieldName json = do
    kvs <- jTopObject json
    v   <- lookup fieldName kvs
    case v of
      JNum t -> do i <- readMaybe (T.unpack t) :: Maybe Integer   -- rejects 3.5 / 1e3 (non-integer)
                   if i >= 0 then Just i else Nothing
      _      -> Nothing
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
      -- Escape ALL remaining control characters (U+0000–U+001F) as \u00XX.
      -- Leaving them raw produces invalid JSON and enables injection/smuggling
      -- when the value is interpolated into a JWT payload or response body.
      escChar c
        | c < '\x20' = T.pack (printf "\\u%04x" (fromEnum c))
        | otherwise  = T.singleton c
  #-}
{-# COMPILE GHC escapeJsonString = escapeJsonStringImpl #-}
