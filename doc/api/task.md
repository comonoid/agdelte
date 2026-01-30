# Task (Monadic Chains)

From `Agdelte.Core.Task`.

## Core Type

```agda
data Task (A : Set) : Set where
  pure    : A → Task A
  fail    : String → Task A
  httpGet : String → (String → Task A) → (String → Task A) → Task A
  httpPost : String → String → (String → Task A) → (String → Task A) → Task A
```

## Monad Operations

```agda
_>>=_  : Task A → (A → Task B) → Task B
_>>_   : Task A → Task B → Task B
return : A → Task A
```

## Helpers

```agda
http : String → Task String                    -- GET, fail on error
httpPost′ : String → String → Task String      -- POST, fail on error
```

## Usage with do-notation

```agda
fetchData : Task UserData
fetchData = do
  token ← http "/api/token"
  user ← http ("/api/user?token=" ++ token)
  pure (parseUser user)

-- In command:
cmd Fetch _ = attempt fetchData GotResult
```
