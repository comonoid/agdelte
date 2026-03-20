# Agdelte.Auth

JWT authentication with bcrypt passwords.
Server-side middleware validates tokens and protects endpoints; client-side helpers
manage token storage and build authenticated HTTP requests.

## Design Principles

1. **HS256 JWT** -- tokens signed with HMAC-SHA256 via `FFI.Crypto`
2. **Bcrypt passwords** -- `hashPassword` / `verifyPassword` from FFI
3. **Composable middleware** -- `withAuth` wraps any handler to require a valid token
4. **Cmd-based client** -- login, register, and token management are plain `Cmd` values

## Quick Start

```agda
-- Server: protect an endpoint
open import Agdelte.Auth.Middleware
open import Agdelte.Auth.Handler

handler : AuthRequest -> IO HttpResponse
handler authReq = ...

server = withAuth secret handler

-- Client: login and store token
open import Agdelte.Auth.Client

cmds = loginCmd "/api/login" email password GotToken GotError
     <> saveToken token
```

## JWT

Token creation and verification (HS256).

```agda
-- | Create a signed JWT. Payload should be a JSON string.
signJWT : String -> String -> String
-- signJWT secret payload

-- | Verify JWT signature. Returns decoded payload if valid.
verifyJWT : String -> String -> Maybe String
-- verifyJWT secret token

-- | Split "header.payload.signature" into parts.
splitJWT : String -> Maybe (String * String * String)
```

Tokens use the fixed header `{"alg":"HS256","typ":"JWT"}`.
The payload is an opaque JSON string -- the caller decides what claims to include.

## Middleware

Server-side token extraction and endpoint protection.

```agda
-- | Authenticated request: decoded JWT payload + original request.
record AuthRequest : Set where
  constructor mkAuthRequest
  field
    authPayload : String
    authRaw     : HttpRequest

-- | Extract "Bearer <token>" from a header value.
extractBearer : String -> Maybe String

-- | Extract and verify JWT from the Authorization header.
authenticate : String -> HttpRequest -> Maybe String
-- authenticate secret request

-- | Wrap a handler to require authentication.
-- Returns 401 if no valid token.
withAuth : String -> (AuthRequest -> IO HttpResponse) -> HttpRequest -> IO HttpResponse

-- | Standard CORS headers (Allow-Origin: *, Authorization + Content-Type).
corsHeaders : List (String * String)

-- | Handle OPTIONS preflight with CORS headers (204 No Content).
handleOptions : IO HttpResponse
```

## Handler

Server-side registration and login over an in-memory user store.

```agda
record User : Set where
  constructor mkUser
  field
    userId       : String
    userEmail    : String
    userPassHash : String

-- | Mutable list of users (IORef).
UserStore : Set
UserStore = IORef (List User)

newUserStore : IO UserStore

-- | POST /api/register
-- Body: {"email":"...","password":"..."}
-- Returns 201 {"token":"...", "userId":"..."} or 400/409 on error.
handleRegister : String -> UserStore -> HttpRequest -> IO HttpResponse

-- | POST /api/login
-- Body: {"email":"...","password":"..."}
-- Returns 200 {"token":"...", "userId":"..."} or 400/401 on error.
handleLogin : String -> UserStore -> HttpRequest -> IO HttpResponse
```

Both handlers include `corsHeaders` on every response.
Passwords are hashed with bcrypt before storage; login verifies with `verifyPassword`.

## Client

Browser-side token management and authenticated requests via `Cmd`.

```agda
-- Token storage (localStorage, key "agdelte-auth-token")
saveToken  : String -> Cmd A
clearToken : Cmd A
loadToken  : (Maybe String -> A) -> Cmd A

-- Header construction
authHeaders     : String -> List (String * String)   -- Authorization: Bearer ...
authJsonHeaders : String -> List (String * String)   -- + Content-Type: application/json

-- Authenticated HTTP requests
authGet  : String -> String -> (String -> A) -> (String -> A) -> Cmd A
-- authGet url token onOk onErr

authPost : String -> String -> String -> (String -> A) -> (String -> A) -> Cmd A
-- authPost url token body onOk onErr

-- Unauthenticated login/register (POST with JSON body)
loginCmd    : String -> String -> String -> (String -> A) -> (String -> A) -> Cmd A
-- loginCmd url email password onOk onErr

registerCmd : String -> String -> String -> (String -> A) -> (String -> A) -> Cmd A
-- same body format as loginCmd
```

## Usage Example

### Server side

```agda
open import Agdelte.Auth.Handler
open import Agdelte.Auth.Middleware

secret = "my-secret-key"

main : IO Unit
main = do
  store <- newUserStore
  startServer 8080 $ \req ->
    case reqMethod req , reqPath req of
      "OPTIONS" , _              -> handleOptions
      "POST"    , "/api/register" -> handleRegister secret store req
      "POST"    , "/api/login"    -> handleLogin secret store req
      "GET"     , "/api/profile"  -> withAuth secret profileHandler req
      _         , _              -> pure (mkResponse 404 "Not found")
```

### Client side

```agda
open import Agdelte.Auth.Client
open import Agdelte.Core.Cmd

data Msg : Set where
  LoginResult  : String -> Msg
  LoginError   : String -> Msg
  TokenLoaded  : Maybe String -> Msg

-- Attempt login
loginEffect : String -> String -> Cmd Msg
loginEffect email password =
  loginCmd "/api/login" email password LoginResult LoginError

-- On success, save the token
update : Msg -> Model -> Model * Cmd Msg
update (LoginResult resp) m = record m { token = parseToken resp }
                            , saveToken (parseToken resp)
update (LoginError err) m   = record m { error = just err } , epsilon
update (TokenLoaded mt) m   = record m { token = mt } , epsilon
```

## Module Structure

```
Agdelte/Auth/
  JWT.agda          -- signJWT, verifyJWT, splitJWT
  Middleware.agda   -- AuthRequest, authenticate, withAuth, CORS
  Handler.agda      -- User, UserStore, handleRegister, handleLogin
  Client.agda       -- saveToken, clearToken, loadToken, authGet, authPost, loginCmd, registerCmd
```
