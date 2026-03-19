# Video Player — Content Protection Design

## Threat model

**Goal:** make casual downloading impractical. Full protection without hardware DRM
(Widevine L1, FairPlay TEE) is not achievable — a determined user with devtools
can always capture decoded frames. The objective is deterrence, not prevention.

**Target audience for protection:** casual users who would right-click → Save,
use browser extensions, or copy a URL from Network tab.

## Protection layers

### Layer 1 — No direct URL (baseline)

Video delivered via `MediaSource API`, not `<video src="url">`.
No single URL to copy/download. This is baked into the player architecture (see DESIGN.md).

**Agda-side:** The `videoPlayer` widget renders `<video>` with no `src` attribute.
Media is fed via `mediaSourceInit` / `mediaSourceAppend` Cmd constructors.
The `<video>` element's `src` is set to a `URL.createObjectURL(mediaSource)` blob URL
inside the JS runtime — not exposed in the Agda template.

### Layer 2 — Segmented delivery with signed URLs

- Video split into short segments (HLS `.m4s`).
- Each segment URL is a short-lived signed URL (expires in seconds).
- Manifest (`.m3u8`) also delivered with a short-lived token.
- Copying a segment URL after expiry yields 403.

**Server-side requirements:** URL signing endpoint, token validation middleware.

**Agda-side integration:**

The `PlayerConfig` has a `pcSignUrl : Maybe (String → String)` field.
When `just signFn`, the SegmentLoader pipeline calls `signFn` before fetching:

```agda
-- In SegmentLoader.agda:
buildSegmentUrl : PlayerConfig M A → String → ℕ → String
buildSegmentUrl cfg baseUrl segIdx =
  let url = baseUrl ++ "/" ++ showNat segIdx ++ ".m4s"
  in case pcSignUrl cfg of
       nothing → url
       just sign → sign url
```

The `sign` function is a JS postulate provided by the consumer. It appends
a query parameter with a short-lived HMAC token:

```agda
-- Consumer provides:
postulate signSegmentUrl : String → String
{-# COMPILE JS signSegmentUrl = function(url) {
  // Token from server, cached in closure with expiry tracking
  return url + "?token=" + currentToken + "&exp=" + expiry;
} #-}
```

**Token refresh** — when a segment fetch returns 403, SegmentLoader dispatches
`ProtectionError "token_expired"`. The consumer's update function can then
trigger a token refresh via `httpGet` Cmd and dispatch `TokenRefreshed`.

**Manifest delivery** — the initial manifest fetch also uses `pcSignUrl` if present.
The manifest URL in `pcManifestUrl` is the base URL; the signed version is computed
at load time.

### Layer 3 — Segment encryption (AES-128)

- Segments encrypted with AES-128-CBC.
- Encryption key delivered via a separate authenticated endpoint.
- Key rotation: new key every N segments (key period).
- Even if segments are intercepted, they are unusable without the key.

**Key delivery:** `fetch` with auth cookie/token → returns raw key bytes.
Standard `#EXT-X-KEY` in HLS manifest points to the key endpoint.

**Agda-side integration:**

New `Task` primitive for decryption (added to `Agdelte.Core.Task` and
`executeTask` in `runtime/reactive.js`):

```agda
-- In Task.agda:
--   decryptAES128 : String → String → String → Task String
--   -- key (base64), iv (base64), data (base64) → decrypted (base64)
```

```js
// In reactive.js executeTask:
'decryptAES128': (keyB64, ivB64, dataB64, cont) => {
  const key = base64ToArrayBuffer(keyB64);
  const iv = base64ToArrayBuffer(ivB64);
  const data = base64ToArrayBuffer(dataB64);
  crypto.subtle.importKey('raw', key, 'AES-CBC', false, ['decrypt'])
    .then(k => crypto.subtle.decrypt({ name: 'AES-CBC', iv }, k, data))
    .then(dec => cont.pure(arrayBufferToBase64(dec)))
    .catch(e => cont.fail(e.message));
}
```

SegmentLoader pipeline with encryption enabled:

```
buildURL → [signURL] → fetchArrayBuffer → decryptAES128 → base64 ArrayBuffer
```

All three steps compose as `Task` via `_>>=_`:

```agda
loadSegment : PlayerConfig M A → String → ℕ → Task String
loadSegment cfg baseUrl idx =
  let url = buildSegmentUrl cfg baseUrl idx
  in fetchArrayBuffer url >>= λ encrypted →
     case pcKeyEndpoint cfg of
       nothing  → pure encrypted   -- no encryption
       just kep →
         fetchKey kep >>= λ keyData →
         decryptAES128 (keyBytes keyData) (keyIV keyData) encrypted
```

Then used via `attempt` in the Cmd layer:

```agda
videoCmd (LoadNextSegment) model =
  attempt (loadSegment cfg baseUrl (currentSegment model))
    (λ { (ok data)  → SegmentLoaded (currentSegment model)
       ; (err msg)  → SegmentError (currentSegment model) msg
       })
  <> mediaSourceAppend videoSel data onAppended onAppendError
```

**Key caching** — the key endpoint returns a key valid for N segments.
Key caching is handled in the JS layer (inside `fetchKey` Task implementation)
to avoid re-fetching on every segment. The Agda side is unaware of caching.

**Key rotation** — the manifest's `#EXT-X-KEY` tag specifies which segments use
which key URI. The manifest parser (`parseM3U8` postulate) extracts key URIs
per segment range. Source.agda tracks the current key URI and re-fetches when
it changes.

### Layer 4 — Watermarking

- Invisible per-user watermark embedded in video at the encoding stage.
- Forensic (pixel-level): survives re-encoding and screen capture.
- Allows tracing the source of leaked content.

**Implementation:** server-side, during the transcoding pipeline in the admin interface.
Video is encoded/transcoded on our side anyway (admin uploads → transcode → store),
so watermarking integrates naturally into that pipeline.

**Delivery strategy: A/B segment mixing.**

At transcode time, each segment is encoded in two variants (A and B) with a
micro-difference (e.g. slight brightness shift). Storage cost: ×2 (fixed,
independent of user count). No per-user transcoding at delivery time.

Each user receives a unique combination of A/B variants across segments.
20 segments × 2 variants = 2²⁰ ≈ 1M unique users.

**Variant selection — deterministic PRNG (no database storage):**

The A/B sequence for a given user is computed on the fly via a linear
congruential generator seeded from the user ID:

```
state = (user_id × prime) mod M
for each segment:
  state = (state × prime) mod M
  variant = state & 1        // 0 → A, 1 → B
```

- `prime` and `M` chosen so the period exceeds the maximum segment count.
- No per-user state stored — the sequence is reproducible from `user_id` alone.
- On leak detection: iterate over users, regenerate their sequences, compare
  against the leaked video to identify the source.
- Cryptographic strength is not required — only uniqueness of combinations.
  The `prime` and `M` constants are server-side secrets.

**Stealth:** segment URLs are identical for all users; the server selects
the variant internally based on the authenticated user. No A/B markers
in URLs, filenames, or segment metadata.

**Player-side impact:** none. The player fetches segments normally.
Variant selection is entirely server-side, keyed by the auth token/cookie
already present in requests (from Layer 2). The player has no knowledge
of A/B variants.

**Leak detection pipeline (admin-side):**

```
Input: leaked video file
1. Split into segments (same boundaries as original)
2. For each segment, compare against A and B variants (SSIM or pixel diff)
3. Extract binary sequence: [A, B, A, A, B, ...]
4. For each user_id in database:
     a. Regenerate their A/B sequence via PRNG
     b. Compare against extracted sequence
     c. Score = number of matching segments / total
5. User with highest score (≈ 100%) is the source
```

Hamming distance tolerance handles re-encoding artifacts:
a few segments may be ambiguous, but 18/20 matches is still decisive.

### Layer 5 — UI-level deterrence

- Disable right-click context menu on video element.
- Detect devtools open (debugger timing, window size heuristic) — show warning or pause.
- CSS `pointer-events` / overlay to block drag.

**Note:** easily bypassed, but raises the bar for non-technical users.

**Agda-side implementation:**

Context menu prevention — add `on "contextmenu"` to the video element:

```agda
-- In Player.agda, on the <video> element:
  on "contextmenu" (wrap PreventDefault)  -- handled in JS as e.preventDefault()
```

This needs a minor runtime extension: the `on` handler currently dispatches
a message but doesn't prevent default. Options:

1. **New Attr variant:** `onPreventDefault : String → Msg → Attr Model Msg`
   — calls `e.preventDefault()` before dispatching.
2. **JS postulate approach:** add `attr "oncontextmenu" "return false;"` as
   an inline handler (works but bypasses the reactive event system).
3. **Recommended:** Option 1, added to `Agdelte.Reactive.Node.Core` as a new
   `Attr` constructor. Useful beyond video (forms, drag-and-drop, etc.).

```agda
-- In Core.agda Attr data type:
  onPreventDefault : String → Msg → Attr Model Msg

-- In reactive.js renderAttr:
'onPreventDefault': (eventName, msg) => {
  el.addEventListener(eventName, (e) => {
    e.preventDefault();
    dispatch(msg);
  }, { signal: currentScope.abortCtrl.signal });
}
```

Devtools detection — JS postulate, checked periodically:

```agda
postulate detectDevtools : String   -- returns "true" or "false"
{-# COMPILE JS detectDevtools =
  (function() {
    var t0 = performance.now();
    debugger;  // pauses if devtools open
    return (performance.now() - t0 > 100) ? "true" : "false";
  })()
#-}
```

Note: the `debugger` technique is aggressive and can be annoying. The window
size heuristic (comparing `window.outerWidth - window.innerWidth > threshold`)
is less intrusive. Both are easily bypassed. Consider making this opt-in
via a `pcDevtoolsDetection : Bool` field in PlayerConfig.

Transparent overlay to block drag/select:

```agda
-- In Controls.agda, rendered above <video>:
div [ class "agdelte-video__shield"
    , style "position" "absolute"
    , style "inset" "0"
    , style "z-index" "1"    -- above video, below controls
    , style "pointer-events" "auto"  -- captures drag attempts
    , on "contextmenu" (wrap PreventDefault)
    , on "dragstart" (wrap PreventDefault)
    ] []
```

## Server-side architecture

### Existing server constructs used (already in the codebase — do not redefine)

| Construct | Module | What it is |
|---|---|---|
| `listen` | `Agdelte.FFI.Server` | Start Warp HTTP server on port with handler |
| `HttpRequest`, `reqMethod`, `reqPath`, `reqBody` | `Agdelte.FFI.Server` | Request type + accessors |
| `HttpResponse`, `mkResponse` | `Agdelte.FFI.Server` | Response type (status + body) |
| `IORef`, `newIORef`, `readIORef`, `writeIORef` | `Agdelte.FFI.Server` | Mutable references |
| `MVar`, `newMVar`, `takeMVar`, `putMVar` | `Agdelte.FFI.Server` | Mutual exclusion |
| `_>>=_`, `_>>_`, `pure`, `bracket`, `onException`, `mask` | `Agdelte.FFI.Server` | IO combinators |
| `Agent`, `state`, `observe`, `stepAgent` | `Agdelte.Concurrent.Agent` | Coalgebra agent type |
| `wireAgent` | `Agdelte.FFI.Server` | Bridge pure Agent to IO (MVar-backed) |
| `serve`, `serveWithWs` | `hs/Agdelte/Http.hs` | Warp HTTP server (Haskell) |

### Overview

```
┌─────────────────────────────────────────────────────────────────────┐
│                          Internet                                   │
└──────────────────────────────┬──────────────────────────────────────┘
                               │
┌──────────────────────────────▼──────────────────────────────────────┐
│                        nginx (front)                                │
│                                                                     │
│  • TLS termination                                                  │
│  • Static segment serving (/segments/ → filesystem)                │
│  • Token validation (auth_request → Warp)                          │
│  • Rate limiting (per-IP, per-token)                               │
│  • Cache-Control headers                                           │
│  • Manifest proxy (/api/manifest → Warp)                           │
│  • Key endpoint proxy (/api/key → Warp)                            │
└─────┬──────────────────────────────────────┬───────────────────────┘
      │ static (fast path)                   │ dynamic (auth, keys)
      ▼                                      ▼
┌───────────────┐              ┌──────────────────────────────────────┐
│  Filesystem   │              │           Warp (Haskell)             │
│               │              │                                      │
│  /data/video/ │              │           Warp (Haskell)             │
│    {id}/      │              │                                      │
│      a/       │              │  Agda (MAlonzo-compiled):            │
│        0.m4s  │              │  • Token signing & validation        │
│        1.m4s  │              │  • Manifest generation (per-user)    │
│      b/       │              │  • A/B variant selection (PRNG)      │
│        0.m4s  │              │  • Session agent (rate limiting)     │
│        1.m4s  │              │  • Leak detection matching           │
│      init.mp4 │              │  • Request routing                   │
│      manifest │              │                                      │
│        .m3u8  │              │  FFI bindings (Haskell):             │
│               │              │  • HMAC, AES (→ cryptonite)          │
│               │              │  • ffmpeg (→ System.Process)         │
│               │              │  • Warp (→ Agdelte.Http.serve)       │
└───────────────┘              └──────────────────────────────────────┘
```

### nginx configuration

nginx handles two roles: static segment serving (fast, cached) and proxying
dynamic requests to Warp.

#### Static segment serving with token validation

```nginx
# /etc/nginx/conf.d/video.conf

upstream warp_backend {
    server 127.0.0.1:3100;  # Warp video API
    keepalive 32;
}

server {
    listen 443 ssl http2;
    server_name video.example.com;

    ssl_certificate     /etc/ssl/certs/video.pem;
    ssl_certificate_key /etc/ssl/private/video.key;

    # --- Static segment serving (Layer 2: token-gated) ---
    #
    # URL format: /segments/{videoId}/{segIdx}.m4s?token=...&exp=...
    #
    # auth_request validates the token via Warp before nginx serves the file.
    # On 200 from Warp, nginx serves from filesystem.
    # On 403, client gets 403 immediately — nginx never touches the file.
    #
    # The X-Variant header from Warp (Layer 4) tells nginx which variant to serve.

    location /segments/ {
        auth_request /auth/validate-token;
        auth_request_set $variant $upstream_http_x_variant;  # "a" or "b"

        # Rewrite: /segments/{videoId}/{seg}.m4s → /data/video/{videoId}/{variant}/{seg}.m4s
        # $variant comes from Warp's auth response (Layer 4: A/B selection).
        # If Warp returns no X-Variant (protection < Layer 4), defaults to "a".
        set $var $variant;
        if ($var = '') { set $var 'a'; }

        rewrite ^/segments/([^/]+)/(.+)$ /data/video/$1/$var/$2 break;
        root /;

        # Caching: segments are immutable (content-addressed by index).
        # But token expiry means the same URL won't be reused after expiry.
        add_header Cache-Control "private, max-age=10, no-transform";

        # Security: no MIME sniffing, no embedding
        add_header X-Content-Type-Options nosniff;
        add_header Content-Type video/iso.segment;

        # CORS (same-origin preferred; if cross-origin needed, restrict)
        add_header Access-Control-Allow-Origin $http_origin;
        add_header Access-Control-Allow-Credentials true;
    }

    # Init segment (ftyp+moov) — same token validation
    location ~ ^/segments/([^/]+)/init\.mp4$ {
        auth_request /auth/validate-token;
        rewrite ^/segments/([^/]+)/init\.mp4$ /data/video/$1/init.mp4 break;
        root /;
        add_header Cache-Control "private, max-age=60, no-transform";
        add_header Content-Type video/mp4;
    }

    # --- Auth subrequest endpoint (internal only) ---
    location = /auth/validate-token {
        internal;
        proxy_pass http://warp_backend/internal/validate-token;
        proxy_pass_request_body off;
        proxy_set_header Content-Length "";
        proxy_set_header X-Original-URI $request_uri;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header Cookie $http_cookie;
    }

    # --- Dynamic API (proxied to Warp) ---
    location /api/ {
        proxy_pass http://warp_backend;
        proxy_http_version 1.1;
        proxy_set_header Connection "";  # keepalive
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;
        proxy_set_header Cookie $http_cookie;
    }

    # --- Rate limiting ---
    # Per-IP: 30 segment requests/sec (burst 60).
    # Prevents bulk downloading even with valid tokens.
    limit_req_zone $binary_remote_addr zone=segments:10m rate=30r/s;

    location /segments/ {
        limit_req zone=segments burst=60 nodelay;
        # ... (merged with segment location above in real config)
    }
}
```

**Key design decisions:**

- **auth_request + X-Variant**: a single subrequest to Warp both validates
  the token (Layer 2) and selects the A/B variant (Layer 4). Two layers
  handled in one round-trip.
- **Filesystem layout**: `/data/video/{videoId}/a/` and `/data/video/{videoId}/b/`
  contain the two variants. `init.mp4` is shared (identical for both).
- **No segment URLs differ per user**: all users request the same URL
  (`/segments/{videoId}/3.m4s?token=...`). The variant is selected by Warp
  based on the user's auth cookie, returned as `X-Variant` header.
  nginx rewrites the path to the correct variant directory. The client
  has no way to observe which variant it received.

#### Why nginx serves segments (not Warp)

- nginx's `sendfile()` is zero-copy — kernel sends file data directly to socket.
  Warp would read file into Haskell heap → GC pressure on large files.
- nginx handles thousands of concurrent segment requests with minimal memory.
- Warp only handles the lightweight auth/key/manifest requests.

### Warp (Haskell) API server

Built on existing `Agdelte.Http` (`serve`/`serveWithWs` from `hs/Agdelte/Http.hs`).
No need for AgentServer — video protection is stateless request/response, not
a coalgebra agent.

#### Module structure

Agda (compiled via MAlonzo):
```
src/Agdelte/Video/
  Types.agda       — shared types, config records
  Token.agda       — HMAC token construction & validation (uses FFI.Crypto)
  Variant.agda     — A/B PRNG selection, leak detection matching (uses FFI.Word)
  Segment.agda     — segment state machine, key-segment mapping
  Pipeline.agda    — protection layer composition
  Manifest.agda    — HLS manifest generation (uses Token for signing)
  Session.agda     — playback session Agent (rate limiting)

server/VideoApi.agda — Warp routing, request handling, main
```

Haskell (FFI bindings only):
```
hs/Agdelte/Crypto.hs          — hmacSHA256, aesEncryptCBC, aesDecryptCBC (→ cryptonite)
hs/Agdelte/Video/Transcode.hs — ffmpeg command construction
```

See "Type-level guarantees" section below for why this split.

#### Endpoints

```
POST /api/token                  — issue a new signed token (requires auth cookie)
GET  /api/manifest/{videoId}     — return HLS manifest with signed segment URLs
GET  /api/key/{videoId}/{keyIdx} — return AES-128 key (requires auth cookie)

GET  /internal/validate-token    — nginx auth_request target (returns 200 or 403)
                                   + X-Variant header for A/B selection

POST /admin/upload               — upload video → start transcode pipeline
GET  /admin/transcode/{jobId}    — transcode job status
POST /admin/detect-leak          — upload leaked video → identify source user
```

#### Token.agda — HMAC signing & validation (Layer 2)

```agda
module Agdelte.Video.Token where

open import Agdelte.FFI.Crypto using (hmacSHA256)
open import Agdelte.FFI.Word using (Word64; w64fromNat; w64toNat)
open import Agdelte.Video.Types using (TokenParams; tpVideoId; tpUserId; tpSegStart; tpSegEnd; tpExpiry)

-- Token: HMAC-SHA256(secret, videoId | segmentRange | userId | expiry)
--
-- Fields packed into the token (not encrypted, but tamper-proof):
--   videoId      : which video
--   segStart     : first segment index this token covers
--   segEnd       : last segment index (range allows pre-fetching several segments)
--   userId       : who requested it (for A/B variant selection)
--   exp          : Unix timestamp (seconds) of expiry
--
-- The token is the hex-encoded HMAC. The fields are also sent as query params
-- so the server can reconstruct the message and verify the HMAC.
--
-- URL format: /segments/{videoId}/{idx}.m4s?uid={userId}&s={segStart}&e={segEnd}&exp={exp}&tok={hmac}

-- Canonical serialization: defined ONCE, used by both sign and validate
serializeParams : TokenParams → String
serializeParams tp =
  tpVideoId tp ++ "|" ++
  showNat (tpUserId tp) ++ "|" ++
  showNat (tpSegStart tp) ++ "|" ++
  showNat (tpSegEnd tp) ++ "|" ++
  showNat (tpExpiry tp)

-- Sign: produce HMAC for these params
signToken : String → TokenParams → String
signToken secret tp = hmacSHA256 secret (serializeParams tp)

-- Validate: check HMAC and expiry. Pure — time passed as argument.
validateToken : String → TokenParams → ℕ → Maybe TokenParams
validateToken secret params now =
  let expected = signToken secret params
  in if expected == tpSignature params ∧ tpExpiry params > now
     then just params
     else nothing

-- Issue: create token params for next N segments, expiring in T seconds
issueToken : String → String → ℕ → ℕ → ℕ → ℕ → TokenParams × String
--           secret   videoId  userId segStart segCount ttl now
issueToken secret videoId userId segStart segCount ttl now =
  let params = mkTokenParams videoId userId segStart (segStart + segCount) (now + ttl)
      sig = signToken secret params
  in params , sig
```

**Token flow:**

```
1. Browser loads page → auth cookie set (standard session, not video-specific)
2. Player init → Cmd httpGet "/api/manifest/{videoId}"
3. Warp checks auth cookie → identifies userId
4. Warp generates manifest with signed segment URLs:
     #EXTINF:4.0,
     /segments/{videoId}/0.m4s?uid=42&s=0&e=9&exp=1711036800&tok=a3b2c1...
     #EXTINF:4.0,
     /segments/{videoId}/1.m4s?uid=42&s=0&e=9&exp=1711036800&tok=a3b2c1...
     ...
   Token covers segments 0–9 (batch), expires in 30s.
5. Player fetches segment → nginx auth_request → Warp validates tok+exp
6. When approaching segment 8, player requests new manifest or new token
   → Warp issues token for segments 10–19
```

**Token batch strategy:** one token covers a range of segments (e.g. 10),
not one per segment. This reduces auth_request traffic and allows the player
to pre-fetch several segments ahead without extra round-trips. The range is
encoded in the token, so a token for segments 0–9 cannot be used for segment 15.

#### Segment.agda — key management & encryption (Layer 3)

```agda
module Agdelte.Video.Segment where

open import Agdelte.FFI.Crypto using (aesEncrypt; aesDecrypt; randomBytes)
open import Agdelte.FFI.Server using (IORef; newIORef; readIORef; writeIORef; _>>=_; pure)

-- Key period: number of segments sharing one key
-- 10 segments ≈ 40 seconds of video per key
KeyPeriod : ℕ
KeyPeriod = 10

-- Key record (see Guarantee 4 below for indexed version)
record AESKey : Set where
  field
    keyBytes : String    -- base64, 16 bytes
    ivBytes  : String    -- base64, 16 bytes

-- Key table: list of (keyIndex, key). Loaded from keys.json at startup.
KeyTable : Set
KeyTable = List (ℕ × AESKey)

-- Lookup key for a segment index
keyForSegment : KeyTable → ℕ → Maybe AESKey
keyForSegment table segIdx = lookup (segIdx / KeyPeriod) table

-- Generate key table for N segments (IO — uses randomBytes)
generateKeyTable : ℕ → IO KeyTable
generateKeyTable totalSegments =
  let periods = suc (totalSegments / KeyPeriod)
  in mapM (λ i → randomBytes 16 >>= λ k →
                  randomBytes 16 >>= λ iv →
                  pure (i , record { keyBytes = k ; ivBytes = iv }))
          (range 0 periods)

-- Encrypt segment (pure — delegates to FFI)
encryptSegment : AESKey → String → String
encryptSegment key plaintext = aesEncrypt (keyBytes key) (ivBytes key) plaintext

-- Serve key: returns base64 key bytes for a given keyIdx
-- Auth check happens in the router (AuthRequest); this just does the lookup.
serveKey : KeyTable → ℕ → Maybe String
serveKey table keyIdx = map keyBytes (lookup keyIdx table)
```

**Key storage:**

```
/data/video/{videoId}/
  keys.json          — { "0": {"key": "base64...", "iv": "base64..."}, "1": ... }
  a/0.m4s            — encrypted segment (if Layer 3 enabled)
  a/1.m4s
  b/0.m4s
  ...
```

`keys.json` is read once at startup (or on first access, cached in IORef).
Keys are small (32 bytes per period), so even a video with 1000 segments
= 100 keys = 3.2 KB — trivially fits in memory.

**Manifest with EXT-X-KEY:**

```
#EXTM3U
#EXT-X-VERSION:7
#EXT-X-TARGETDURATION:4
#EXT-X-MAP:URI="/segments/{videoId}/init.mp4?tok=..."

#EXT-X-KEY:METHOD=AES-128,URI="/api/key/{videoId}/0",IV=0x00000000000000000000000000000000
#EXTINF:4.0,
/segments/{videoId}/0.m4s?uid=42&s=0&e=9&exp=...&tok=...
#EXTINF:4.0,
/segments/{videoId}/1.m4s?uid=42&s=0&e=9&exp=...&tok=...
...
#EXT-X-KEY:METHOD=AES-128,URI="/api/key/{videoId}/1",IV=0x00000000000000000000000000000001
#EXTINF:4.0,
/segments/{videoId}/10.m4s?uid=42&s=10&e=19&exp=...&tok=...
```

Note: since we do client-side decryption via `crypto.subtle` (not native HLS),
the `#EXT-X-KEY` tags are parsed by our manifest parser (JS postulate), not by
the browser. The key URI tells the player where to fetch the key.

#### Variant.agda — A/B PRNG selection (Layer 4)

```agda
module Agdelte.Video.Variant where

open import Agdelte.FFI.Word using (Word64; w64fromNat; _*w_; _modw_; oddw)

-- Server-side secrets. Loaded from config, never sent to client.
-- Must be coprime with variantM. Choose a large prime.
-- Using Word64 for O(1) arithmetic instead of Peano ℕ.
variantPrime : Word64
variantPrime = w64fromNat 48271      -- example; real value loaded from config

variantM : Word64
variantM = w64fromNat 2147483647     -- 2^31 - 1 (Mersenne prime)

-- Core PRNG step — pure, uses Word64 arithmetic
prngStep : Word64 → Word64
prngStep state = (state *w variantPrime) modw variantM

-- Seed from userId
prngSeed : Word64 → Word64
prngSeed userId = (userId *w variantPrime) modw variantM

-- Select variant for a specific segment
selectVariant : Word64 → ℕ → Bool   -- userId → segIdx → false=A, true=B
selectVariant userId segIdx =
  let state = iterate prngStep (prngSeed userId) (suc segIdx)
  in oddw state

-- Full sequence for a user (used by BOTH delivery and detection — see Guarantee 5)
userSequence : Word64 → ℕ → List Bool
userSequence userId totalSegs = map (selectVariant userId) (range 0 totalSegs)

-- Leak detection: compare observed against expected
matchScore : List (Maybe Bool) → List Bool → ℕ × ℕ  -- (matches, totalKnown)
matchScore [] _ = 0 , 0
matchScore _ [] = 0 , 0
matchScore (nothing ∷ obs) (_ ∷ exp) = matchScore obs exp
matchScore (just o ∷ obs) (e ∷ exp) =
  let (m , t) = matchScore obs exp
  in (if o == e then suc m else m) , suc t
```

**Integration with nginx auth_request:**

When nginx sends `auth_request` to `/internal/validate-token`, Warp:

1. Extracts `token`, `exp`, `uid`, `s`, `e` from query params (X-Original-URI header).
2. Validates HMAC and checks expiry.
3. Extracts segment index from the URI path.
4. Calls `selectVariant userId segIdx`.
5. Returns `200` with `X-Variant: a` (or `b`) header.
6. nginx uses `X-Variant` to select the filesystem path.

```agda
handleValidateToken : String → List (String × String) → ℕ → HttpResponse
--                    secret   headers                  now
handleValidateToken secret headers now =
  case lookupHeader "X-Original-URI" headers of
    nothing → mkResponse 403 "Missing X-Original-URI"
    just uri →
      case parseTokenFromURI uri of
        nothing → mkResponse 403 "Invalid token format"
        just (params , segIdx) →
          case validateToken secret params now of
            nothing → mkResponse 403 "Token expired or invalid"
            just validParams →
              let var = selectVariant (w64fromNat (tpUserId validParams)) segIdx
              in mkResponseH 200 ""
                   (("X-Variant" , if var then "b" else "a") ∷ [])
```

#### Transcode — upload → A/B segments (Layer 4)

Transcode pipeline (runs as background job):

```
1. Admin uploads video via POST /admin/upload
2. Server saves to temp file, creates job record, returns jobId
3. Background thread runs ffmpeg pipeline:

   Input.mp4
     │
     ├─ ffmpeg (variant A): brightness +0.3%
     │   → segmenter → /data/video/{id}/a/0.m4s, 1.m4s, ...
     │
     └─ ffmpeg (variant B): brightness -0.3%
         → segmenter → /data/video/{id}/b/0.m4s, 1.m4s, ...

   + init segment:  /data/video/{id}/init.mp4  (shared, from either variant)
   + base manifest: /data/video/{id}/manifest.m3u8 (template, no tokens)
   + key table:     /data/video/{id}/keys.json (if Layer 3 enabled)

4. If Layer 3 enabled, encrypt all segments with keys from key table.
5. Update job status → "done".
```

ffmpeg commands:
```bash
# Variant A (brightness +0.3%):
ffmpeg -i input.mp4 \
  -vf "eq=brightness=0.003" \
  -c:v libx264 -preset medium -crf 23 \
  -c:a aac -b:a 128k \
  -f hls \
  -hls_time 4 \
  -hls_segment_type fmp4 \
  -hls_fmp4_init_filename init.mp4 \
  -hls_segment_filename '/data/video/{id}/a/%d.m4s' \
  /data/video/{id}/a/playlist.m3u8

# Variant B: same but -vf "eq=brightness=-0.003"
```

The brightness difference (±0.003 ≈ ±0.3%) is:
- Invisible to human eye (below JND threshold for most content)
- Detectable by SSIM comparison between A and B
- Survives re-encoding (spatial, not temporal artifact)
- Survives moderate quality reduction (not a fragile watermark)

ffmpeg command construction lives in `hs/Agdelte/Video/Transcode.hs` because
it's purely mechanical string building with no invariants to protect. The job
management (status tracking, polling) is in Agda:

```agda
data TranscodeStatus : Set where
  Queued : TranscodeStatus
  Running : String → TranscodeStatus   -- progress "0.45"
  Done : TranscodeStatus
  Failed : String → TranscodeStatus

record TranscodeJob : Set where
  field
    tjVideoId   : String
    tjStatus    : TranscodeStatus
    tjSegCount  : Maybe ℕ
    tjEncrypted : Bool
```

**Filesystem layout after transcode:**

```
/data/video/{videoId}/
  init.mp4              — fMP4 init segment (ftyp + moov), shared
  manifest.m3u8         — base manifest template (no tokens, no keys)
  keys.json             — key table (Layer 3; absent if unencrypted)
  a/
    0.m4s               — variant A, segment 0
    1.m4s               — variant A, segment 1
    ...
  b/
    0.m4s               — variant B, segment 0
    1.m4s               — variant B, segment 1
    ...
  meta.json             — { totalSegments, duration, codec, resolution, ... }
```

If Layer 4 (watermarking) is not enabled, only the `a/` directory exists.
If Layer 3 (encryption) is not enabled, `keys.json` is absent and segments
are plaintext.

#### Manifest.agda — per-user manifest generation (Layers 2+3)

```agda
module Agdelte.Video.Manifest where

open import Agdelte.Video.Token using (issueToken; serializeParams; signToken)
open import Agdelte.Video.Segment using (KeyTable; KeyPeriod)
open import Agdelte.FFI.Time using (getPosixTime)

-- Generate HLS manifest for a specific user.
-- Called by GET /api/manifest/{videoId}.
--
-- 1. Read meta (segment count, duration) — passed as VideoMeta
-- 2. Generate signed URLs for all segments (Layer 2)
-- 3. Insert #EXT-X-KEY tags with key endpoint URLs (Layer 3, if encrypted)
-- 4. Return complete .m3u8 text
--
-- Generated on the fly — not cached — because:
-- - Tokens are short-lived (unique per request)
-- - userId is baked into token params (for A/B selection on segment fetch)
-- - Generation is cheap (string concatenation, HMAC)

record VideoMeta : Set where
  field
    totalSegments  : ℕ
    segmentDuration : String   -- e.g. "4.0"
    encrypted      : Bool

generateManifest : String → String → ℕ → VideoMeta → ℕ → String
--                 secret   videoId  userId meta       now → .m3u8 content
generateManifest secret videoId userId meta now =
  let tokenBatchSize = 10
      header = "#EXTM3U\n#EXT-X-VERSION:7\n#EXT-X-TARGETDURATION:"
               ++ segmentDuration meta ++ "\n"
      initSeg = "#EXT-X-MAP:URI=\"/segments/" ++ videoId ++ "/init.mp4?"
                ++ tokenQuery secret videoId userId 0 0 now ++ "\"\n"
      segments = concatMap (renderSegment secret videoId userId meta now)
                           (range 0 (totalSegments meta))
  in header ++ initSeg ++ segments

-- Render one segment entry with optional #EXT-X-KEY
renderSegment : String → String → ℕ → VideoMeta → ℕ → ℕ → String
renderSegment secret videoId userId meta now idx =
  let keyTag = if encrypted meta ∧ idx mod KeyPeriod ≡ 0
               then "#EXT-X-KEY:METHOD=AES-128,URI=\"/api/key/"
                    ++ videoId ++ "/" ++ showNat (idx / KeyPeriod) ++ "\"\n"
               else ""
      (tp , sig) = issueToken secret videoId userId idx (idx + 9) 30 now
      segLine = "#EXTINF:" ++ segmentDuration meta ++ ",\n"
                ++ "/segments/" ++ videoId ++ "/" ++ showNat idx ++ ".m4s?"
                ++ tokenQueryString tp sig ++ "\n"
  in keyTag ++ segLine

-- | Build query string from token params + signature
tokenQueryString : TokenParams → String → String
tokenQueryString tp sig =
  "uid=" ++ showNat (tpUserId tp)
  ++ "&s=" ++ showNat (tpSegStart tp)
  ++ "&e=" ++ showNat (tpSegEnd tp)
  ++ "&exp=" ++ showNat (tpExpiry tp)
  ++ "&tok=" ++ sig
```

The manifest includes the init segment URI with a token:
```
#EXT-X-MAP:URI="/segments/{videoId}/init.mp4?uid=42&exp=...&tok=..."
```

#### LeakDetect — identify source user (Layer 4)

Leak detection has two parts:
- **SSIM extraction** (IO-heavy, shells out to ffmpeg) — in Agda with FFI.Process
- **Matching** (pure, uses Variant.agda) — pure Agda, same `matchScore` function

```agda
-- In Agdelte.Video.Variant (already defined above):
-- matchScore : List (Maybe Bool) → List Bool → ℕ × ℕ

-- In a separate LeakDetect module or in Server.agda:

record LeakResult : Set where
  field
    lrUserId  : ℕ
    lrMatched : ℕ
    lrTotal   : ℕ

-- Pure matching: test one user against observed sequence
testUser : ℕ → ℕ → List (Maybe Bool) → LeakResult
testUser userId totalSegs observed =
  let expected = userSequence (w64fromNat userId) totalSegs
      (matched , total) = matchScore observed expected
  in record { lrUserId = userId ; lrMatched = matched ; lrTotal = total }

-- Test all candidate userIds (pure — can be parallelized via Haskell runtime)
detectAll : List ℕ → ℕ → List (Maybe Bool) → List LeakResult
detectAll userIds totalSegs observed =
  sortBy (λ a b → lrMatched b ≤? lrMatched a)
    (map (λ uid → testUser uid totalSegs observed) userIds)
```

SSIM extraction (IO part) shells out to ffmpeg:
```agda
-- Uses FFI.Process postulate:
postulate runFfmpegSSIM : String → String → IO String
--                        segmentPath variantPath → SSIM score as String
{-# COMPILE GHC runFfmpegSSIM = ... #-}

-- Compare one segment against A and B variants, classify
classifySegment : String → String → String → IO (Maybe Bool)
--                segPath   variantAPath variantBPath
classifySegment seg a b =
  runFfmpegSSIM seg a >>= λ ssimA →
  runFfmpegSSIM seg b >>= λ ssimB →
  pure (if parseFloat ssimA > 0.99 then just false     -- matches A
        else if parseFloat ssimB > 0.99 then just true -- matches B
        else nothing)                                    -- ambiguous
```

### Warp server wiring

The Warp video API server is a standalone process, separate from the existing
AgentServer-based servers. Written in Agda, compiled via MAlonzo, using
existing `listen` from `Agdelte.FFI.Server`:

```agda
-- server/VideoApi.agda
module VideoApi where

open import Agdelte.FFI.Server using (listen; HttpRequest; HttpResponse; mkResponse;
  reqMethod; reqPath; reqBody; reqHeaders;
  IORef; newIORef; readIORef; writeIORef;
  _>>=_; _>>_; pure;
  AgentDef; wireAgent; mkAgentDef)
open import Agdelte.FFI.Crypto using (hmacSHA256)
open import Agdelte.FFI.Time using (getPosixTime)
open import Agdelte.FFI.FileSystem using (readFileText)
open import Agdelte.FFI.Word using (Word64; w64fromNat)
open import Agdelte.Video.Token using (TokenParams; tpUserId; serializeParams; validateToken; issueToken)
open import Agdelte.Video.Variant using (selectVariant)
open import Agdelte.Video.Manifest using (generateManifest; VideoMeta)
open import Agdelte.Video.Segment using (KeyTable; serveKey)
open import Agdelte.Video.Session using (videoSession; SessionState; SessionInput; SessionOutput)
open import Agdelte.Video.Types
open import Agdelte.Concurrent.Agent using (Agent)

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

-- | Response with custom headers (new postulate — see "Required changes" section)
postulate mkResponseH : Nat → String → List (String × String) → HttpResponse

------------------------------------------------------------------------

-- | Lookup a header by name (case-insensitive comparison via postulate)
lookupHeader : String → List (String × String) → Maybe String
lookupHeader _ [] = nothing
lookupHeader name ((k , v) ∷ rest) =
  if eqStrCI name k then just v else lookupHeader name rest

postulate eqStrCI : String → String → Bool  -- case-insensitive string equality
{-# COMPILE GHC eqStrCI = \a b -> Data.Text.toCaseFold a == Data.Text.toCaseFold b #-}

-- | Route type: parsed request path
data Route : Set where
  ApiManifest         : String → Route           -- /api/manifest/{videoId}
  ApiKey              : String → ℕ → Route       -- /api/key/{videoId}/{keyIdx}
  ApiToken            : Route                    -- /api/token
  InternalValidate    : Route                    -- /internal/validate-token
  AdminUpload         : Route                    -- /admin/upload
  AdminTranscode      : String → Route           -- /admin/transcode/{jobId}
  AdminDetectLeak     : Route                    -- /admin/detect-leak
  NotFound            : Route

-- | Parse request path into Route
postulate parsePath : String → Route
{-# COMPILE JS parsePath = ... #-}  -- MAlonzo: pattern match on path segments
-- Implementation: split on "/", match prefixes:
--   ["api","manifest",vid] → ApiManifest vid
--   ["api","key",vid,idx]  → ApiKey vid (parseNat idx)
--   ["api","token"]        → ApiToken
--   ["internal","validate-token"] → InternalValidate
--   _ → NotFound

-- | Parse token params and segment index from a signed URL
-- Input: "/segments/vid123/5.m4s?uid=42&s=0&e=9&exp=1711036800&tok=abc..."
-- Output: (TokenParams, segIdx)
postulate parseTokenFromURI : String → Maybe (TokenParams × ℕ)
{-# COMPILE GHC parseTokenFromURI = ... #-}
-- Implementation: parse query params, construct TokenParams, extract segment
-- index from path. ~20 lines of Haskell string splitting.

-- | Authenticate request by extracting userId from session cookie.
-- Returns Maybe because auth can fail (expired session, no cookie).
-- This is the only postulate that touches external state (session store).
postulate authenticate : HttpRequest → IO (Maybe AuthRequest)
{-# COMPILE GHC authenticate = \req -> do
  let cookies = parseCookies (lookupHeader "Cookie" (Http.reqHeaders req))
  case Map.lookup "session" cookies of
    Nothing -> return Nothing
    Just sid -> do
      mUser <- lookupSession sid  -- Redis/DB lookup
      return (fmap (\uid -> AuthRequest uid req) mUser)
#-}

record AuthRequest : Set where
  field
    userId : ℕ
    raw    : HttpRequest

------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------

-- | Load secret from file at startup
postulate loadSecret : String → IO String
{-# COMPILE GHC loadSecret = TIO.readFile . T.unpack #-}

-- | Server state: key tables loaded lazily per video
record ServerState : Set where
  field
    secret    : String
    keyTables : IORef (List (String × KeyTable))  -- videoId → KeyTable

-- | Load key table for a video (reads keys.json, caches in IORef)
loadKeyTable : ServerState → String → IO KeyTable
loadKeyTable st videoId =
  readIORef (keyTables st) >>= λ tables →
  case lookup videoId tables of
    just kt → pure kt
    nothing →
      readFileText ("/data/video/" ++ videoId ++ "/keys.json") >>= λ json →
      let kt = parseKeyTable json   -- postulate: JSON → KeyTable
      in writeIORef (keyTables st) ((videoId , kt) ∷ tables) >>
         pure kt

postulate parseKeyTable : String → KeyTable
{-# COMPILE GHC parseKeyTable = ... #-}  -- aeson: decode JSON to [(ℕ, AESKey)]

main : IO ⊤
main =
  loadSecret "/run/secrets/video-token-key" >>= λ sec →
  newIORef []                               >>= λ ktRef →
  let st = record { secret = sec ; keyTables = ktRef }
  in listen 3100 (router st)

router : ServerState → HttpRequest → IO HttpResponse
router st req =
  case parsePath (reqPath req) of

    -- Public API (requires auth cookie)
    ApiManifest videoId →
      authenticate req >>= λ
        { nothing → pure (mkResponse 403 "Unauthorized")
        ; (just authReq) →
          readFileText ("/data/video/" ++ videoId ++ "/meta.json") >>= λ metaJson →
          let meta = parseVideoMeta metaJson   -- postulate
          in getPosixTime >>= λ now →
             let m3u8 = generateManifest (secret st) videoId (userId authReq) meta now
             in pure (mkResponseH 200 m3u8
                  (("Content-Type" , "application/vnd.apple.mpegurl") ∷ []))
        }

    ApiKey videoId keyIdx →
      authenticate req >>= λ
        { nothing → pure (mkResponse 403 "Unauthorized")
        ; (just authReq) →
          loadKeyTable st videoId >>= λ kt →
          case serveKey kt keyIdx of
            nothing → pure (mkResponse 404 "Key not found")
            just keyB64 → pure (mkResponseH 200 keyB64
              (("Content-Type" , "application/octet-stream") ∷ []))
        }

    InternalValidate →
      let headers = reqHeaders req
      in case lookupHeader "X-Original-URI" headers of
           nothing → pure (mkResponse 403 "Missing X-Original-URI")
           just uri →
             case parseTokenFromURI uri of
               nothing → pure (mkResponse 403 "Invalid token format")
               just (params , segIdx) →
                 getPosixTime >>= λ now →
                 case validateToken (secret st) params now of
                   nothing → pure (mkResponse 403 "Token expired or invalid")
                   just validParams →
                     let var = selectVariant (w64fromNat (tpUserId validParams)) segIdx
                     in pure (mkResponseH 200 ""
                          (("X-Variant" , if var then "b" else "a") ∷ []))

    _ → pure (mkResponse 404 "Not found")

postulate parseVideoMeta : String → VideoMeta
{-# COMPILE GHC parseVideoMeta = ... #-}  -- aeson: decode meta.json
```

All business logic — routing, token validation, variant selection, manifest
generation — is type-checked Agda. Postulates are limited to:
- IO operations (`loadSecret`, `readFileText`, `authenticate`, `getPosixTime`)
- String parsing (`parsePath`, `parseTokenFromURI`, `parseKeyTable`, `parseVideoMeta`)
- Crypto (`hmacSHA256` via FFI.Crypto)

### Authentication

The video API does **not** implement its own auth. It relies on the application's
existing session mechanism:

- Browser has an auth cookie (e.g., `session=abc123`) set by the main application.
- `authenticate` (postulate) reads the cookie, looks up `userId` in a shared
  session store (Redis, database, or validates a JWT with a shared secret).
- Returns `Maybe AuthRequest` — `nothing` if session is invalid/expired.
- The `AuthRequest` type (see Guarantee 1) ensures handlers that need auth
  can only receive authenticated requests.

This means: no separate video login, no OAuth flow for video. The user's existing
session is sufficient.

For the internal `/internal/validate-token` endpoint, the auth cookie is forwarded
by nginx (`proxy_set_header Cookie $http_cookie`). But the primary validation is
HMAC-based (the token itself encodes the userId and is tamper-proof), so even if
the cookie is absent, the token alone is sufficient for segment access. The cookie
is used only as a fallback for A/B variant selection if the token doesn't encode userId.

### Deployment topology

```
                    ┌──────────────┐
                    │   Browser    │
                    └──────┬───────┘
                           │ HTTPS
                    ┌──────▼───────┐
                    │    nginx     │
                    │  (port 443)  │
                    └──┬───────┬───┘
           static ─────┘       └───── dynamic
        (sendfile)                (proxy_pass)
    ┌──────▼───────┐        ┌──────▼───────┐
    │  Filesystem  │        │    Warp      │
    │ /data/video/ │        │ (port 3100)  │
    └──────────────┘        └──────────────┘
```

Both nginx and Warp run on the same machine. Warp listens on 127.0.0.1 only —
not exposed to the internet.

**Scaling (if needed later):**
- Horizontal: multiple nginx+Warp instances behind a load balancer.
  Token validation is stateless (HMAC). Key tables are per-video (read-only).
  Session store must be shared (Redis/DB).
- CDN: segments can be served via CDN with signed URLs. The CDN validates
  the token (or uses origin-pull with auth_request). A/B variant selection
  stays at origin (CDN caches both variants, keyed by `Vary: X-Variant`
  or by query param).

### Dependencies (additions to flake.nix)

```nix
# New Haskell packages (for FFI bindings):
cryptonite      # HMAC-SHA256, AES-128-CBC → Agdelte.FFI.Crypto
memory          # ByteArray conversions (used by cryptonite)
base64          # base64 encoding/decoding
aeson           # JSON for meta.json, keys.json, API responses → Agdelte.FFI.Json
process         # System.Process for ffmpeg → Agdelte.FFI.Process (extend existing)

# Runtime:
ffmpeg          # transcode pipeline (admin machine only)
```

All available in nixpkgs. The Haskell packages are used only via FFI postulates
from Agda — no direct Haskell application code except thin wrappers in
`hs/Agdelte/Crypto.hs` (~50 lines) and `hs/Agdelte/Video/Transcode.hs` (~30 lines).

### Summary: what each layer needs server-side

| Layer | nginx | Warp | Filesystem | External |
|---|---|---|---|---|
| 1 | — | — | — | — |
| 2 | `auth_request` + token validation proxy | Token.hs: sign/validate HMAC | — | — |
| 3 | — | Key.hs: serve key bytes, Manifest.hs: `#EXT-X-KEY` tags | `keys.json` per video | — |
| 4 | `X-Variant` header → path rewrite | Variant.hs: PRNG, validate-token returns X-Variant | `a/` + `b/` segment dirs | ffmpeg (transcode) |
| 5 | — | — | — | — |

## Type-level guarantees (Agda for server logic)

The video protection server has structure that benefits from dependent types —
not for every module, but for the core invariants where a bug means silent
data leak or wrong user blamed for piracy.

### Approach: full Agda with bindings

The server is written in Agda and compiled via MAlonzo. MAlonzo generates
adequate Haskell code — the overhead is small when the right set of bindings
is in place:

1. **Library bindings** — postulates with `COMPILE GHC` for Haskell libraries
   that have no reason to be reimplemented (cryptonite for HMAC/AES,
   aeson for JSON, process for ffmpeg, warp/wai for HTTP).
2. **Performance bindings** — `Word64` for PRNG arithmetic (instead of Peano ℕ),
   `Text` for string operations, `Vector`/array-index references where
   GC pressure matters. These are small, targeted, and the rest of the code
   stays idiomatic Agda.

With this set, the entire server — routing, token logic, variant selection,
manifest generation, session management — lives in Agda. Haskell is only
the FFI layer, not a parallel codebase.

### Module structure

```
src/Agdelte/Video/
  Types.agda         — shared types: TokenParams, Segment, ProtLevel, etc.
  Token.agda         — token construction, serialization, validation
  Variant.agda       — PRNG, A/B selection, leak detection matching
  Segment.agda       — segment state machine, key-segment mapping
  Pipeline.agda      — protection layer composition
  Session.agda       — playback session Agent (rate limiting, abuse detection)
  Manifest.agda      — HLS manifest generation
  Server.agda        — Warp routing, request handling, main

src/Agdelte/FFI/
  Crypto.agda        — bindings: HMAC-SHA256, AES-128-CBC (→ cryptonite)
  Json.agda          — bindings: encode/decode (→ aeson)
  Process.agda       — bindings: run ffmpeg (→ System.Process) [existing + extend]
  Word.agda          — bindings: Word64 arithmetic (→ Data.Word)
  FileSystem.agda    — bindings: readFile, writeFile, listDirectory
  Time.agda          — bindings: getPOSIXTime, UTCTime

hs/Agdelte/
  Crypto.hs          — thin wrappers: hmacSHA256, aesEncrypt, aesDecrypt
  Video/Transcode.hs — ffmpeg command construction (complex shell args)
```

The `hs/` layer is minimal — just enough to bridge Agda postulates to
Haskell library calls. No business logic in Haskell.

### Guarantee 1: Authenticated requests — separate type

**Problem:** A handler accidentally skips auth check. In pure Haskell, `Request`
is `Request` — nothing stops you from reading `userId` from an unauthenticated
request (it's just not there, but you'd find out at runtime).

**Agda solution:**

```agda
-- Raw request: no userId available
record RawRequest : Set where
  field
    method  : String
    path    : String
    body    : String
    headers : List (String × String)

-- Authenticated request: userId is a field, not a Maybe
record AuthRequest : Set where
  field
    userId  : ℕ
    videoId : String
    raw     : RawRequest

-- The ONLY way to get an AuthRequest from a RawRequest.
-- This is a postulate because actual cookie/session validation is IO.
-- But the type boundary is enforced: no AuthRequest without calling this.
postulate
  authenticate : RawRequest → IO (Maybe AuthRequest)

-- Handler types: manifest/key/validate REQUIRE AuthRequest
handleManifest      : AuthRequest → IO Response   -- cannot forget auth
handleKey           : AuthRequest → IO Response
handleValidateToken : AuthRequest → IO Response

-- Admin handler: could be a separate type (AdminRequest) for role check
```

**What this prevents:** Every handler that needs a userId is forced to receive
`AuthRequest`, which can only be produced by `authenticate`. A new endpoint
added by a future contributor cannot accidentally skip auth — it won't
type-check.

In Haskell, the equivalent is `newtype AuthRequest = AuthRequest Request` with
a smart constructor, but newtypes can be `coerce`d or pattern-matched to
extract the inner `Request`. In Agda, the only way to get the `userId` field
is through the `AuthRequest` type.

### Guarantee 2: Token indexed by its parameters

**Problem:** Token signing and validation must agree on which fields are covered
by the HMAC. If `signToken` hashes `(videoId, userId, segStart, segEnd, expiry)`
but `validateToken` reconstructs the message as `(videoId, segStart, segEnd, userId, expiry)`
(swapped order), the HMAC won't match — silent failure. Or worse: if a field
is accidentally omitted from the HMAC message, the token is valid for any value
of that field.

**Agda solution:**

```agda
-- Token parameters: a record with all fields that must be covered
record TokenParams : Set where
  constructor mkTokenParams
  field
    tpVideoId  : String
    tpUserId   : ℕ
    tpSegStart : ℕ
    tpSegEnd   : ℕ
    tpExpiry   : ℕ

-- Canonical serialization: defined ONCE, used by both sign and validate.
-- Not a postulate — pure Agda, so we can inspect it.
serializeParams : TokenParams → String
serializeParams tp =
  tpVideoId tp ++ "|" ++
  showNat (tpUserId tp) ++ "|" ++
  showNat (tpSegStart tp) ++ "|" ++
  showNat (tpSegEnd tp) ++ "|" ++
  showNat (tpExpiry tp)

-- Deserialization: parses back, must be inverse of serialize
-- (can be verified by a round-trip property test, or even proved)
deserializeParams : String → Maybe TokenParams

-- Sign and validate both use serializeParams — SAME function.
-- The HMAC itself is a Haskell postulate (cryptonite), but the message
-- construction is in Agda, shared between sign and validate.

postulate hmacSHA256 : String → String → String  -- secret, message → hex digest

signToken : String → TokenParams → String
signToken secret tp = hmacSHA256 secret (serializeParams tp)

-- Validate: deserialize, recompute HMAC, compare.
-- Returns the SAME TokenParams that were signed — not re-parsed from URL.
validateToken : String → String → String → Maybe TokenParams
--              secret    paramStr  providedHmac
validateToken secret paramStr providedHmac =
  case deserializeParams paramStr of
    nothing → nothing
    just tp →
      let expected = signToken secret tp
      in if expected == providedHmac then just tp else nothing
```

**What this prevents:**
- Sign/validate message mismatch — impossible, they call the same `serializeParams`.
- Field omission — if you add a field to `TokenParams`, `serializeParams` must
  be updated (Agda's coverage checker ensures all fields are used if you
  pattern-match on the record).
- Field order swap — the serialization order is defined once.

### Guarantee 3: Segment state machine — pipeline correctness

**Problem:** A segment must go through protection layers in the right order.
Serving an unencrypted segment when encryption is enabled = content leak.
Encrypting an already-encrypted segment = corruption.

**Agda solution:**

```agda
-- Protection level is a type index, not a runtime flag
data ProtLevel : Set where
  Raw Encrypted Signed : ProtLevel

-- Segment indexed by its protection state
record Segment (p : ProtLevel) : Set where
  field
    segVideoId : String
    segIndex   : ℕ
    segPayload : String   -- base64 content

-- Operations are typed by state transitions:

-- Encrypt: Raw → Encrypted (only)
encryptSeg : String → String → Segment Raw → Segment Encrypted
encryptSeg key iv seg = record
  { segVideoId = segVideoId seg
  ; segIndex   = segIndex seg
  ; segPayload = aesEncrypt key iv (segPayload seg)  -- postulate
  }

-- Sign URL: any state → Signed (adds token to URL, marks as ready to serve)
signSeg : String → TokenParams → Segment p → Segment Signed
signSeg secret tp seg = record
  { segVideoId = segVideoId seg
  ; segIndex   = segIndex seg
  ; segPayload = segPayload seg  -- payload unchanged, signing is URL-level
  }

-- Serve: ONLY Signed segments can be served
serveSeg : Segment Signed → Response
```

**What this prevents:**
- Serving `Segment Raw` — type error. The HTTP handler returns `Response`,
  which can only be produced from `Segment Signed` via `serveSeg`.
- Double encryption — `encryptSeg` requires `Segment Raw`, not `Segment Encrypted`.
- Serving encrypted-but-unsigned — `serveSeg` requires `Signed`, not `Encrypted`.

For different protection configurations (with/without encryption), the pipeline
type changes:

```agda
-- No encryption: Raw → Signed → serve
pipelineNoEncrypt : String → TokenParams → Segment Raw → Response
pipelineNoEncrypt secret tp = serveSeg ∘ signSeg secret tp

-- With encryption: Raw → Encrypted → Signed → serve
pipelineEncrypted : String → String → String → TokenParams → Segment Raw → Response
pipelineEncrypted key iv secret tp = serveSeg ∘ signSeg secret tp ∘ encryptSeg key iv

-- There is no pipeline that produces Response from Segment Raw directly.
```

### Guarantee 4: Key-segment correspondence — no mismatch

**Problem:** Segment N must be encrypted with key `N / keyPeriod`. Using the
wrong key = silent corruption (decryption produces garbage, player shows
black frames or errors). This is especially tricky with key rotation.

**Agda solution:**

```agda
-- Key period as a compile-time constant (or a parameter)
KeyPeriod : ℕ
KeyPeriod = 10

-- Key indexed by its period number
record AESKey (period : ℕ) : Set where
  field
    keyBytes : String
    ivBytes  : String

-- Encrypt requires a PROOF that the segment belongs to the key's period.
-- The proof is: segIndex / KeyPeriod ≡ period
encryptWithKey : ∀ {p : ℕ}
  → AESKey p
  → (seg : Segment Raw)
  → segIndex seg / KeyPeriod ≡ p    -- proof of correspondence
  → Segment Encrypted

-- In practice, the proof is computed automatically:
-- given segIndex = 15, KeyPeriod = 10, period = 1:
-- 15 / 10 = 1 ≡ 1 → refl (trivially satisfied)
--
-- But if you pass the wrong key (period 0 for segment 15),
-- 15 / 10 = 1 ≢ 0 → does not type-check.

-- Key table: lookup returns a key indexed by the correct period
lookupKey : (idx : ℕ) → KeyTable → Maybe (AESKey (idx / KeyPeriod))
```

**What this prevents:** Encrypting segment 15 with the key for period 0 —
the proof obligation `15 / 10 ≡ 0` is `1 ≡ 0`, which is uninhabited.
The code doesn't compile.

**Pragmatic note:** This level of proof may be overkill for a first implementation.
A simpler version without the proof term but with the indexed `AESKey p` type
still catches most mistakes — you'd need to explicitly construct a wrong-period
key, which is harder than accidentally passing the wrong index.

### Guarantee 5: Single PRNG for delivery and detection

**Problem:** The A/B variant selection (delivery) and the leak detection
(analysis) must use the EXACT same PRNG. If they diverge — different constants,
different iteration count, off-by-one — an innocent user gets blamed.

This is a real risk when delivery is in Haskell and detection is in Python
(data science tool). Two implementations of the same algorithm will eventually
diverge.

**Agda solution:**

This is the same `selectVariant` and `matchScore` defined in Variant.agda above.
The definitions live in one place and are used by both the delivery server
(MAlonzo → Haskell binary) and the leak detection tool.

**What this guarantees:**
- `selectVariant` is compiled to Haskell via MAlonzo → used on the server.
- The same `selectVariant` can be compiled to JS via `agda --js` → used in
  a browser-based admin tool (if needed).
- Leak detection calls `userSequence` — the same function, not a reimplementation.
- If you change `variantPrime`, both delivery and detection change simultaneously.
- No "Python version uses `(segIdx + 1)` but Haskell version uses `segIdx`" bugs.
- Word64 arithmetic ensures O(1) multiply/mod — no Peano overhead.

### Guarantee 6: Playback session as Agent (optional)

If rate limiting and abuse detection are added to the video server, the session
becomes stateful: track which segments were served, when, to whom. This maps
naturally to the existing Agent coalgebra.

```agda
record SessionState : Set where
  field
    lastServed    : ℕ          -- highest segment index served
    servedCount   : ℕ          -- total segments served in this session
    windowStart   : ℕ          -- timestamp of rate limit window start
    windowCount   : ℕ          -- requests in current window

data SessionInput : Set where
  RequestSegment : ℕ → SessionInput       -- segment index
  ResetWindow    : ℕ → SessionInput       -- new window timestamp
  Expire         : SessionInput

data SessionOutput : Set where
  Allowed   : ℕ → SessionOutput           -- segment index to serve
  RateLimited : SessionOutput
  SessionExpired : SessionOutput

videoSession : Agent SessionState SessionInput SessionOutput
videoSession = record
  { state   = initialSession
  ; observe = λ s → if expired s then SessionExpired else Allowed (lastServed s)
  ; step    = λ s i → case i of
      RequestSegment idx →
        if windowCount s ≥ maxRate
        then record s { }                          -- state unchanged, observe → RateLimited
        else record s { lastServed = idx
                      ; servedCount = suc (servedCount s)
                      ; windowCount = suc (windowCount s) }
      ResetWindow t → record s { windowStart = t ; windowCount = 0 }
      Expire → expiredState
  }
```

**How it integrates with the HTTP flow:**

The session agent runs per-user (keyed by userId from the token). The router
consults it before serving a segment:

```agda
-- In the router, inside InternalValidate handler (after token is validated):

-- Session map: userId → wired Agent IO interface
-- Stored in ServerState, created lazily on first request per user.
record SessionIO : Set where
  field
    sessionObserve : IO String
    sessionStep    : String → IO String

-- On segment request:
--   1. Look up or create session for this userId
--   2. Step the agent with RequestSegment segIdx
--   3. Check output: Allowed → serve, RateLimited → 429

handleSegmentWithSession : ServerState → ℕ → ℕ → IO HttpResponse
handleSegmentWithSession st userId segIdx =
  getOrCreateSession st userId >>= λ session →
  sessionStep session (showNat segIdx) >>= λ output →
  case parseSessionOutput output of
    Allowed _      → pure (mkResponseH 200 "" (variantHeader ∷ []))
    RateLimited    → pure (mkResponse 429 "Rate limited")
    SessionExpired → pure (mkResponse 403 "Session expired")
```

Sessions are wired via existing `wireAgent`:
```agda
createSession : ℕ → IO SessionIO
createSession userId =
  let totalSegs = 1000  -- max expected; or read from meta
      agent = videoSession totalSegs
  in wireAgent ("session-" ++ showNat userId) "/session" agent >>= λ def →
     pure (record { sessionObserve = agentObserve def
                  ; sessionStep = agentStep def })
```

The session map (`IORef (List (ℕ × SessionIO))`) is stored in `ServerState`.
Sessions expire via the `Expire` input (sent by a periodic cleanup, or
on timeout detected during the next request).

This is **optional** — the server works without session agents (HMAC tokens
alone provide auth). Sessions add rate limiting and sequential access enforcement
as an extra layer.

### What stays in Haskell (thin FFI layer only)

| hs/ module | What it provides | Why not Agda |
|---|---|---|
| Crypto.hs | `hmacSHA256`, `aesEncryptCBC`, `aesDecryptCBC` | cryptonite API is deeply Haskell-idiomatic (ByteArray class, ScrubbedBytes). Thin postulate wrappers. |
| Video/Transcode.hs | `runFfmpeg : [String] → IO ExitCode` | Complex shell argument construction. Could be Agda, but low value — no invariants to protect in "build ffmpeg command line". |
| Http.hs (existing) | `serve`, `Request`, `Response` | Already exists. Only change: add `reqHeaders` field. |

Everything else — routing, token logic, variant selection, manifest generation,
session agent, leak detection — is Agda.

### FFI bindings

The bindings needed for the video server, following the project convention
(`postulate` + `COMPILE GHC`):

```agda
-- src/Agdelte/FFI/Crypto.agda
module Agdelte.FFI.Crypto where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.IO using (IO)

{-# FOREIGN GHC import qualified Agdelte.Crypto as Crypto #-}

-- HMAC-SHA256: secret (hex) × message → hex digest
postulate hmacSHA256 : String → String → String
{-# COMPILE GHC hmacSHA256 = Crypto.hmacSHA256 #-}

-- AES-128-CBC encrypt: key (base64) × iv (base64) × plaintext (base64) → ciphertext (base64)
postulate aesEncrypt : String → String → String → String
{-# COMPILE GHC aesEncrypt = Crypto.aesEncryptCBC #-}

-- AES-128-CBC decrypt
postulate aesDecrypt : String → String → String → String
{-# COMPILE GHC aesDecrypt = Crypto.aesDecryptCBC #-}

-- Generate N random bytes, return as base64
postulate randomBytes : ℕ → IO String
{-# COMPILE GHC randomBytes = Crypto.randomBytesB64 #-}
```

```agda
-- src/Agdelte/FFI/Word.agda
module Agdelte.FFI.Word where

{-# FOREIGN GHC import Data.Word (Word64) #-}

postulate Word64 : Set
{-# COMPILE GHC Word64 = type Word64 #-}

postulate
  w64zero    : Word64
  w64fromNat : ℕ → Word64
  w64toNat   : Word64 → ℕ
  _*w_       : Word64 → Word64 → Word64
  _modw_     : Word64 → Word64 → Word64
  _andw_     : Word64 → Word64 → Word64
  oddw       : Word64 → Bool

-- All trivial COMPILE GHC pragmas (fromIntegral, mod, .&., odd)
```

```agda
-- src/Agdelte/FFI/Time.agda
module Agdelte.FFI.Time where

postulate getPosixTime : IO ℕ   -- seconds since epoch
{-# COMPILE GHC getPosixTime = fmap (round . nominalDiffTimeToSeconds) getPOSIXTime #-}
```

With these bindings, PRNG arithmetic uses `Word64` (O(1) multiply/mod),
strings use Agda's `String` (compiled to `Text` by MAlonzo), and crypto
operations delegate to cryptonite without Agda seeing the internals.

### Performance notes

MAlonzo compiles Agda to GHC Haskell. The generated code is normal Haskell
with normal GHC optimizations. The key is to avoid performance traps:

| Trap | Fix | Where |
|---|---|---|
| Peano ℕ for arithmetic | `Word64` bindings for hot-path math | Variant.agda (PRNG), Token.agda (expiry comparison) |
| `List Char` string concat | Use `String` (= `Text` via MAlonzo) | Everywhere — this is the default, already fine |
| Linked-list traversal for key lookup | `postulate` for `Map` or array-index lookup | Key table in Segment.agda |
| Lazy thunks piling up | `{-# COMPILE GHC ... = ... $! ... #-}` strict bindings where needed | Session agent state updates |

Warp handles ~25 000 req/s on simple handlers — comparable to nginx for
dynamic requests. The MAlonzo-compiled token validation adds microseconds
per request, which is negligible at this scale. The bindings are cheap to
add and prevent surprises if the workload grows.

### Required changes to Agdelte infrastructure

**1. Headers in `Http.Request`** (needed for Cookie, X-Original-URI):

```haskell
-- hs/Agdelte/Http.hs — extend Request:
data Request = Request
  { reqMethod  :: Text
  , reqPath    :: Text
  , reqBody    :: Text
  , reqHeaders :: [(Text, Text)]   -- NEW: all request headers
  }
```

```haskell
-- In toWaiApp, populate reqHeaders:
reqHeaders = map (\(k,v) -> (TE.decodeUtf8With lenientDecode (CI.original k),
                              TE.decodeUtf8With lenientDecode v))
                 (Wai.requestHeaders waiReq)
```

Backward-compatible: existing Agda FFI only accesses `reqMethod`, `reqPath`,
`reqBody`. Add to `Server.agda`:

```agda
postulate
  reqHeaders : HttpRequest → List (String × String)
{-# COMPILE GHC reqHeaders = \req -> map (\(k,v) -> (k,v)) (Http.reqHeaders req) #-}
```

**2. Response with headers** from Agda (currently `mkResponse` discards headers):

```agda
postulate
  mkResponseH : Nat → String → List (String × String) → HttpResponse

{-# FOREIGN GHC
  mkResponseHImpl :: Integer -> T.Text -> [(T.Text, T.Text)] -> AgdaResponse
  -- needs a new AgdaResponse type that carries headers, or extend existing one
  #-}
```

Alternatively, extend `AgdaResponse` to include headers:
```haskell
data AgdaResponse = AgdaResponse Integer T.Text [(T.Text, T.Text)]
```
And update `listenImpl` to pass headers through to `Http.Response`.

**3. New FFI modules** (Crypto.agda, Word.agda, Time.agda, FileSystem.agda):

These are new files, not changes to existing ones. They add `COMPILE GHC`
postulates for the Haskell libraries needed by the video server. No existing
code is modified.

**4. `hs/Agdelte/Crypto.hs`** — new file with thin cryptonite wrappers:

```haskell
module Agdelte.Crypto (hmacSHA256, aesEncryptCBC, aesDecryptCBC, randomBytesB64) where
-- ~50 lines total: import cryptonite, wrap each function to operate on Text (base64)
```

No other infrastructure changes. The video server is a new binary that uses
existing `listen` from `Server.agda` and the new Agda modules.

## Implementation order

1. **Layer 1** — built into player from day one (MediaSource architecture).
   Comes for free with the `mediaSourceInit`/`mediaSourceAppend` Cmd approach.

2. **Layer 2** — signed URLs, implement with backend integration.
   Agda-side: `pcSignUrl` field in PlayerConfig, `ProtectionError`/`TokenRefreshed`
   messages. Small surface area.

3. **Layer 3** — AES-128 encryption, after segment delivery is stable.
   Requires: `decryptAES128` Task primitive, `fetchKey` Task, key caching in JS runtime.
   Manifest parser must extract `#EXT-X-KEY` URIs.

4. **Layer 4** — watermarking, independent track, can be added anytime.
   Zero player-side changes. Server-side only: transcode pipeline + PRNG variant selection.

5. **Layer 5** — UI deterrence, trivial to add, low priority.
   Requires: `onPreventDefault` Attr constructor (useful generally), devtools detection
   postulate (optional). Can be added to any existing player without config changes.

## What we explicitly do NOT do

- No Widevine/FairPlay integration (requires hardware, licensing, CDM binaries).
- No obfuscated JavaScript "security" (security through obscurity, trivially bypassed).
- No disabling screenshots/screen recording (OS-level, impossible from browser).

## Dependencies

- Player must use `MediaSource API` (see DESIGN.md) — prerequisite for layers 2–3.
- Backend must support signed URL generation and key serving endpoints.
- Watermarking (layer 4) is part of the admin transcoding pipeline.

### Agda/runtime dependencies per layer

| Layer | New Agda types | New Cmd/Task | New JS runtime code | New Attr |
|---|---|---|---|---|
| 1 | — | `mediaSourceInit`, `mediaSourceAppend`, `mediaSourceEnd` | MediaSource manager | — |
| 2 | `pcSignUrl` field | — (uses existing `httpGet`) | — | — |
| 3 | `pcKeyEndpoint` field | `decryptAES128` Task | `crypto.subtle` wrapper, key cache | — |
| 4 | — | — | — | — |
| 5 | — | — | devtools detection (optional) | `onPreventDefault` |
