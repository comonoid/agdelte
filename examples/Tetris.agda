{-# OPTIONS --without-K #-}

-- Tetris: chord-based controls with all 10 fingers
-- Position: A S D F G H J K L ; → columns 0–9
-- Rotation: C + M thumb chord (2 bits → 4 orientations)
-- Alternative: arrow keys for beginners
-- No hard drop — piece falls by gravity, speed increases with level

module Tetris where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; const)

open import Agdelte.Core.Event
open import Agdelte.Core.Cmd using (Cmd; ε)
open import Agdelte.Reactive.Node hiding (onKeyDown; onKeyUp)
open import Agdelte.Css.Decl using (Style; _∶_; _<>_; toAttrs)

------------------------------------------------------------------------
-- Game engine (JS FFI)
-- All game logic lives in a single JS IIFE assigned to globalThis._T
-- Individual postulates delegate to it
------------------------------------------------------------------------

-- Initialize engine + return empty 200-cell board
postulate initEngine : List ℕ

{-# COMPILE JS initEngine = (() => {
  const B = [
    [[[1,0],[1,1],[1,2],[1,3]],[[0,0],[1,0],[2,0],[3,0]],[[2,0],[2,1],[2,2],[2,3]],[[0,0],[1,0],[2,0],[3,0]]],
    [[[0,0],[0,1],[1,0],[1,1]],[[0,0],[0,1],[1,0],[1,1]],[[0,0],[0,1],[1,0],[1,1]],[[0,0],[0,1],[1,0],[1,1]]],
    [[[0,1],[1,0],[1,1],[1,2]],[[0,0],[1,0],[1,1],[2,0]],[[1,0],[1,1],[1,2],[2,1]],[[0,1],[1,0],[1,1],[2,1]]],
    [[[0,1],[0,2],[1,0],[1,1]],[[0,0],[1,0],[1,1],[2,1]],[[1,1],[1,2],[2,0],[2,1]],[[0,0],[1,0],[1,1],[2,1]]],
    [[[0,0],[0,1],[1,1],[1,2]],[[0,1],[1,0],[1,1],[2,0]],[[1,0],[1,1],[2,1],[2,2]],[[0,1],[1,0],[1,1],[2,0]]],
    [[[0,0],[1,0],[1,1],[1,2]],[[0,0],[0,1],[1,0],[2,0]],[[1,0],[1,1],[1,2],[2,2]],[[0,1],[1,1],[2,0],[2,1]]],
    [[[0,2],[1,0],[1,1],[1,2]],[[0,0],[1,0],[2,0],[2,1]],[[1,0],[1,1],[1,2],[2,0]],[[0,0],[0,1],[1,1],[2,1]]]
  ];
  const C = ['#1a1a2e','#00f0f0','#f0f000','#a000f0','#00f000','#f00000','#0000f0','#f0a000','#333','#ffffff'];
  const PK = {KeyA:0,KeyS:1,KeyD:2,KeyF:3,KeyG:4,KeyH:5,KeyJ:6,KeyK:7,KeyL:8,Semicolon:9};
  function col(board,t,r,row,co) {
    const bl = B[Number(t)][Number(r)];
    for (const [br,bc] of bl) {
      const rr = Number(row)+br, cc = Number(co)+bc;
      if (rr<0||rr>=20||cc<0||cc>=10) return true;
      if (board[rr*10+cc] !== 0n) return true;
    }
    return false;
  }
  function pl(board,t,r,row,co,color) {
    const res = [...board], bl = B[Number(t)][Number(r)];
    for (const [br,bc] of bl) {
      const rr = Number(row)+br, cc = Number(co)+bc;
      if (rr>=0&&rr<20&&cc>=0&&cc<10) res[rr*10+cc] = color;
    }
    return res;
  }
  function gh(board,t,r,row,co) {
    let rr = Number(row);
    while (!col(board,t,r,BigInt(rr+1),co)) rr++;
    return BigInt(rr);
  }
  function disp(board,t,r,row,co) {
    const gr = gh(board,t,r,row,co);
    let res = pl(board,t,r,gr,co,8n);
    return pl(res,t,r,row,co,BigInt(Number(t)+1));
  }
  function clr(board) {
    const rows = []; let cleared = 0;
    for (let i=0;i<20;i++) {
      const row = board.slice(i*10,(i+1)*10);
      if (row.every(c => c!==0n)) cleared++; else rows.push(row);
    }
    while (rows.length<20) rows.unshift(new Array(10).fill(0n));
    return mkP(rows.flat(), BigInt(cleared));
  }
  function nR(s) { return (s*1664525n+1013904223n)&0xFFFFFFFFn; }
  function shuf(seed) {
    const bag = [0n,1n,2n,3n,4n,5n,6n]; let s = seed;
    for (let i=6;i>0;i--) { s=nR(s); const j=Number(s%BigInt(i+1)); [bag[i],bag[j]]=[bag[j],bag[i]]; }
    return {bag,seed:s};
  }
  function pop(bag,seed) {
    if (bag.length<1) { const r=shuf(seed); bag=r.bag; seed=r.seed; }
    return mkP(mkP(bag.slice(1),bag[0]),seed);
  }
  function prev(type) {
    const res = new Array(16).fill(0n);
    const bl = B[Number(type)][0], color = BigInt(Number(type)+1);
    for (const [r,c] of bl) res[r*4+c] = color;
    return res;
  }
  function mkP(a,b) { return {"_,_": c => c["_,_"](a,b)}; }
  globalThis._T = {
    col, pl, gh, disp, clr, shuf, pop, prev, mkP,
    spCol: t => {
      const bl=B[Number(t)][0];
      const maxC=Math.max(...bl.map(([_,c])=>c));
      return BigInt(Math.floor((10-maxC-1)/2));
    },
    scFor: (l,lv) => ([0n,100n,300n,500n,800n][Number(l)]||0n)*(lv+1n),
    tkMs: lv => { const ms=800n-lv*70n; return ms<100n?100n:ms; },
    gTicks: lv => { const ms=Number(800n-lv*70n); const t=Math.max(1,Math.round(ms/100)); return BigInt(t); },
    cStr: n => C[Number(n)]||C[0],
    pCol: k => k in PK ? BigInt(PK[k]) : 99n,
    isPos: k => k in PK,
    isTh: k => k==='KeyC'||k==='KeyM',
    dRot: keys => {
      let c=false,m=false;
      for (const k of keys) { if(k==='KeyC')c=true; if(k==='KeyM')m=true; }
      return c&&m?3n:m?2n:c?1n:0n;
    },
    adjC: (t,r,tc) => {
      const bl=B[Number(t)][Number(r)];
      const maxC=Math.max(...bl.map(([_,c])=>c));
      return BigInt(Math.max(0,Math.min(Number(tc),9-maxC)));
    },
    bestC: (board,t,r,row,cur,tgt) => {
      if (!col(board,t,r,row,tgt)) return tgt;
      const step = Number(tgt)>Number(cur) ? 1 : -1;
      let best = cur, c = Number(cur)+step;
      const end = Number(tgt);
      while (step>0 ? c<=end : c>=end) {
        if (!col(board,t,r,row,BigInt(c))) { best=BigInt(c); c+=step; }
        else break;
      }
      return best;
    },
    unfl: (board,c) => board.map(v => v===9n ? c : v),
    markR: board => {
      const res=[...board];
      for(let i=0;i<20;i++){const r=board.slice(i*10,(i+1)*10);if(r.every(v=>v!==0n))for(let j=0;j<10;j++)res[i*10+j]=9n;}
      return res;
    },
    hasR: board => { for(let i=0;i<20;i++){if(board.slice(i*10,(i+1)*10).every(v=>v!==0n))return true;} return false; },
    xorR: (cur,k) => k==='KeyC' ? cur^1n : k==='KeyM' ? cur^2n : cur,
    digK: k => { const m=k.match(/^Digit(\d)$/); return m ? BigInt(m[1]) : 99n; },
    addK: (k,keys) => keys.includes(k)?keys:[k,...keys],
    rmK: (k,keys) => keys.filter(x=>x!==k)
  };
  return new Array(200).fill(0n);
})() #-}

-- Time-based seed (evaluated once at module load)
postulate timeSeed : ℕ
{-# COMPILE JS timeSeed = BigInt(Date.now()) #-}

-- Game functions (delegate to globalThis._T)
postulate
  collides'     : List ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  placePiece'   : List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ
  mergeDisplay' : List ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ
  clearLines'   : List ℕ → List ℕ × ℕ
  popBag'       : List ℕ → ℕ → (List ℕ × ℕ) × ℕ
  previewBoard' : ℕ → List ℕ
  spawnCol'     : ℕ → ℕ
  scoreFor'     : ℕ → ℕ → ℕ
  tickInterval' : ℕ → ℕ
  gravityTicks' : ℕ → ℕ
  colorStr'     : ℕ → String
  posColumn'    : String → ℕ
  isPositionKey' : String → Bool
  isThumbKey'    : String → Bool
  decodeRot'    : List String → ℕ
  adjustCol'    : ℕ → ℕ → ℕ → ℕ
  bestCol'      : List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  toggleRot'    : ℕ → String → ℕ
  digitKey'     : String → ℕ
  unflash'      : List ℕ → ℕ → List ℕ
  markFullRows' : List ℕ → List ℕ
  hasFullRows'  : List ℕ → Bool
  addKey'       : String → List String → List String
  removeKey'    : String → List String → List String
  natDiv        : ℕ → ℕ → ℕ

{-# COMPILE JS collides'     = b=>t=>r=>row=>co => globalThis._T.col(b,t,r,row,co) #-}
{-# COMPILE JS placePiece'   = b=>t=>r=>row=>co=>c => globalThis._T.pl(b,t,r,row,co,c) #-}
{-# COMPILE JS mergeDisplay' = b=>t=>r=>row=>co => globalThis._T.disp(b,t,r,row,co) #-}
{-# COMPILE JS clearLines'   = b => globalThis._T.clr(b) #-}
{-# COMPILE JS popBag'       = b=>s => globalThis._T.pop(b,s) #-}
{-# COMPILE JS previewBoard' = t => globalThis._T.prev(t) #-}
{-# COMPILE JS spawnCol'     = t => globalThis._T.spCol(t) #-}
{-# COMPILE JS scoreFor'     = l=>lv => globalThis._T.scFor(l,lv) #-}
{-# COMPILE JS tickInterval' = lv => globalThis._T.tkMs(lv) #-}
{-# COMPILE JS gravityTicks' = lv => globalThis._T.gTicks(lv) #-}
{-# COMPILE JS colorStr'     = n => globalThis._T.cStr(n) #-}
{-# COMPILE JS posColumn'    = k => globalThis._T.pCol(k) #-}
{-# COMPILE JS isPositionKey' = k => globalThis._T.isPos(k) #-}
{-# COMPILE JS isThumbKey'   = k => globalThis._T.isTh(k) #-}
{-# COMPILE JS decodeRot'    = ks => globalThis._T.dRot(ks) #-}
{-# COMPILE JS adjustCol'    = t=>r=>tc => globalThis._T.adjC(t,r,tc) #-}
{-# COMPILE JS bestCol'      = b=>t=>r=>row=>cur=>tgt => globalThis._T.bestC(b,t,r,row,cur,tgt) #-}
{-# COMPILE JS toggleRot'    = cur=>k => globalThis._T.xorR(cur,k) #-}
{-# COMPILE JS digitKey'     = k => globalThis._T.digK(k) #-}
{-# COMPILE JS unflash'      = b=>c => globalThis._T.unfl(b,c) #-}
{-# COMPILE JS markFullRows' = b => globalThis._T.markR(b) #-}
{-# COMPILE JS hasFullRows'  = b => globalThis._T.hasR(b) #-}
{-# COMPILE JS addKey'       = k=>ks => globalThis._T.addK(k,ks) #-}
{-# COMPILE JS removeKey'    = k=>ks => globalThis._T.rmK(k,ks) #-}
{-# COMPILE JS natDiv        = a=>b => b===0n ? 0n : a/b #-}

-- Fixed-size index lists for foreach (constant, never changes → no DOM recreation)
postulate boardIndices   : List ℕ
postulate previewIndices : List ℕ
postulate boardCellColor : ℕ → List ℕ → String

{-# COMPILE JS boardIndices   = Array.from({length:200}, (_,i) => BigInt(i)) #-}
{-# COMPILE JS previewIndices = Array.from({length:16}, (_,i) => BigInt(i)) #-}
{-# COMPILE JS boardCellColor = i => board => globalThis._T.cStr(board[Number(i)] ?? 0n) #-}

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    board      : List ℕ       -- 200 cells (20 rows × 10 cols), 0=empty 1–7=piece color
    pieceType  : ℕ             -- 0–6: I O T S Z J L
    pieceRot   : ℕ             -- 0–3
    pieceRow   : ℕ             -- row of bounding box top
    pieceCol   : ℕ             -- column of bounding box left
    next1      : ℕ             -- next piece type
    next2      : ℕ             -- second preview piece type
    bag        : List ℕ        -- remaining pieces in 7-bag
    score      : ℕ
    level      : ℕ
    linesTotal : ℕ
    gameState  : ℕ             -- 0=menu, 1=playing, 2=gameover, 3=paused
    lockTimer  : ℕ             -- ticks spent on ground
    seed       : ℕ             -- PRNG state
    heldKeys   : List String   -- currently pressed key codes
    startLevel : ℕ             -- chosen starting level (0–9)
    animTimer  : ℕ             -- animation ticks remaining
    gravCount  : ℕ             -- base ticks until next gravity step

open Model public

initialModel : Model
initialModel = mkModel initEngine 0 0 0 3 0 0 [] 0 0 0 0 0 timeSeed [] 0 0 0

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  Tick    : Msg
  KeyDown : String → Msg
  KeyUp   : String → Msg

------------------------------------------------------------------------
-- Rotation helper
------------------------------------------------------------------------

nextRot : ℕ → ℕ
nextRot 0 = 1
nextRot 1 = 2
nextRot 2 = 3
nextRot _ = 0

------------------------------------------------------------------------
-- Update helpers
------------------------------------------------------------------------

lockDelay : ℕ
lockDelay = 5

-- Try to move/rotate piece; if valid, apply + reset lock timer
tryMoveTo : Model → ℕ → ℕ → Model
tryMoveTo m col rot =
  if not (collides' (board m) (pieceType m) rot (pieceRow m) col)
  then record m { pieceCol = col ; pieceRot = rot ; lockTimer = 0 }
  else m

-- Start lock animation: place piece with flash color (9)
startLockAnim : Model → Model
startLockAnim m =
  let flashBoard = placePiece' (board m) (pieceType m) (pieceRot m)
                               (pieceRow m) (pieceCol m) 9
  in record m { board = flashBoard ; gameState = 4 ; animTimer = 1 }

-- Spawn next piece (used after animation finishes)
spawnNext : Model → Model
spawnNext m =
  let bagResult = popBag' (bag m) (seed m)
      newBag    = proj₁ (proj₁ bagResult)
      nextPiece = proj₂ (proj₁ bagResult)
      newSeed   = proj₂ bagResult
      newType   = next1 m
      newCol    = spawnCol' newType
  in if collides' (board m) newType 0 0 newCol
     then record m { gameState = 2 }
     else record m { pieceType  = newType
                   ; pieceRot   = 0
                   ; pieceRow   = 0
                   ; pieceCol   = newCol
                   ; next1      = next2 m
                   ; next2      = nextPiece
                   ; bag        = newBag
                   ; lockTimer  = 0
                   ; seed       = newSeed
                   ; heldKeys   = []
                   ; gameState  = 1
                   ; animTimer  = 0
                   ; gravCount  = gravityTicks' (level m) }

-- Finish lock flash: unflash, check for line clears
finishLockAnim : Model → Model
finishLockAnim m =
  let realBoard = unflash' (board m) (suc (pieceType m))
  in if hasFullRows' realBoard
     then record m { board = markFullRows' realBoard ; gameState = 5 ; animTimer = 1 }
     else let result   = clearLines' realBoard
              newBoard = proj₁ result
              cleared  = proj₂ result
              newScore = score m + scoreFor' cleared (level m)
              newLines = linesTotal m + cleared
              newLevel = startLevel m + natDiv newLines 10
          in spawnNext (record m { board = newBoard ; score = newScore
                                 ; linesTotal = newLines ; level = newLevel })

-- Finish line clear flash: remove lines, spawn
finishClearAnim : Model → Model
finishClearAnim m =
  let realBoard = unflash' (board m) (suc (pieceType m))
      result    = clearLines' realBoard
      newBoard  = proj₁ result
      cleared   = proj₂ result
      newScore  = score m + scoreFor' cleared (level m)
      newLines  = linesTotal m + cleared
      newLevel  = natDiv newLines 10
  in spawnNext (record m { board = newBoard ; score = newScore
                         ; linesTotal = newLines ; level = newLevel })

-- Base tick (50ms). Gravity uses counter; animation uses animTimer.
handleTick : Model → Model
handleTick m =
  if gameState m ≡ᵇ 4
  then (if animTimer m ≡ᵇ 0 then finishLockAnim m
        else record m { animTimer = animTimer m ∸ 1 })
  else if gameState m ≡ᵇ 5
  then (if animTimer m ≡ᵇ 0 then finishClearAnim m
        else record m { animTimer = animTimer m ∸ 1 })
  else if not (gameState m ≡ᵇ 1) then m
  else if not (gravCount m ≡ᵇ 0)
  then record m { gravCount = gravCount m ∸ 1 }
  else gravityStep (record m { gravCount = gravityTicks' (level m) })
  where
    gravityStep : Model → Model
    gravityStep m' =
      if not (collides' (board m') (pieceType m') (pieceRot m') (suc (pieceRow m')) (pieceCol m'))
      then record m' { pieceRow = suc (pieceRow m') ; lockTimer = 0 }
      else if not (lockTimer m' <ᵇ lockDelay)
      then startLockAnim m'
      else record m' { lockTimer = suc (lockTimer m') }

-- Start a new game
startNewGame : Model → Model
startNewGame m = go (popBag' [] (seed m))
  where
    go : (List ℕ × ℕ) × ℕ → Model
    go r0 =
      let bag0 = proj₁ (proj₁ r0)
          p0   = proj₂ (proj₁ r0)
          s0   = proj₂ r0
          r1   = popBag' bag0 s0
          bag1 = proj₁ (proj₁ r1)
          p1   = proj₂ (proj₁ r1)
          s1   = proj₂ r1
          r2   = popBag' bag1 s1
          bag2 = proj₁ (proj₁ r2)
          p2   = proj₂ (proj₁ r2)
          s2   = proj₂ r2
      in mkModel initEngine p0 0 0 (spawnCol' p0) p1 p2 bag2
                 0 (startLevel m) 0 1 0 s2 [] (startLevel m) 0
                 (gravityTicks' (startLevel m))

-- Arrow key helpers
postulate
  isArrowLeft'  : String → Bool
  isArrowRight' : String → Bool
  isArrowUp'    : String → Bool
  isEnterKey'   : String → Bool
  isEscKey'     : String → Bool

{-# COMPILE JS isArrowLeft'  = k => k === 'ArrowLeft' #-}
{-# COMPILE JS isArrowRight' = k => k === 'ArrowRight' #-}
{-# COMPILE JS isArrowUp'    = k => k === 'ArrowUp' #-}
{-# COMPILE JS isEnterKey'   = k => k === 'Enter' #-}
{-# COMPILE JS isEscKey'     = k => k === 'Escape' #-}

postulate moveLeft' : ℕ → ℕ
{-# COMPILE JS moveLeft' = c => { const r = c - 1n; return r < 0n ? 0n : r; } #-}

-- Handle key during play
handlePlayKey : String → Model → Model
handlePlayKey k m = handlePlayKey' (record m { heldKeys = addKey' k (heldKeys m) })
  where
    movePos : Model → Model
    movePos m' =
      let tgt = adjustCol' (pieceType m') (pieceRot m') (posColumn' k)
          c   = bestCol' (board m') (pieceType m') (pieceRot m') (pieceRow m') (pieceCol m') tgt
      in record m' { pieceCol = c ; lockTimer = 0 }

    doToggle : Model → Model
    doToggle m' =
      let newRot = toggleRot' (pieceRot m') k
      in tryMoveTo m' (adjustCol' (pieceType m') newRot (pieceCol m')) newRot

    handlePlayKey' : Model → Model
    handlePlayKey' m' =
      if isPositionKey' k then movePos m'
      else if isThumbKey' k then doToggle m'
      else if isArrowLeft' k then tryMoveTo m' (moveLeft' (pieceCol m')) (pieceRot m')
      else if isArrowRight' k then tryMoveTo m' (suc (pieceCol m')) (pieceRot m')
      else if isArrowUp' k then tryMoveTo m' (pieceCol m') (nextRot (pieceRot m'))
      else m'

-- Handle key press
handleKeyDown : String → Model → Model
handleKeyDown k m =
  if gameState m ≡ᵇ 3
  then (if isEscKey' k then record m { gameState = 1 } else m)
  else if gameState m ≡ᵇ 1
  then (if isEscKey' k then record m { gameState = 3 } else handlePlayKey k m)
  else (if isEnterKey' k then startNewGame m
        else let d = digitKey' k
             in if d <ᵇ 10 then record m { startLevel = d } else m)

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel Tick m          = handleTick m
updateModel (KeyDown k) m   = handleKeyDown k m
updateModel (KeyUp k) m     = record m { heldKeys = removeKey' k (heldKeys m) }

------------------------------------------------------------------------
-- Display helpers
------------------------------------------------------------------------

displayBoardFn : Model → List ℕ
displayBoardFn m =
  if gameState m ≡ᵇ 0 then initEngine
  else if gameState m ≡ᵇ 4 then board m
  else if gameState m ≡ᵇ 5 then board m
  else if gameState m ≡ᵇ 2 then board m
  else if gameState m ≡ᵇ 3 then board m
  else mergeDisplay' (board m) (pieceType m) (pieceRot m) (pieceRow m) (pieceCol m)

preview1Fn : Model → List ℕ
preview1Fn m = previewBoard' (next1 m)

preview2Fn : Model → List ℕ
preview2Fn m = previewBoard' (next2 m)

scoreStr : Model → String
scoreStr m = show (score m)

levelStr : Model → String
levelStr m = show (level m)

linesStr : Model → String
linesStr m = show (linesTotal m)

isMenu : Model → Bool
isMenu m = gameState m ≡ᵇ 0

isGameOver : Model → Bool
isGameOver m = gameState m ≡ᵇ 2

isPaused : Model → Bool
isPaused m = gameState m ≡ᵇ 3

menuText : Model → String
menuText m = "Level: " ++ show (startLevel m) ++ " (0-9)\nPress Enter to start"

gameOverText : Model → String
gameOverText m = "Game Over\nScore: " ++ show (score m) ++ "\nLevel: " ++ show (startLevel m) ++ " (0-9)\nPress Enter"

------------------------------------------------------------------------
-- Styles (inline, following Todo/Keyboard pattern)
------------------------------------------------------------------------

gameStyle : Style
gameStyle =
    "display"         ∶ "flex"
  ∷ "gap"             ∶ "24px"
  ∷ "justify-content" ∶ "center"
  ∷ "align-items"     ∶ "flex-start"
  ∷ "padding"         ∶ "20px"
  ∷ "font-family"     ∶ "monospace"
  ∷ "color"           ∶ "#e0e0e0"
  ∷ "user-select"     ∶ "none"
  ∷ []

boardStyle : Style
boardStyle =
    "display"               ∶ "grid"
  ∷ "grid-template-columns" ∶ "repeat(10, 28px)"
  ∷ "gap"                   ∶ "1px"
  ∷ "background"            ∶ "#111"
  ∷ "border"                ∶ "2px solid #444"
  ∷ "padding"               ∶ "2px"
  ∷ []

cellStaticStyle : Style
cellStaticStyle =
    "width"            ∶ "28px"
  ∷ "height"           ∶ "28px"
  ∷ "border-radius"    ∶ "2px"
  ∷ []

sidebarStyle : Style
sidebarStyle =
    "display"        ∶ "flex"
  ∷ "flex-direction" ∶ "column"
  ∷ "gap"            ∶ "16px"
  ∷ []

previewStyle : Style
previewStyle =
    "display"               ∶ "grid"
  ∷ "grid-template-columns" ∶ "repeat(4, 20px)"
  ∷ "gap"                   ∶ "1px"
  ∷ "background"            ∶ "#111"
  ∷ "border"                ∶ "1px solid #333"
  ∷ "padding"               ∶ "2px"
  ∷ []

prevCellStaticStyle : Style
prevCellStaticStyle =
    "width"            ∶ "20px"
  ∷ "height"           ∶ "20px"
  ∷ "border-radius"    ∶ "2px"
  ∷ []

infoStyle : Style
infoStyle = "text-align" ∶ "center" ∷ []

labelStyle : Style
labelStyle =
    "margin"         ∶ "0 0 4px 0"
  ∷ "font-size"      ∶ "12px"
  ∷ "color"          ∶ "#888"
  ∷ "text-transform" ∶ "uppercase"
  ∷ []

valueStyle : Style
valueStyle =
    "font-size"   ∶ "24px"
  ∷ "font-weight" ∶ "bold"
  ∷ "margin"      ∶ "0"
  ∷ []

wrapperStyle : Style
wrapperStyle = "position" ∶ "relative" ∷ []

overlayStyle : Style
overlayStyle =
    "position"        ∶ "absolute"
  ∷ "top"             ∶ "0"
  ∷ "left"            ∶ "0"
  ∷ "right"           ∶ "0"
  ∷ "bottom"          ∶ "0"
  ∷ "display"         ∶ "flex"
  ∷ "align-items"     ∶ "center"
  ∷ "justify-content" ∶ "center"
  ∷ "background"      ∶ "rgba(0,0,0,0.7)"
  ∷ "font-size"       ∶ "20px"
  ∷ "text-align"      ∶ "center"
  ∷ "line-height"     ∶ "1.6"
  ∷ []

controlsStyle : Style
controlsStyle =
    "font-size"   ∶ "11px"
  ∷ "color"       ∶ "#666"
  ∷ "line-height" ∶ "1.6"
  ∷ "max-width"   ∶ "140px"
  ∷ []

------------------------------------------------------------------------
-- Template
------------------------------------------------------------------------

boardIndicesFn : Model → List ℕ
boardIndicesFn _ = boardIndices

previewIndicesFn : Model → List ℕ
previewIndicesFn _ = previewIndices

renderCell : ℕ → ℕ → Node Model Msg
renderCell idx _ =
  div (styleBind "background-color"
         (stringBinding (λ m → boardCellColor idx (displayBoardFn m)))
       ∷ toAttrs cellStaticStyle)
      []

renderPreview1Cell : ℕ → ℕ → Node Model Msg
renderPreview1Cell idx _ =
  div (styleBind "background-color"
         (stringBinding (λ m → boardCellColor idx (preview1Fn m)))
       ∷ toAttrs prevCellStaticStyle)
      []

renderPreview2Cell : ℕ → ℕ → Node Model Msg
renderPreview2Cell idx _ =
  div (styleBind "background-color"
         (stringBinding (λ m → boardCellColor idx (preview2Fn m)))
       ∷ toAttrs prevCellStaticStyle)
      []

tetrisTemplate : Node Model Msg
tetrisTemplate =
  div (toAttrs gameStyle)
    -- Sidebar: previews + stats
    ( div (toAttrs sidebarStyle)
        ( div (toAttrs infoStyle)
            ( h3 (toAttrs labelStyle) [ text "Next" ]
            ∷ div (toAttrs previewStyle)
                [ foreach previewIndicesFn renderPreview1Cell ]
            ∷ [] )
        ∷ div (toAttrs infoStyle)
            ( h3 (toAttrs labelStyle) [ text "Then" ]
            ∷ div (toAttrs previewStyle)
                [ foreach previewIndicesFn renderPreview2Cell ]
            ∷ [] )
        ∷ div (toAttrs infoStyle)
            ( h3 (toAttrs labelStyle) [ text "Score" ]
            ∷ p (toAttrs valueStyle) [ bindF scoreStr ]
            ∷ [] )
        ∷ div (toAttrs infoStyle)
            ( h3 (toAttrs labelStyle) [ text "Level" ]
            ∷ p (toAttrs valueStyle) [ bindF levelStr ]
            ∷ [] )
        ∷ div (toAttrs infoStyle)
            ( h3 (toAttrs labelStyle) [ text "Lines" ]
            ∷ p (toAttrs valueStyle) [ bindF linesStr ]
            ∷ [] )
        ∷ [] )
    -- Board + overlays
    ∷ div (toAttrs wrapperStyle)
        ( div (toAttrs boardStyle)
            [ foreach boardIndicesFn renderCell ]
        ∷ when isMenu
            (div (toAttrs overlayStyle) [ bindF menuText ])
        ∷ when isGameOver
            (div (toAttrs overlayStyle) [ bindF gameOverText ])
        ∷ when isPaused
            (div (toAttrs overlayStyle) [ text "Paused\nEsc to resume" ])
        ∷ [] )
    -- Controls help
    ∷ div (toAttrs controlsStyle)
        ( p [] [ text "Position (home row):" ]
        ∷ p [] [ text "A S D F G H J K L ;" ]
        ∷ p [] [ text "col 0 ← → col 9" ]
        ∷ p [] [ text "" ]
        ∷ p [] [ text "Rotation (toggle):" ]
        ∷ p [] [ text "C = ±90°" ]
        ∷ p [] [ text "M = ±180°" ]
        ∷ p [] [ text "" ]
        ∷ p [] [ text "Alt: ←→ move, ↑ rotate" ]
        ∷ p [] [ text "Esc: pause" ]
        ∷ p [] [ text "Enter: start/restart" ]
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Subscriptions
------------------------------------------------------------------------

baseTick : ℕ
baseTick = 100

subs' : Model → Event Msg
subs' _ =
  merge
    (onKeyDown (λ e → if repeat e then nothing else just (KeyDown (code e))))
    (merge
      (onKeyUp (λ e → just (KeyUp (code e))))
      (interval baseTick Tick))

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel tetrisTemplate (λ _ _ → ε) subs'
