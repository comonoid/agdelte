{-# OPTIONS --without-K #-}

-- JS postulates for the Video Player:
-- time formatting, seek/buffered percentages, volume clamping,
-- time offset, manifest parsing, JSON array access.

module Agdelte.Html.Controls.Video.Util where

open import Data.String using (String)
open import Data.Nat using (ℕ)

------------------------------------------------------------------------
-- Time formatting
------------------------------------------------------------------------

-- | Format seconds string "125.7" → "2:05"
postulate formatTime : String → String
{-# COMPILE JS formatTime = function(s) {
  var t = Math.max(0, parseFloat(s) || 0);
  var m = Math.floor(t / 60);
  var sec = Math.floor(t % 60);
  return m + ":" + (sec < 10 ? "0" : "") + sec;
} #-}

-- | Format seconds string "125.7" → "02:05" (zero-padded, shows hours when ≥ 1h)
postulate formatTimeLong : String → String
{-# COMPILE JS formatTimeLong = function(s) {
  var t = Math.max(0, parseFloat(s) || 0);
  var h = Math.floor(t / 3600);
  var m = Math.floor((t % 3600) / 60);
  var sec = Math.floor(t % 60);
  var pad = function(n) { return n < 10 ? "0" + n : "" + n; };
  if (h > 0) return pad(h) + ":" + pad(m) + ":" + pad(sec);
  return pad(m) + ":" + pad(sec);
} #-}

------------------------------------------------------------------------
-- Seek / buffered percentages
------------------------------------------------------------------------

-- | Compute seek bar percentage: currentTime / duration × 100
postulate seekPercent : String → String → String
{-# COMPILE JS seekPercent = function(cur) { return function(dur) {
  var c = parseFloat(cur) || 0, d = parseFloat(dur) || 0;
  if (d <= 0) return "0";
  return String((c / d) * 100);
}; } #-}

-- | Compute buffered percentage: bufferedEnd / duration × 100
postulate bufferedPercent : String → String → String
{-# COMPILE JS bufferedPercent = function(buf) { return function(dur) {
  var b = parseFloat(buf) || 0, d = parseFloat(dur) || 0;
  if (d <= 0) return "0";
  return String((b / d) * 100);
}; } #-}

------------------------------------------------------------------------
-- Volume / time clamping
------------------------------------------------------------------------

-- | Add offset to volume, clamped to [0, 1]
postulate offsetVolume : String → String → String
{-# COMPILE JS offsetVolume = function(cur) { return function(off) {
  var c = parseFloat(cur) || 0, o = parseFloat(off) || 0;
  return String(Math.max(0, Math.min(1, c + o)));
}; } #-}

-- | Clamp volume to [0, 1]
postulate clampVolume : String → String
{-# COMPILE JS clampVolume = function(s) {
  var v = parseFloat(s) || 0;
  return String(Math.max(0, Math.min(1, v)));
} #-}

-- | Add/subtract from time, clamped to [0, duration]
postulate offsetTime : String → String → String → String
{-# COMPILE JS offsetTime = function(cur) { return function(off) { return function(dur) {
  var c = parseFloat(cur) || 0, o = parseFloat(off) || 0, d = parseFloat(dur) || 0;
  return String(Math.max(0, Math.min(d, c + o)));
}; }; } #-}

------------------------------------------------------------------------
-- Manifest parsing
------------------------------------------------------------------------

-- | Parse .m3u8 manifest, extract segment URLs as JSON array string
postulate parseM3U8 : String → String
{-# COMPILE JS parseM3U8 = function(m3u8Text) {
  var lines = m3u8Text.split('\n');
  var segments = [];
  for (var i = 0; i < lines.length; i++) {
    if (lines[i].startsWith('#EXTINF:')) {
      if (i + 1 < lines.length && !lines[i+1].startsWith('#')) {
        segments.push(lines[i+1].trim());
      }
    }
  }
  return JSON.stringify(segments);
} #-}

-- | Extract N-th element from JSON array string (0-indexed). Returns "" if out of bounds.
postulate jsonArrayGet : String → ℕ → String
{-# COMPILE JS jsonArrayGet = function(arr) { return function(n) {
  try { var a = JSON.parse(arr); return (n < a.length) ? a[n] : ""; }
  catch(e) { return ""; }
}; } #-}

-- | Get length of JSON array string. Returns 0 on parse error.
postulate jsonArrayLength : String → ℕ
{-# COMPILE JS jsonArrayLength = function(arr) {
  try { return JSON.parse(arr).length; }
  catch(e) { return 0; }
} #-}

------------------------------------------------------------------------
-- Gesture classification
------------------------------------------------------------------------

-- | Classify a touch gesture from start/end coordinates.
-- Arguments: startX, startY, endX, endY, screenWidth
-- Returns JSON: {"gesture":"tap"|"swipe-h"|"swipe-vl"|"swipe-vr", "magnitude":"..."}
-- For swipe-h, magnitude is scaled to seek seconds (pixels / screenWidth * 60).
-- For swipe-vr/vl, magnitude is scaled to [0,1] range (pixels / screenHeight estimate).
-- Double-tap detection requires stateful tracking and is handled separately.
postulate classifyGesture : String → String → String → String → String → String
{-# COMPILE JS classifyGesture = function(sx) { return function(sy) { return function(ex) { return function(ey) { return function(sw) {
  var x0 = parseFloat(sx) || 0, y0 = parseFloat(sy) || 0;
  var x1 = parseFloat(ex) || 0, y1 = parseFloat(ey) || 0;
  var w = parseFloat(sw) || 1;
  var dx = x1 - x0, dy = y1 - y0;
  var dist = Math.sqrt(dx * dx + dy * dy);
  if (dist < 15) {
    return JSON.stringify({gesture:"tap",magnitude:""});
  }
  if (Math.abs(dx) > Math.abs(dy)) {
    var seekSec = (dx / w) * 60;
    return JSON.stringify({gesture:"swipe-h",magnitude:String(Math.round(seekSec))});
  }
  var volDelta = -dy / (w * 0.6);
  if (x0 < w / 2) {
    return JSON.stringify({gesture:"swipe-vl",magnitude:String(volDelta.toFixed(2))});
  }
  return JSON.stringify({gesture:"swipe-vr",magnitude:String(volDelta.toFixed(2))});
}; }; }; }; } #-}

-- | Extract "gesture" field from classifyGesture JSON result
postulate gestureType : String → String
{-# COMPILE JS gestureType = function(json) {
  try { return JSON.parse(json).gesture || ""; }
  catch(e) { return ""; }
} #-}

-- | Extract "magnitude" field from classifyGesture JSON result
postulate gestureMagnitude : String → String
{-# COMPILE JS gestureMagnitude = function(json) {
  try { return JSON.parse(json).magnitude || ""; }
  catch(e) { return ""; }
} #-}

------------------------------------------------------------------------
-- Touch coordinate extraction
------------------------------------------------------------------------

-- | Extract fields from comma-separated touch data.
-- touch.start format: "x,y"
-- touch.end format: "x,y,screenWidth"
postulate parseTouchX : String → String
{-# COMPILE JS parseTouchX = function(s) {
  return s.split(",")[0] || "0";
} #-}

postulate parseTouchY : String → String
{-# COMPILE JS parseTouchY = function(s) {
  return s.split(",")[1] || "0";
} #-}

postulate parseTouchScreenW : String → String
{-# COMPILE JS parseTouchScreenW = function(s) {
  return s.split(",")[2] || "0";
} #-}

