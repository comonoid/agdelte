/**
 * Video Player Tests
 *
 * Tests JS postulates (Util), state machine (update/cmd), and runtime handlers.
 * Run: node test/video.test.js
 * Prerequisite: npm run build:video (or agda --js ... examples/VideoDemo.agda)
 */

import Types from '../_build/jAgda.Agdelte.Html.Controls.Video.Types.mjs';
import Util from '../_build/jAgda.Agdelte.Html.Controls.Video.Util.mjs';
import Player from '../_build/jAgda.Agdelte.Html.Controls.Video.Player.mjs';
import Bool from '../_build/jAgda.Agda.Builtin.Bool.mjs';
import Maybe from '../_build/jAgda.Agda.Builtin.Maybe.mjs';
import agdaRTS from '../_build/agda-rts.mjs';

// ========================================
// Test runner (matches project convention)
// ========================================

let passed = 0;
let failed = 0;
const failures = [];

function test(name, fn) {
  try {
    fn();
    console.log(`  ✓ ${name}`);
    passed++;
  } catch (e) {
    console.log(`  ✗ ${name}: ${e.message}`);
    failed++;
    failures.push({ name, error: e.message });
  }
}

function assert(cond, msg = 'Assertion failed') {
  if (!cond) throw new Error(msg);
}

function assertEqual(actual, expected, msg) {
  if (actual !== expected) {
    throw new Error(msg || `Expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
  }
}

function assertClose(actual, expected, tolerance = 0.01, msg) {
  if (Math.abs(actual - expected) > tolerance) {
    throw new Error(msg || `Expected ~${expected}, got ${actual}`);
  }
}

// ========================================
// Helpers: extract values from Scott-encoded types
// ========================================

function scottBool(b) {
  return b === Bool["Bool"]["true"];
}

function scottMaybe(m) {
  let result = { tag: 'nothing', value: null };
  m({ just: v => { result = { tag: 'just', value: v }; }, nothing: () => {} });
  return result;
}

function scottState(s) {
  const names = ['Idle', 'Loading', 'Playing', 'Paused', 'Ended', 'Error'];
  let result = 'unknown';
  const cases = {};
  for (const n of names) cases[n] = () => { result = n; };
  s(cases);
  return result;
}

// Extract field from VideoModel (Scott-encoded record)
function getField(model, field) {
  return Types["VideoModel"][field](model);
}

function getState(model) {
  return scottState(getField(model, 'state'));
}

function getString(model, field) {
  return getField(model, field);
}

function getBool(model, field) {
  return scottBool(getField(model, field));
}

function getNat(model, field) {
  return agdaRTS.IsNat(getField(model, field))
    ? Number(agdaRTS.IsNat(getField(model, field)))
    : Number(getField(model, field));
}

// VideoMsg constructors
const Msg = Types["VideoMsg"];

// Use defaultPlayerConfig with identity getter/wrapper for testing
const testConfig = Player["defaultPlayerConfig"](null)(null)(
  "https://example.com/manifest.m3u8")(x => x)(x => x);

// Helper: apply update
function applyUpdate(cfg, msg, model) {
  return Player["mkUpdateVideo"](null)(null)(cfg)(msg)(model);
}

// Helper: inspect Cmd (Scott-encoded)
function cmdName(cmd) {
  let name = 'ε';
  try {
    cmd({
      'ε': () => { name = 'ε'; },
      '_<>_': () => { name = '<>'; },
      'delay': () => { name = 'delay'; },
      'httpGet': () => { name = 'httpGet'; },
      'httpPost': () => { name = 'httpPost'; },
      'attempt': () => { name = 'attempt'; },
      'focus': () => { name = 'focus'; },
      'blur': () => { name = 'blur'; },
      'scrollTo': () => { name = 'scrollTo'; },
      'scrollIntoView': () => { name = 'scrollIntoView'; },
      'writeClipboard': () => { name = 'writeClipboard'; },
      'readClipboard': () => { name = 'readClipboard'; },
      'getItem': () => { name = 'getItem'; },
      'setItem': () => { name = 'setItem'; },
      'removeItem': () => { name = 'removeItem'; },
      'wsSend': () => { name = 'wsSend'; },
      'channelSend': () => { name = 'channelSend'; },
      'freeBuffer': () => { name = 'freeBuffer'; },
      'touchBuffer': () => { name = 'touchBuffer'; },
      'callMethod': () => { name = 'callMethod'; },
      'setProp': () => { name = 'setProp'; },
      'getProp': () => { name = 'getProp'; },
      'mediaSourceInit': () => { name = 'mediaSourceInit'; },
      'mediaSourceAppend': () => { name = 'mediaSourceAppend'; },
      'mediaSourceEnd': () => { name = 'mediaSourceEnd'; },
      'pushUrl': () => { name = 'pushUrl'; },
      'replaceUrl': () => { name = 'replaceUrl'; },
      'back': () => { name = 'back'; },
      'forward': () => { name = 'forward'; },
    });
  } catch (e) { name = 'error:' + e.message; }
  return name;
}

function cmdCallMethod(cmd) {
  let sel = '', method = '';
  cmd({
    'ε': () => {},
    '_<>_': () => {},
    'callMethod': (s, m) => { sel = s; method = m; },
    'setProp': () => {},
    'getProp': () => {},
    'mediaSourceInit': () => {},
    'mediaSourceAppend': () => {},
    'mediaSourceEnd': () => {},
    'attempt': () => {},
    'delay': () => {},
    'httpGet': () => {},
    'httpPost': () => {},
    'focus': () => {},
    'blur': () => {},
    'scrollTo': () => {},
    'scrollIntoView': () => {},
    'writeClipboard': () => {},
    'readClipboard': () => {},
    'getItem': () => {},
    'setItem': () => {},
    'removeItem': () => {},
    'wsSend': () => {},
    'channelSend': () => {},
    'freeBuffer': () => {},
    'touchBuffer': () => {},
    'pushUrl': () => {},
    'replaceUrl': () => {},
    'back': () => {},
    'forward': () => {},
  });
  return { sel, method };
}

function cmdSetProp(cmd) {
  let sel = '', prop = '', value = '';
  cmd({
    'ε': () => {},
    '_<>_': () => {},
    'callMethod': () => {},
    'setProp': (s, p, v) => { sel = s; prop = p; value = v; },
    'getProp': () => {},
    'mediaSourceInit': () => {},
    'mediaSourceAppend': () => {},
    'mediaSourceEnd': () => {},
    'attempt': () => {},
    'delay': () => {},
    'httpGet': () => {},
    'httpPost': () => {},
    'focus': () => {},
    'blur': () => {},
    'scrollTo': () => {},
    'scrollIntoView': () => {},
    'writeClipboard': () => {},
    'readClipboard': () => {},
    'getItem': () => {},
    'setItem': () => {},
    'removeItem': () => {},
    'wsSend': () => {},
    'channelSend': () => {},
    'freeBuffer': () => {},
    'touchBuffer': () => {},
    'pushUrl': () => {},
    'replaceUrl': () => {},
    'back': () => {},
    'forward': () => {},
  });
  return { sel, prop, value };
}

// ========================================
// 1. JS Postulates (Util.agda)
// ========================================

console.log('\n=== JS Postulates (Util) ===\n');

// formatTime
test('formatTime: 0 → "0:00"', () => assertEqual(Util["formatTime"]("0"), "0:00"));
test('formatTime: 65 → "1:05"', () => assertEqual(Util["formatTime"]("65"), "1:05"));
test('formatTime: 125.7 → "2:05"', () => assertEqual(Util["formatTime"]("125.7"), "2:05"));
test('formatTime: 3661 → "61:01"', () => assertEqual(Util["formatTime"]("3661"), "61:01"));
test('formatTime: empty → "0:00"', () => assertEqual(Util["formatTime"](""), "0:00"));
test('formatTime: garbage → "0:00"', () => assertEqual(Util["formatTime"]("abc"), "0:00"));

// formatTimeLong
test('formatTimeLong: 65 → "01:05"', () => assertEqual(Util["formatTimeLong"]("65"), "01:05"));
test('formatTimeLong: 3661 → "01:01:01"', () => assertEqual(Util["formatTimeLong"]("3661"), "01:01:01"));
test('formatTimeLong: 0 → "00:00"', () => assertEqual(Util["formatTimeLong"]("0"), "00:00"));

// seekPercent
test('seekPercent: 50/100 → "50"', () => assertEqual(Util["seekPercent"]("50")("100"), "50"));
test('seekPercent: 0/100 → "0"', () => assertEqual(Util["seekPercent"]("0")("100"), "0"));
test('seekPercent: 100/100 → "100"', () => assertEqual(Util["seekPercent"]("100")("100"), "100"));
test('seekPercent: 0/0 → "0" (avoid div by zero)', () => assertEqual(Util["seekPercent"]("0")("0"), "0"));
test('seekPercent: 50/0 → "0"', () => assertEqual(Util["seekPercent"]("50")("0"), "0"));

// bufferedPercent
test('bufferedPercent: 75/100 → "75"', () => assertEqual(Util["bufferedPercent"]("75")("100"), "75"));
test('bufferedPercent: 0/0 → "0"', () => assertEqual(Util["bufferedPercent"]("0")("0"), "0"));

// clampVolume
test('clampVolume: 0.5 → "0.5"', () => assertEqual(Util["clampVolume"]("0.5"), "0.5"));
test('clampVolume: -1 → "0"', () => assertEqual(Util["clampVolume"]("-1"), "0"));
test('clampVolume: 2 → "1"', () => assertEqual(Util["clampVolume"]("2"), "1"));
test('clampVolume: 0 → "0"', () => assertEqual(Util["clampVolume"]("0"), "0"));
test('clampVolume: 1 → "1"', () => assertEqual(Util["clampVolume"]("1"), "1"));
test('clampVolume: garbage → "0"', () => assertEqual(Util["clampVolume"]("abc"), "0"));

// offsetVolume
test('offsetVolume: 0.5 + 0.1 → "0.6"', () => assertClose(parseFloat(Util["offsetVolume"]("0.5")("+0.1")), 0.6));
test('offsetVolume: 0.5 - 0.1 → "0.4"', () => assertClose(parseFloat(Util["offsetVolume"]("0.5")("-0.1")), 0.4));
test('offsetVolume: 0.9 + 0.5 → "1" (clamped)', () => assertEqual(Util["offsetVolume"]("0.9")("0.5"), "1"));
test('offsetVolume: 0.1 - 0.5 → "0" (clamped)', () => assertEqual(Util["offsetVolume"]("0.1")("-0.5"), "0"));

// offsetTime
test('offsetTime: 10+5/100 → "15"', () => assertEqual(Util["offsetTime"]("10")("5")("100"), "15"));
test('offsetTime: 10-15/100 → "0" (clamped)', () => assertEqual(Util["offsetTime"]("10")("-15")("100"), "0"));
test('offsetTime: 95+10/100 → "100" (clamped)', () => assertEqual(Util["offsetTime"]("95")("10")("100"), "100"));

// parseM3U8
test('parseM3U8: extract segment URLs', () => {
  const m3u8 = '#EXTM3U\n#EXT-X-VERSION:7\n#EXTINF:4.0,\nseg0.m4s\n#EXTINF:4.0,\nseg1.m4s\n';
  const result = JSON.parse(Util["parseM3U8"](m3u8));
  assertEqual(result.length, 2);
  assertEqual(result[0], 'seg0.m4s');
  assertEqual(result[1], 'seg1.m4s');
});
test('parseM3U8: empty manifest → []', () => {
  assertEqual(Util["parseM3U8"](""), "[]");
});
test('parseM3U8: no segments → []', () => {
  assertEqual(Util["parseM3U8"]("#EXTM3U\n#EXT-X-VERSION:7"), "[]");
});

// jsonArrayGet
test('jsonArrayGet: ["a","b"] at 0 → "a"', () => assertEqual(Util["jsonArrayGet"]('["a","b"]')(0), "a"));
test('jsonArrayGet: ["a","b"] at 1 → "b"', () => assertEqual(Util["jsonArrayGet"]('["a","b"]')(1), "b"));
test('jsonArrayGet: out of bounds → ""', () => assertEqual(Util["jsonArrayGet"]('["a"]')(5), ""));
test('jsonArrayGet: invalid JSON → ""', () => assertEqual(Util["jsonArrayGet"]('garbage')(0), ""));

// jsonArrayLength
test('jsonArrayLength: ["a","b"] → 2', () => assertEqual(Util["jsonArrayLength"]('["a","b"]'), 2));
test('jsonArrayLength: [] → 0', () => assertEqual(Util["jsonArrayLength"]('[]'), 0));
test('jsonArrayLength: invalid → 0', () => assertEqual(Util["jsonArrayLength"]('garbage'), 0));

// ========================================
// 2. State Machine (update)
// ========================================

console.log('\n=== State Machine (update) ===\n');

const model0 = Types["defaultVideoModel"];

// Play / Pause / Toggle
test('update Play: Idle → Playing', () => {
  const m = applyUpdate(testConfig, Msg["Play"], model0);
  assertEqual(getState(m), 'Playing');
});

test('update Pause: Playing → Paused', () => {
  const playing = applyUpdate(testConfig, Msg["Play"], model0);
  const m = applyUpdate(testConfig, Msg["Pause"], playing);
  assertEqual(getState(m), 'Paused');
});

test('update TogglePlay: Idle → Playing', () => {
  const m = applyUpdate(testConfig, Msg["TogglePlay"], model0);
  assertEqual(getState(m), 'Playing');
});

test('update TogglePlay: Playing → Paused', () => {
  const playing = applyUpdate(testConfig, Msg["Play"], model0);
  const m = applyUpdate(testConfig, Msg["TogglePlay"], playing);
  assertEqual(getState(m), 'Paused');
});

// Error state blocks playback
test('update Play from Error: stays Error', () => {
  const errModel = applyUpdate(testConfig, Msg["MediaError"]("fail"), model0);
  assertEqual(getState(errModel), 'Error');
  const m = applyUpdate(testConfig, Msg["Play"], errModel);
  assertEqual(getState(m), 'Error');
});

test('update TogglePlay from Error: stays Error', () => {
  const errModel = applyUpdate(testConfig, Msg["MediaError"]("fail"), model0);
  const m = applyUpdate(testConfig, Msg["TogglePlay"], errModel);
  assertEqual(getState(m), 'Error');
});

// Volume
test('update SetVolume: sets volume', () => {
  const m = applyUpdate(testConfig, Msg["SetVolume"]("0.5"), model0);
  assertEqual(getString(m, 'volume'), '0.5');
});

test('update SetVolume: clamps to [0,1]', () => {
  const m = applyUpdate(testConfig, Msg["SetVolume"]("2"), model0);
  assertEqual(getString(m, 'volume'), '1');
});

test('update AdjustVolume: adds to current', () => {
  const m = applyUpdate(testConfig, Msg["AdjustVolume"]("+0.1"), model0);
  // default volume is "0.8", so 0.8 + 0.1 = 0.9
  assertClose(parseFloat(getString(m, 'volume')), 0.9);
});

test('update AdjustVolume: clamps at 0', () => {
  const m = applyUpdate(testConfig, Msg["AdjustVolume"]("-1"), model0);
  assertEqual(getString(m, 'volume'), '0');
});

// Mute
test('update ToggleMute: false → true', () => {
  const m = applyUpdate(testConfig, Msg["ToggleMute"], model0);
  assertEqual(getBool(m, 'muted'), true);
});

test('update ToggleMute twice: false → true → false', () => {
  const m1 = applyUpdate(testConfig, Msg["ToggleMute"], model0);
  const m2 = applyUpdate(testConfig, Msg["ToggleMute"], m1);
  assertEqual(getBool(m2, 'muted'), false);
});

// Rate
test('update SetRate: sets playbackRate', () => {
  const m = applyUpdate(testConfig, Msg["SetRate"]("2"), model0);
  assertEqual(getString(m, 'playbackRate'), '2');
});

// Fullscreen
test('update EnterFullscreen: true', () => {
  const m = applyUpdate(testConfig, Msg["EnterFullscreen"], model0);
  assertEqual(getBool(m, 'fullscreen'), true);
});

test('update ExitFullscreen: false', () => {
  const fs = applyUpdate(testConfig, Msg["EnterFullscreen"], model0);
  const m = applyUpdate(testConfig, Msg["ExitFullscreen"], fs);
  assertEqual(getBool(m, 'fullscreen'), false);
});

test('update ToggleFullscreen: toggles', () => {
  const m1 = applyUpdate(testConfig, Msg["ToggleFullscreen"], model0);
  assertEqual(getBool(m1, 'fullscreen'), true);
  const m2 = applyUpdate(testConfig, Msg["ToggleFullscreen"], m1);
  assertEqual(getBool(m2, 'fullscreen'), false);
});

// TimeUpdated
test('update TimeUpdated: sets currentTime', () => {
  const m = applyUpdate(testConfig, Msg["TimeUpdated"]("42.5"), model0);
  assertEqual(getString(m, 'currentTime'), '42.5');
});

// DurationLoaded
test('update DurationLoaded: sets duration, state = Paused (no autoplay)', () => {
  const m = applyUpdate(testConfig, Msg["DurationLoaded"]("120"), model0);
  assertEqual(getString(m, 'duration'), '120');
  assertEqual(getState(m), 'Paused');
});

// VolumeChanged
test('update VolumeChanged: sets volume from DOM', () => {
  const m = applyUpdate(testConfig, Msg["VolumeChanged"]("0.3"), model0);
  assertEqual(getString(m, 'volume'), '0.3');
});

// MediaEnded
test('update MediaEnded: → Ended (no loop)', () => {
  const m = applyUpdate(testConfig, Msg["MediaEnded"], model0);
  assertEqual(getState(m), 'Ended');
});

// MediaError
test('update MediaError: → Error with message', () => {
  const m = applyUpdate(testConfig, Msg["MediaError"]("codec not supported"), model0);
  assertEqual(getState(m), 'Error');
  const err = scottMaybe(getField(m, 'error'));
  assertEqual(err.tag, 'just');
  assertEqual(err.value, 'codec not supported');
});

// ManifestLoaded with segments
test('update ManifestLoaded: parses segments, → Loading', () => {
  const m3u8 = '#EXTM3U\n#EXTINF:4.0,\nseg0.m4s\n#EXTINF:4.0,\nseg1.m4s\n';
  const m = applyUpdate(testConfig, Msg["ManifestLoaded"](m3u8), model0);
  assertEqual(getState(m), 'Loading');
});

// ManifestLoaded empty
test('update ManifestLoaded empty: → Error', () => {
  const m = applyUpdate(testConfig, Msg["ManifestLoaded"]("#EXTM3U\n"), model0);
  assertEqual(getState(m), 'Error');
  const err = scottMaybe(getField(m, 'error'));
  assertEqual(err.tag, 'just');
  assert(err.value.includes('Empty manifest'));
});

// ManifestError
test('update ManifestError: → Error', () => {
  const m = applyUpdate(testConfig, Msg["ManifestError"]("404"), model0);
  assertEqual(getState(m), 'Error');
});

// SourceReady
test('update SourceReady: sets sourceReady', () => {
  const m = applyUpdate(testConfig, Msg["SourceReady"], model0);
  assertEqual(getBool(m, 'sourceReady'), true);
});

// SegmentAppended
test('update SegmentAppended: state unchanged', () => {
  const m = applyUpdate(testConfig, Msg["SegmentAppended"](0n), model0);
  assertEqual(getState(m), 'Idle'); // state unchanged, only currentSegment changes
});

// BufferedUpdated
test('update BufferedUpdated: sets buffered', () => {
  const m = applyUpdate(testConfig, Msg["BufferedUpdated"]("42"), model0);
  assertEqual(getString(m, 'buffered'), '42');
});

// Controls visibility
test('update ControlsShow: visible = true', () => {
  const hidden = applyUpdate(testConfig, Msg["ControlsHide"], model0);
  assertEqual(getBool(hidden, 'controlsVisible'), false);
  const m = applyUpdate(testConfig, Msg["ControlsShow"], hidden);
  assertEqual(getBool(m, 'controlsVisible'), true);
});

test('update ControlsHide: visible = false', () => {
  const m = applyUpdate(testConfig, Msg["ControlsHide"], model0);
  assertEqual(getBool(m, 'controlsVisible'), false);
});

test('update ControlsActivity: visible = true', () => {
  const hidden = applyUpdate(testConfig, Msg["ControlsHide"], model0);
  const m = applyUpdate(testConfig, Msg["ControlsActivity"], hidden);
  assertEqual(getBool(m, 'controlsVisible'), true);
});

// ========================================
// 3. Cmd dispatch
// ========================================

console.log('\n=== Cmd dispatch ===\n');

function applyCmd(cfg, msg, model) {
  return Player["mkVideoCmd"](null)(null)(cfg)(msg)(model);
}

test('cmd Play: callMethod "play"', () => {
  const cmd = applyCmd(testConfig, Msg["Play"], model0);
  assertEqual(cmdName(cmd), 'callMethod');
  const { method } = cmdCallMethod(cmd);
  assertEqual(method, 'play');
});

test('cmd Pause: callMethod "pause"', () => {
  const cmd = applyCmd(testConfig, Msg["Pause"], model0);
  const { method } = cmdCallMethod(cmd);
  assertEqual(method, 'pause');
});

test('cmd SeekTo: setProp currentTime (absolute)', () => {
  const cmd = applyCmd(testConfig, Msg["SeekTo"]("42.5"), model0);
  assertEqual(cmdName(cmd), 'setProp');
  const { prop, value } = cmdSetProp(cmd);
  assertEqual(prop, 'currentTime');
  assertEqual(value, '42.5');
});

test('cmd Seek: setProp currentTime (relative via offsetTime)', () => {
  // model has currentTime "0", duration "0"
  const cmd = applyCmd(testConfig, Msg["Seek"]("5"), model0);
  assertEqual(cmdName(cmd), 'setProp');
  const { prop } = cmdSetProp(cmd);
  assertEqual(prop, 'currentTime');
});

test('cmd SetVolume: setProp volume', () => {
  const cmd = applyCmd(testConfig, Msg["SetVolume"]("0.5"), model0);
  const { prop, value } = cmdSetProp(cmd);
  assertEqual(prop, 'volume');
  assertEqual(value, '0.5');
});

test('cmd SetRate: setProp playbackRate', () => {
  const cmd = applyCmd(testConfig, Msg["SetRate"]("1.5"), model0);
  const { prop, value } = cmdSetProp(cmd);
  assertEqual(prop, 'playbackRate');
  assertEqual(value, '1.5');
});

test('cmd ExitFullscreen: callMethod on "document"', () => {
  const cmd = applyCmd(testConfig, Msg["ExitFullscreen"], model0);
  const { sel, method } = cmdCallMethod(cmd);
  assertEqual(sel, 'document');
  assertEqual(method, 'exitFullscreen');
});

test('cmd ControlsActivity: ε (no side effect)', () => {
  const cmd = applyCmd(testConfig, Msg["ControlsActivity"], model0);
  assertEqual(cmdName(cmd), 'ε');
});

test('cmd ManifestLoaded: mediaSourceInit (when sourceReady=false)', () => {
  const cmd = applyCmd(testConfig, Msg["ManifestLoaded"]("..."), model0);
  assertEqual(cmdName(cmd), 'mediaSourceInit');
});

test('cmd ToggleMute from unmuted: setProp muted "true"', () => {
  const cmd = applyCmd(testConfig, Msg["ToggleMute"], model0);
  const { prop, value } = cmdSetProp(cmd);
  assertEqual(prop, 'muted');
  assertEqual(value, 'true');
});

test('cmd ToggleMute from muted: setProp muted "false"', () => {
  const mutedModel = applyUpdate(testConfig, Msg["ToggleMute"], model0);
  const cmd = applyCmd(testConfig, Msg["ToggleMute"], mutedModel);
  const { prop, value } = cmdSetProp(cmd);
  assertEqual(prop, 'muted');
  assertEqual(value, 'false');
});

test('cmd AdjustVolume: setProp volume', () => {
  const cmd = applyCmd(testConfig, Msg["AdjustVolume"]("+0.1"), model0);
  assertEqual(cmdName(cmd), 'setProp');
  const { prop } = cmdSetProp(cmd);
  assertEqual(prop, 'volume');
});

test('cmd TogglePlay from Idle: callMethod play', () => {
  const cmd = applyCmd(testConfig, Msg["TogglePlay"], model0);
  const { method } = cmdCallMethod(cmd);
  assertEqual(method, 'play');
});

test('cmd TogglePlay from Playing: callMethod pause', () => {
  const playing = applyUpdate(testConfig, Msg["Play"], model0);
  const cmd = applyCmd(testConfig, Msg["TogglePlay"], playing);
  const { method } = cmdCallMethod(cmd);
  assertEqual(method, 'pause');
});

test('cmd EnterFullscreen: callMethod requestFullscreen', () => {
  const cmd = applyCmd(testConfig, Msg["EnterFullscreen"], model0);
  const { method } = cmdCallMethod(cmd);
  assertEqual(method, 'requestFullscreen');
});

test('cmd ToggleFullscreen: callMethod requestFullscreen', () => {
  const cmd = applyCmd(testConfig, Msg["ToggleFullscreen"], model0);
  const { method } = cmdCallMethod(cmd);
  assertEqual(method, 'requestFullscreen');
});

test('cmd SegmentFetched: mediaSourceAppend', () => {
  const cmd = applyCmd(testConfig, Msg["SegmentFetched"](0n)("base64data"), model0);
  assertEqual(cmdName(cmd), 'mediaSourceAppend');
});

test('cmd MediaEnded (no loop): ε', () => {
  const cmd = applyCmd(testConfig, Msg["MediaEnded"], model0);
  assertEqual(cmdName(cmd), 'ε');
});

test('cmd MediaError: ε', () => {
  const cmd = applyCmd(testConfig, Msg["MediaError"]("fail"), model0);
  assertEqual(cmdName(cmd), 'ε');
});

test('cmd TimeUpdated: ε', () => {
  const cmd = applyCmd(testConfig, Msg["TimeUpdated"]("10"), model0);
  assertEqual(cmdName(cmd), 'ε');
});

test('cmd VolumeChanged: ε', () => {
  const cmd = applyCmd(testConfig, Msg["VolumeChanged"]("0.5"), model0);
  assertEqual(cmdName(cmd), 'ε');
});

test('cmd ControlsShow: ε', () => {
  const cmd = applyCmd(testConfig, Msg["ControlsShow"], model0);
  assertEqual(cmdName(cmd), 'ε');
});

test('cmd ControlsHide: ε', () => {
  const cmd = applyCmd(testConfig, Msg["ControlsHide"], model0);
  assertEqual(cmdName(cmd), 'ε');
});

test('cmd SourceReady (no segments): ε', () => {
  // model0 has totalSegments=0
  const cmd = applyCmd(testConfig, Msg["SourceReady"], model0);
  assertEqual(cmdName(cmd), 'ε');
});

test('cmd SourceReady (with segments): attempt (loadSegment)', () => {
  // Simulate model after ManifestLoaded
  const m3u8 = '#EXTM3U\n#EXTINF:4.0,\nseg0.m4s\n#EXTINF:4.0,\nseg1.m4s\n';
  const loaded = applyUpdate(testConfig, Msg["ManifestLoaded"](m3u8), model0);
  const ready = applyUpdate(testConfig, Msg["SourceReady"], loaded);
  const cmd = applyCmd(testConfig, Msg["SourceReady"], ready);
  assertEqual(cmdName(cmd), 'attempt');
});

test('cmd ManifestLoaded (sourceReady=true): ε', () => {
  const readyModel = applyUpdate(testConfig, Msg["SourceReady"], model0);
  const cmd = applyCmd(testConfig, Msg["ManifestLoaded"]("..."), readyModel);
  assertEqual(cmdName(cmd), 'ε');
});

// ========================================
// 3b. Update — remaining messages
// ========================================

console.log('\n=== Update (remaining messages) ===\n');

test('update SeekTo: no state change', () => {
  const m = applyUpdate(testConfig, Msg["SeekTo"]("42"), model0);
  assertEqual(getState(m), 'Idle');
});

test('update Seek: no state change', () => {
  const m = applyUpdate(testConfig, Msg["Seek"]("-5"), model0);
  assertEqual(getState(m), 'Idle');
});

test('update SourceError: → Error', () => {
  const m = applyUpdate(testConfig, Msg["SourceError"]("failed"), model0);
  assertEqual(getState(m), 'Error');
});

test('update SegmentError: → Error', () => {
  const m = applyUpdate(testConfig, Msg["SegmentError"](0n)("network"), model0);
  assertEqual(getState(m), 'Error');
  const err = scottMaybe(getField(m, 'error'));
  assertEqual(err.value, 'network');
});

test('update ProtectionError: → Error', () => {
  const m = applyUpdate(testConfig, Msg["ProtectionError"]("token expired"), model0);
  assertEqual(getState(m), 'Error');
});

test('update LoadNextSegment: no state change', () => {
  const m = applyUpdate(testConfig, Msg["LoadNextSegment"], model0);
  assertEqual(getState(m), 'Idle');
});

test('update AllSegmentsLoaded: no state change', () => {
  const m = applyUpdate(testConfig, Msg["AllSegmentsLoaded"], model0);
  assertEqual(getState(m), 'Idle');
});

test('update TokenRefreshed: no state change', () => {
  const m = applyUpdate(testConfig, Msg["TokenRefreshed"]("tok"), model0);
  assertEqual(getState(m), 'Idle');
});

test('update KeyLoaded: no state change', () => {
  const m = applyUpdate(testConfig, Msg["KeyLoaded"]("key"), model0);
  assertEqual(getState(m), 'Idle');
});

test('update SegmentFetched: no state change', () => {
  const m = applyUpdate(testConfig, Msg["SegmentFetched"](0n)("data"), model0);
  assertEqual(getState(m), 'Idle');
});

// ========================================
// 3c. Multi-step sequences
// ========================================

console.log('\n=== Multi-step sequences ===\n');

test('Play → Pause → Play roundtrip', () => {
  const m1 = applyUpdate(testConfig, Msg["Play"], model0);
  assertEqual(getState(m1), 'Playing');
  const m2 = applyUpdate(testConfig, Msg["Pause"], m1);
  assertEqual(getState(m2), 'Paused');
  const m3 = applyUpdate(testConfig, Msg["Play"], m2);
  assertEqual(getState(m3), 'Playing');
});

test('ManifestLoaded → SourceReady flow', () => {
  const m3u8 = '#EXTM3U\n#EXTINF:4.0,\nseg0.m4s\n';
  const m1 = applyUpdate(testConfig, Msg["ManifestLoaded"](m3u8), model0);
  assertEqual(getState(m1), 'Loading');
  assertEqual(getBool(m1, 'sourceReady'), false);
  const m2 = applyUpdate(testConfig, Msg["SourceReady"], m1);
  assertEqual(getBool(m2, 'sourceReady'), true);
});

test('Error → Play blocked, error preserved', () => {
  const err = applyUpdate(testConfig, Msg["MediaError"]("broken"), model0);
  assertEqual(getState(err), 'Error');
  const m = applyUpdate(testConfig, Msg["Play"], err);
  assertEqual(getState(m), 'Error');
  const errMsg = scottMaybe(getField(m, 'error'));
  assertEqual(errMsg.value, 'broken');
});

test('ControlsHide → ControlsActivity → visible again', () => {
  const hidden = applyUpdate(testConfig, Msg["ControlsHide"], model0);
  assertEqual(getBool(hidden, 'controlsVisible'), false);
  const m = applyUpdate(testConfig, Msg["ControlsActivity"], hidden);
  assertEqual(getBool(m, 'controlsVisible'), true);
});

test('SetVolume → AdjustVolume composes', () => {
  const m1 = applyUpdate(testConfig, Msg["SetVolume"]("0.5"), model0);
  assertEqual(getString(m1, 'volume'), '0.5');
  const m2 = applyUpdate(testConfig, Msg["AdjustVolume"]("+0.2"), m1);
  assertClose(parseFloat(getString(m2, 'volume')), 0.7);
});

test('ToggleMute preserves volume', () => {
  const m1 = applyUpdate(testConfig, Msg["SetVolume"]("0.6"), model0);
  const m2 = applyUpdate(testConfig, Msg["ToggleMute"], m1);
  assertEqual(getBool(m2, 'muted'), true);
  assertEqual(getString(m2, 'volume'), '0.6');
});

// ========================================
// 3d. Postulate edge cases
// ========================================

console.log('\n=== Postulate edge cases ===\n');

test('formatTime: negative → "0:00"', () => assertEqual(Util["formatTime"]("-5"), "0:00"));
test('formatTime: very large → correct', () => {
  const r = Util["formatTime"]("7200");
  assertEqual(r, "120:00");
});

test('seekPercent: negative current → correct', () => {
  // parseFloat("-10") = -10, -10/100 = -0.1 → "-10"
  const r = Util["seekPercent"]("-10")("100");
  assertEqual(r, "-10");
});

test('offsetTime: negative offset beyond 0 → "0"', () => {
  assertEqual(Util["offsetTime"]("5")("-100")("200"), "0");
});

test('offsetTime: positive offset beyond duration → duration', () => {
  assertEqual(Util["offsetTime"]("5")("1000")("200"), "200");
});

test('clampVolume: very small negative → "0"', () => {
  assertEqual(Util["clampVolume"]("-0.001"), "0");
});

test('clampVolume: just above 1 → "1"', () => {
  assertEqual(Util["clampVolume"]("1.001"), "1");
});

test('parseM3U8: handles Windows line endings', () => {
  const m3u8 = '#EXTM3U\r\n#EXTINF:4.0,\r\nseg0.m4s\r\n';
  const result = JSON.parse(Util["parseM3U8"](m3u8));
  assertEqual(result.length, 1);
  // May have trailing \r
  assert(result[0].startsWith('seg0.m4s'));
});

test('parseM3U8: skips comment-only lines after EXTINF', () => {
  const m3u8 = '#EXTM3U\n#EXTINF:4.0,\n#EXT-X-BYTERANGE:100\nseg0.m4s\n';
  const result = JSON.parse(Util["parseM3U8"](m3u8));
  // The parser looks at line i+1 after EXTINF — if it starts with #, it's skipped
  assertEqual(result.length, 0);
});

test('jsonArrayGet: deeply nested → returns string', () => {
  assertEqual(Util["jsonArrayGet"]('["hello"]')(0), "hello");
});

test('offsetVolume: 0 + 0 → "0"', () => {
  assertEqual(Util["offsetVolume"]("0")("0"), "0");
});

test('offsetVolume: 1 + 0 → "1"', () => {
  assertEqual(Util["offsetVolume"]("1")("0"), "1");
});

// ========================================
// 4. initVideoModel
// ========================================

console.log('\n=== initVideoModel ===\n');

test('initVideoModel uses config volume', () => {
  // initVideoModel has two implicit args {M} {A} then the config
  const m = Types["initVideoModel"](testConfig);
  assertEqual(getString(m, 'volume'), '0.8');
});

test('initVideoModel state is Idle', () => {
  const m = Types["initVideoModel"](testConfig);
  assertEqual(getState(m), 'Idle');
});

// ========================================
// 5. eqState / isPlaying / isPaused
// ========================================

console.log('\n=== State predicates ===\n');

const states = {
  Idle: Types["PlayerState"]["Idle"],
  Loading: Types["PlayerState"]["Loading"],
  Playing: Types["PlayerState"]["Playing"],
  Paused: Types["PlayerState"]["Paused"],
  Ended: Types["PlayerState"]["Ended"],
  Error: Types["PlayerState"]["Error"],
};

test('eqState reflexive: all states equal themselves', () => {
  for (const [name, s] of Object.entries(states)) {
    assert(scottBool(Types["eqState"](s)(s)), `eqState ${name} ${name} should be true`);
  }
});

test('eqState: different states are not equal', () => {
  assert(!scottBool(Types["eqState"](states.Playing)(states.Paused)));
  assert(!scottBool(Types["eqState"](states.Idle)(states.Error)));
});

test('isPlaying: only Playing → true', () => {
  assert(scottBool(Types["isPlaying"](states.Playing)));
  assert(!scottBool(Types["isPlaying"](states.Paused)));
  assert(!scottBool(Types["isPlaying"](states.Idle)));
  assert(!scottBool(Types["isPlaying"](states.Error)));
});

test('isPaused: only Paused → true', () => {
  assert(scottBool(Types["isPaused"](states.Paused)));
  assert(!scottBool(Types["isPaused"](states.Playing)));
});

// ========================================
// Summary
// ========================================

console.log(`\n${'='.repeat(40)}`);
console.log(`Results: ${passed} passed, ${failed} failed`);
if (failures.length > 0) {
  console.log('\nFailures:');
  for (const f of failures) console.log(`  - ${f.name}: ${f.error}`);
}
console.log();
process.exit(failed > 0 ? 1 : 0);
