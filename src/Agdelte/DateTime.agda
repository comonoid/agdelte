{-# OPTIONS --without-K #-}

-- Date and Time for Agdelte
-- FFI bindings to JavaScript Date API

module Agdelte.DateTime where

open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Int using (ℤ)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Agdelte.Core.Task using (Task)

------------------------------------------------------------------------
-- Date type (opaque, backed by JS Date)
------------------------------------------------------------------------

postulate
  Date : Set

{-# COMPILE JS Date = function(x) { return x; } #-}

------------------------------------------------------------------------
-- Duration type
------------------------------------------------------------------------

record Duration : Set where
  constructor mkDuration
  field
    milliseconds : ℕ

open Duration public

-- Duration constructors
ms : ℕ → Duration
ms n = mkDuration n

seconds : ℕ → Duration
seconds n = mkDuration (n * 1000)

minutes : ℕ → Duration
minutes n = mkDuration (n * 60000)

hours : ℕ → Duration
hours n = mkDuration (n * 3600000)

days : ℕ → Duration
days n = mkDuration (n * 86400000)

------------------------------------------------------------------------
-- Getting current time
------------------------------------------------------------------------

postulate
  -- Current date/time (impure)
  now : Task ⊥ Date
    where postulate ⊥ : Set

  -- Current timestamp in milliseconds since epoch
  nowMillis : Task ⊥ ℕ
    where postulate ⊥ : Set

{-# COMPILE JS now = {
  run: (onOk, onErr) => { onOk(new Date()); return () => {}; }
} #-}

{-# COMPILE JS nowMillis = {
  run: (onOk, onErr) => { onOk(BigInt(Date.now())); return () => {}; }
} #-}

------------------------------------------------------------------------
-- Date construction
------------------------------------------------------------------------

postulate
  -- From milliseconds since epoch
  fromMillis : ℕ → Date

  -- From ISO string (e.g., "2024-01-15T10:30:00Z")
  fromISOString : String → Maybe Date

  -- From components (year, month 1-12, day, hour, minute, second)
  fromComponents : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Date

  -- Parse with format string
  parse : String → String → Maybe Date

{-# COMPILE JS fromMillis = function(ms) {
  return new Date(Number(ms));
} #-}

{-# COMPILE JS fromISOString = function(s) {
  const d = new Date(s);
  if (isNaN(d.getTime())) return { nothing: null };
  return { just: d };
} #-}

{-# COMPILE JS fromComponents = function(year) { return function(month) { return function(day) {
  return function(hour) { return function(minute) { return function(second) {
    return new Date(Number(year), Number(month) - 1, Number(day), Number(hour), Number(minute), Number(second));
  }; }; };
}; }; } #-}

{-# COMPILE JS parse = function(format) { return function(s) {
  // Simple parser for common formats
  // Full implementation would use a library like date-fns
  const d = new Date(s);
  if (isNaN(d.getTime())) return { nothing: null };
  return { just: d };
}; } #-}

------------------------------------------------------------------------
-- Date components (getters)
------------------------------------------------------------------------

postulate
  -- Get year
  getYear : Date → ℕ

  -- Get month (1-12)
  getMonth : Date → ℕ

  -- Get day of month (1-31)
  getDay : Date → ℕ

  -- Get day of week (0 = Sunday, 6 = Saturday)
  getDayOfWeek : Date → ℕ

  -- Get hour (0-23)
  getHour : Date → ℕ

  -- Get minute (0-59)
  getMinute : Date → ℕ

  -- Get second (0-59)
  getSecond : Date → ℕ

  -- Get millisecond (0-999)
  getMillisecond : Date → ℕ

  -- Get timestamp in milliseconds since epoch
  getTime : Date → ℕ

{-# COMPILE JS getYear = function(d) { return BigInt(d.getFullYear()); } #-}
{-# COMPILE JS getMonth = function(d) { return BigInt(d.getMonth() + 1); } #-}
{-# COMPILE JS getDay = function(d) { return BigInt(d.getDate()); } #-}
{-# COMPILE JS getDayOfWeek = function(d) { return BigInt(d.getDay()); } #-}
{-# COMPILE JS getHour = function(d) { return BigInt(d.getHours()); } #-}
{-# COMPILE JS getMinute = function(d) { return BigInt(d.getMinutes()); } #-}
{-# COMPILE JS getSecond = function(d) { return BigInt(d.getSeconds()); } #-}
{-# COMPILE JS getMillisecond = function(d) { return BigInt(d.getMilliseconds()); } #-}
{-# COMPILE JS getTime = function(d) { return BigInt(d.getTime()); } #-}

------------------------------------------------------------------------
-- Date arithmetic
------------------------------------------------------------------------

postulate
  -- Add duration to date
  addDuration : Duration → Date → Date

  -- Subtract duration from date
  subDuration : Duration → Date → Date

  -- Difference between dates (second - first)
  diffDates : Date → Date → Duration

  -- Set specific component
  setYear : ℕ → Date → Date
  setMonth : ℕ → Date → Date
  setDay : ℕ → Date → Date
  setHour : ℕ → Date → Date
  setMinute : ℕ → Date → Date
  setSecond : ℕ → Date → Date

{-# COMPILE JS addDuration = function(dur) { return function(d) {
  return new Date(d.getTime() + Number(dur.milliseconds));
}; } #-}

{-# COMPILE JS subDuration = function(dur) { return function(d) {
  return new Date(d.getTime() - Number(dur.milliseconds));
}; } #-}

{-# COMPILE JS diffDates = function(d1) { return function(d2) {
  const diff = d2.getTime() - d1.getTime();
  return { milliseconds: BigInt(Math.abs(diff)) };
}; } #-}

{-# COMPILE JS setYear = function(y) { return function(d) {
  const n = new Date(d); n.setFullYear(Number(y)); return n;
}; } #-}

{-# COMPILE JS setMonth = function(m) { return function(d) {
  const n = new Date(d); n.setMonth(Number(m) - 1); return n;
}; } #-}

{-# COMPILE JS setDay = function(day) { return function(d) {
  const n = new Date(d); n.setDate(Number(day)); return n;
}; } #-}

{-# COMPILE JS setHour = function(h) { return function(d) {
  const n = new Date(d); n.setHours(Number(h)); return n;
}; } #-}

{-# COMPILE JS setMinute = function(m) { return function(d) {
  const n = new Date(d); n.setMinutes(Number(m)); return n;
}; } #-}

{-# COMPILE JS setSecond = function(s) { return function(d) {
  const n = new Date(d); n.setSeconds(Number(s)); return n;
}; } #-}

------------------------------------------------------------------------
-- Formatting
------------------------------------------------------------------------

postulate
  -- To ISO string (e.g., "2024-01-15T10:30:00.000Z")
  toISOString : Date → String

  -- To locale date string
  toLocaleDateString : Date → String

  -- To locale time string
  toLocaleTimeString : Date → String

  -- To locale date+time string
  toLocaleString : Date → String

  -- Format with pattern (simplified)
  -- Supports: YYYY, MM, DD, HH, mm, ss
  format : String → Date → String

{-# COMPILE JS toISOString = function(d) { return d.toISOString(); } #-}
{-# COMPILE JS toLocaleDateString = function(d) { return d.toLocaleDateString(); } #-}
{-# COMPILE JS toLocaleTimeString = function(d) { return d.toLocaleTimeString(); } #-}
{-# COMPILE JS toLocaleString = function(d) { return d.toLocaleString(); } #-}

{-# COMPILE JS format = function(pattern) { return function(d) {
  const pad = (n) => String(n).padStart(2, '0');
  return pattern
    .replace('YYYY', d.getFullYear())
    .replace('MM', pad(d.getMonth() + 1))
    .replace('DD', pad(d.getDate()))
    .replace('HH', pad(d.getHours()))
    .replace('mm', pad(d.getMinutes()))
    .replace('ss', pad(d.getSeconds()));
}; } #-}

------------------------------------------------------------------------
-- Comparison
------------------------------------------------------------------------

postulate
  -- Compare dates
  isBefore : Date → Date → Bool
  isAfter : Date → Date → Bool
  isSameDay : Date → Date → Bool
  isSameMonth : Date → Date → Bool
  isSameYear : Date → Date → Bool

{-# COMPILE JS isBefore = function(d1) { return function(d2) {
  return d1.getTime() < d2.getTime();
}; } #-}

{-# COMPILE JS isAfter = function(d1) { return function(d2) {
  return d1.getTime() > d2.getTime();
}; } #-}

{-# COMPILE JS isSameDay = function(d1) { return function(d2) {
  return d1.getFullYear() === d2.getFullYear() &&
         d1.getMonth() === d2.getMonth() &&
         d1.getDate() === d2.getDate();
}; } #-}

{-# COMPILE JS isSameMonth = function(d1) { return function(d2) {
  return d1.getFullYear() === d2.getFullYear() &&
         d1.getMonth() === d2.getMonth();
}; } #-}

{-# COMPILE JS isSameYear = function(d1) { return function(d2) {
  return d1.getFullYear() === d2.getFullYear();
}; } #-}

------------------------------------------------------------------------
-- Relative time
------------------------------------------------------------------------

postulate
  -- Get relative time string (e.g., "2 hours ago", "in 3 days")
  relativeTime : Date → Date → String

{-# COMPILE JS relativeTime = function(from) { return function(to) {
  const diff = to.getTime() - from.getTime();
  const abs = Math.abs(diff);
  const past = diff < 0;

  const seconds = Math.floor(abs / 1000);
  const minutes = Math.floor(seconds / 60);
  const hours = Math.floor(minutes / 60);
  const days = Math.floor(hours / 24);
  const months = Math.floor(days / 30);
  const years = Math.floor(days / 365);

  let result;
  if (years > 0) result = years + ' year' + (years > 1 ? 's' : '');
  else if (months > 0) result = months + ' month' + (months > 1 ? 's' : '');
  else if (days > 0) result = days + ' day' + (days > 1 ? 's' : '');
  else if (hours > 0) result = hours + ' hour' + (hours > 1 ? 's' : '');
  else if (minutes > 0) result = minutes + ' minute' + (minutes > 1 ? 's' : '');
  else result = 'just now';

  if (result === 'just now') return result;
  return past ? result + ' ago' : 'in ' + result;
}; } #-}

------------------------------------------------------------------------
-- Day of week helpers
------------------------------------------------------------------------

-- Day of week names
dayName : ℕ → String
dayName 0 = "Sunday"
dayName 1 = "Monday"
dayName 2 = "Tuesday"
dayName 3 = "Wednesday"
dayName 4 = "Thursday"
dayName 5 = "Friday"
dayName 6 = "Saturday"
dayName _ = "Unknown"

-- Short day names
dayNameShort : ℕ → String
dayNameShort 0 = "Sun"
dayNameShort 1 = "Mon"
dayNameShort 2 = "Tue"
dayNameShort 3 = "Wed"
dayNameShort 4 = "Thu"
dayNameShort 5 = "Fri"
dayNameShort 6 = "Sat"
dayNameShort _ = "???"

-- Month names
monthName : ℕ → String
monthName 1 = "January"
monthName 2 = "February"
monthName 3 = "March"
monthName 4 = "April"
monthName 5 = "May"
monthName 6 = "June"
monthName 7 = "July"
monthName 8 = "August"
monthName 9 = "September"
monthName 10 = "October"
monthName 11 = "November"
monthName 12 = "December"
monthName _ = "Unknown"

-- Short month names
monthNameShort : ℕ → String
monthNameShort 1 = "Jan"
monthNameShort 2 = "Feb"
monthNameShort 3 = "Mar"
monthNameShort 4 = "Apr"
monthNameShort 5 = "May"
monthNameShort 6 = "Jun"
monthNameShort 7 = "Jul"
monthNameShort 8 = "Aug"
monthNameShort 9 = "Sep"
monthNameShort 10 = "Oct"
monthNameShort 11 = "Nov"
monthNameShort 12 = "Dec"
monthNameShort _ = "???"
