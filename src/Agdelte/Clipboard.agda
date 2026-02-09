{-# OPTIONS --without-K #-}

-- Clipboard API for Agdelte
-- Read and write to system clipboard

module Agdelte.Clipboard where

open import Data.String using (String)
open import Data.Unit using (⊤)

open import Agdelte.Core.Cmd using (Cmd)
open import Agdelte.Core.Task using (Task)

------------------------------------------------------------------------
-- Clipboard commands
------------------------------------------------------------------------

postulate
  -- Copy text to clipboard
  copy : String → Cmd ⊤

  -- Copy and notify with message
  copyNotify : String → (String → A) → Cmd A
    where postulate A : Set

{-# COMPILE JS copy = function(text) {
  return {
    tag: 'clipboard',
    action: 'copy',
    text: text
  };
} #-}

{-# COMPILE JS copyNotify = function(text) { return function(toMsg) {
  return {
    tag: 'clipboardNotify',
    action: 'copy',
    text: text,
    onSuccess: toMsg
  };
}; } #-}

------------------------------------------------------------------------
-- Clipboard tasks (async)
------------------------------------------------------------------------

postulate
  -- Read text from clipboard (requires permission)
  readText : Task String String

  -- Write text to clipboard
  writeText : String → Task String ⊤

{-# COMPILE JS readText = {
  run: (onOk, onErr) => {
    navigator.clipboard.readText()
      .then(text => onOk(text))
      .catch(err => onErr(err.message || 'Clipboard read failed'));
    return () => {};
  }
} #-}

{-# COMPILE JS writeText = function(text) {
  return {
    run: (onOk, onErr) => {
      navigator.clipboard.writeText(text)
        .then(() => onOk(null))
        .catch(err => onErr(err.message || 'Clipboard write failed'));
      return () => {};
    }
  };
} #-}

------------------------------------------------------------------------
-- Clipboard events
------------------------------------------------------------------------

open import Agdelte.Core.Event using (Event)

postulate
  -- Listen for paste events on document
  onPaste : (String → A) → Event A
    where postulate A : Set

  -- Listen for copy events
  onCopy : A → Event A
    where postulate A : Set

  -- Listen for cut events
  onCut : A → Event A
    where postulate A : Set

{-# COMPILE JS onPaste = function(toMsg) {
  return {
    tag: 'clipboardEvent',
    event: 'paste',
    handler: toMsg
  };
} #-}

{-# COMPILE JS onCopy = function(msg) {
  return {
    tag: 'clipboardEvent',
    event: 'copy',
    handler: () => msg
  };
} #-}

{-# COMPILE JS onCut = function(msg) {
  return {
    tag: 'clipboardEvent',
    event: 'cut',
    handler: () => msg
  };
} #-}
