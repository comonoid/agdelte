{-# OPTIONS --without-K #-}

-- Markdown rendering via JS FFI (marked.js or similar).
-- Converts markdown string to raw HTML, inserted via innerHTML.

module Agdelte.Html.Markdown where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Markdown → HTML conversion (JS FFI)
------------------------------------------------------------------------

-- | Convert markdown string to HTML string.
-- Uses a minimal markdown parser (no external deps — inline implementation).
postulate
  markdownToHtml : String → String

{-# COMPILE JS markdownToHtml = function(md) {
  // Escape HTML entities first to prevent XSS via innerHTML
  var esc = md
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
  // Minimal markdown: headers, bold, italic, code, links, lists
  var html = esc
    .replace(/^### (.+)$/gm, '<h3>$1</h3>')
    .replace(/^## (.+)$/gm, '<h2>$1</h2>')
    .replace(/^# (.+)$/gm, '<h1>$1</h1>')
    .replace(/\*\*(.+?)\*\*/g, '<strong>$1</strong>')
    .replace(/\*(.+?)\*/g, '<em>$1</em>')
    .replace(/`(.+?)`/g, '<code>$1</code>')
    .replace(/\[(.+?)\]\((.+?)\)/g, function(m, text, url) {
      if (/^(https?:\/\/|\/|#)/.test(url)) return '<a href="' + url + '">' + text + '</a>';
      return text;  // strip links with disallowed protocols (javascript:, data:, etc.)
    })
    .replace(/^\- (.+)$/gm, '<li>$1</li>')
    .replace(/(<li>.*<\/li>)/s, '<ul>$1</ul>')
    .replace(/\n\n/g, '<br><br>')
    .replace(/\n/g, '<br>');
  return html;
} #-}

------------------------------------------------------------------------
-- Markdown display component
------------------------------------------------------------------------

-- | Render markdown content as HTML.
-- Uses innerHTML binding — the markdown is converted once and set as raw HTML.
markdown : ∀ {M A}
         → (M → String)           -- markdown source from model
         → Node M A
markdown getMd =
  div (class "agdelte-markdown" ∷
       attrBind "innerHTML" (stringBinding (λ m → markdownToHtml (getMd m))) ∷
       [])
    []
