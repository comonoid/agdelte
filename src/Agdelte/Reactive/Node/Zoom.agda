{-# OPTIONS --without-K #-}

-- Zoom/Lens composition for Node and Attr.
-- Re-exported by Agdelte.Reactive.Node for backward compatibility.

module Agdelte.Reactive.Node.Zoom where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool)
open import Function using (_∘_)

open import Agdelte.Reactive.Node.Core using
  ( Node; Attr; Binding; mkBinding; extract; equals
  ; text; bind; elem; empty; when; foreach; foreachKeyed
  ; whenT; scope; scopeProj; zoomRT; glCanvas
  ; attr; attrBind; on; onValue; onValueScreen; onKeyFiltered
  ; style; styleBind
  )

------------------------------------------------------------------------
-- Internal: transform binding to work with larger model
------------------------------------------------------------------------

focusBinding : ∀ {Model Model' A} → (Model → Model') → Binding Model' A → Binding Model A
focusBinding get b = mkBinding (extract b ∘ get) (equals b)

------------------------------------------------------------------------
-- Zoom: transform both Model AND Msg
------------------------------------------------------------------------

zoomAttr : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg) → Attr M' Msg' → Attr M Msg
zoomAttr get wrap (attr name val) = attr name val
zoomAttr get wrap (attrBind name b) = attrBind name (focusBinding get b)
zoomAttr get wrap (on event msg) = on event (wrap msg)
zoomAttr get wrap (onValue event handler) = onValue event (wrap ∘ handler)
zoomAttr get wrap (onValueScreen event handler) = onValueScreen event (wrap ∘ handler)
zoomAttr get wrap (onKeyFiltered keys handler) = onKeyFiltered keys (wrap ∘ handler)
zoomAttr get wrap (style name val) = style name val
zoomAttr get wrap (styleBind name b) = styleBind name (focusBinding get b)

mutual
  zoomNode' : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg) → Node M' Msg' → Node M Msg
  zoomNode' get wrap (text s) = text s
  zoomNode' get wrap (bind b) = bind (focusBinding get b)
  zoomNode' get wrap (elem tag attrs children) =
    elem tag (zoomAttrs' get wrap attrs) (zoomNodes' get wrap children)
  zoomNode' get wrap empty = empty
  zoomNode' get wrap (when cond node) = when (cond ∘ get) (zoomNode' get wrap node)
  zoomNode' get wrap (foreach {A} getList render) =
    foreach (getList ∘ get) (λ a i → zoomRT get wrap (render a i))
  zoomNode' get wrap (foreachKeyed {A} getList keyFn render) =
    foreachKeyed (getList ∘ get) keyFn (λ a i → zoomRT get wrap (render a i))
  zoomNode' get wrap (whenT cond trans node) =
    whenT (cond ∘ get) trans (zoomNode' get wrap node)
  zoomNode' get wrap (scope fp node) =
    scope (fp ∘ get) (zoomNode' get wrap node)
  zoomNode' get wrap (scopeProj proj node) =
    scopeProj (proj ∘ get) (zoomNode' get wrap node)
  zoomNode' get wrap (zoomRT get' wrap' inner) =
    zoomRT (get' ∘ get) (wrap ∘ wrap') inner
  zoomNode' get wrap (glCanvas attrs scene) =
    glCanvas (zoomAttrs' get wrap attrs) scene

  zoomNodes' : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg) → List (Node M' Msg') → List (Node M Msg)
  zoomNodes' get wrap [] = []
  zoomNodes' get wrap (n ∷ ns) = zoomNode' get wrap n ∷ zoomNodes' get wrap ns

  zoomAttrs' : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg) → List (Attr M' Msg') → List (Attr M Msg)
  zoomAttrs' get wrap [] = []
  zoomAttrs' get wrap (a ∷ as) = zoomAttr get wrap a ∷ zoomAttrs' get wrap as

zoomNode : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg) → Node M' Msg' → Node M Msg
zoomNode get wrap node = scopeProj get (zoomNode' get wrap node)

------------------------------------------------------------------------
-- Zoom with Lens + Prism
------------------------------------------------------------------------

open import Agdelte.Reactive.Optic using (Prism; Lens; get; build)

zoomNodeL : ∀ {M M' Msg Msg'} → Lens M M' → Prism Msg Msg' → Node M' Msg' → Node M Msg
zoomNodeL l p = zoomNode (get l) (build p)

zoomNodeS : ∀ {M M' Msg Msg'} → (M → M') → (M' → String) → (Msg' → Msg) → Node M' Msg' → Node M Msg
zoomNodeS get' fp wrap node = scope (fp ∘ get') (zoomNode' get' wrap node)

zoomNodeLS : ∀ {M M' Msg Msg'} → Lens M M' → (M' → String) → Prism Msg Msg' → Node M' Msg' → Node M Msg
zoomNodeLS l fp p = zoomNodeS (get l) fp (build p)

zoomAttrL : ∀ {M M' Msg Msg'} → Lens M M' → Prism Msg Msg' → Attr M' Msg' → Attr M Msg
zoomAttrL l p = zoomAttr (get l) (build p)
