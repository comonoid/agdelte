{-# OPTIONS --without-K #-}

-- TreeView: Hierarchical tree structure display
-- CSS classes: .agdelte-tree, .agdelte-tree__node,
--              .agdelte-tree__toggle, .agdelte-tree__label,
--              .agdelte-tree__children

module Agdelte.Html.Controls.TreeView where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)

open import Agdelte.Reactive.Node
open import Agdelte.Html.Controls.Util using (eqStr)

------------------------------------------------------------------------
-- Tree node definition
------------------------------------------------------------------------

-- Simple tree node with string labels
record TreeNode (A : Set) : Set where
  constructor mkTreeNode
  inductive
  field
    nodeId       : String
    nodeLabel    : String
    nodeChildren : List (TreeNode A)

open TreeNode public

private
  depthPaddingUnit : ℕ
  depthPaddingUnit = 16

  hasChildren : ∀ {A} → TreeNode A → Bool
  hasChildren n with nodeChildren n
  ... | [] = false
  ... | _ = true

------------------------------------------------------------------------
-- Simple tree view (all expanded)
------------------------------------------------------------------------

-- | Simple tree view where all nodes are always expanded.
-- | onNodeClick: message when node is clicked (receives node ID)
simpleTree : ∀ {M A}
           → (String → A)         -- node click handler
           → List (TreeNode A)    -- root nodes
           → Node M A
simpleTree {M} {A} onNodeClick roots =
  div ( class "agdelte-tree" ∷ [] )
    (renderNodes 0 roots)
  where
    open import Agda.Builtin.String using (primShowNat)
    open import Data.Nat using (_*_)
    open import Data.String using (_++_)

    depthPadding : ℕ → String
    depthPadding d = primShowNat (d * depthPaddingUnit) ++ "px"

    mutual
      renderNode : ℕ → TreeNode A → Node M A
      renderNode depth node =
        div ( class "agdelte-tree__node"
            ∷ style "padding-left" (depthPadding depth)
            ∷ [] )
          ( button ( class "agdelte-tree__label"
                   ∷ onClick (onNodeClick (nodeId node))
                   ∷ [] )
              ( text (nodeLabel node) ∷ [] )
          ∷ (if hasChildren node
             then div ( class "agdelte-tree__children" ∷ [] )
                    (renderNodes (suc depth) (nodeChildren node))
                  ∷ []
             else []) )

      renderNodes : ℕ → List (TreeNode A) → List (Node M A)
      renderNodes _ [] = []
      renderNodes depth (n ∷ ns) = renderNode depth n ∷ renderNodes depth ns

------------------------------------------------------------------------
-- Collapsible tree view
------------------------------------------------------------------------

-- | Tree view with collapsible nodes.
-- | isExpanded: check if node ID is expanded
-- | toggleNode: message to toggle node expansion
-- | onNodeClick: message when node is clicked
{-# TERMINATING #-}
collapsibleTree : ∀ {M A}
                → (String → M → Bool)   -- is node expanded
                → (String → A)          -- toggle expansion
                → (String → A)          -- node click
                → List (TreeNode A)
                → Node M A
collapsibleTree {M} {A} isExpanded toggleNode onNodeClick roots =
  div ( class "agdelte-tree" ∷ [] )
    (renderNodes 0 roots)
  where
    open import Agda.Builtin.String using (primShowNat)
    open import Data.Nat using (_*_)
    open import Data.String renaming (_++_ to _++ˢ_)
    open import Data.List using (_++_)

    depthPadding : ℕ → String
    depthPadding d = primShowNat (d * depthPaddingUnit) ++ˢ "px"

    -- Lazy children: returns the children list only when expanded,
    -- empty list otherwise. foreach defers renderNode calls to the runtime.
    lazyChildren : String → List (TreeNode A) → M → List (TreeNode A)
    lazyChildren nid cs m = if isExpanded nid m then cs else []

    mutual
      renderNode : ℕ → TreeNode A → Node M A
      renderNode depth node =
        div ( class "agdelte-tree__node"
            ∷ style "padding-left" (depthPadding depth)
            ∷ [] )
          ( div ( class "agdelte-tree__header" ∷ [] )
              ( (if hasChildren node
                 then button ( attrBind "class" (mkBinding
                                 (λ m → if isExpanded (nodeId node) m
                                        then "agdelte-tree__toggle agdelte-tree__toggle--open"
                                        else "agdelte-tree__toggle")
                                 eqStr)
                             ∷ onClick (toggleNode (nodeId node))
                             ∷ [] )
                        ( text "▶" ∷ [] )
                      ∷ []
                 else span ( class "agdelte-tree__spacer" ∷ [] ) [] ∷ [])
              ++ ( button ( class "agdelte-tree__label"
                          ∷ onClick (onNodeClick (nodeId node))
                          ∷ [] )
                     ( text (nodeLabel node) ∷ [] )
                 ∷ [] ) )
          ∷ (if hasChildren node
             then div ( class "agdelte-tree__children" ∷ [] )
                    ( foreach (lazyChildren (nodeId node) (nodeChildren node))
                        (λ child _ → renderNode (suc depth) child)
                    ∷ [] )
                  ∷ []
             else []) )

      renderNodes : ℕ → List (TreeNode A) → List (Node M A)
      renderNodes _ [] = []
      renderNodes depth (n ∷ ns) = renderNode depth n ∷ renderNodes depth ns

------------------------------------------------------------------------
-- Draggable collapsible tree view (drag-drop reorder)
------------------------------------------------------------------------

-- | Drag message: source node ID and drop target node ID
record TreeDrag : Set where
  constructor mkTreeDrag
  field
    dragSourceId : String
    dropTargetId : String

open TreeDrag public

-- | Collapsible tree with drag-drop reorder support.
-- | onDrag: constructs a message from a TreeDrag (source → target)
{-# TERMINATING #-}
draggableTree : ∀ {M A}
              → (String → M → Bool)   -- is node expanded
              → (String → A)          -- toggle expansion
              → (String → A)          -- node click
              → (TreeDrag → A)        -- drag-drop reorder
              → List (TreeNode A)
              → Node M A
draggableTree {M} {A} isExpanded toggleNode onNodeClick onDrag roots =
  div ( class "agdelte-tree" ∷ [] )
    (renderNodes 0 roots)
  where
    open import Agda.Builtin.String using (primShowNat)
    open import Data.Nat using (_*_)
    open import Data.String renaming (_++_ to _++ˢ_)
    open import Data.List using (_++_)

    depthPadding : ℕ → String
    depthPadding d = primShowNat (d * depthPaddingUnit) ++ˢ "px"

    lazyChildren : String → List (TreeNode A) → M → List (TreeNode A)
    lazyChildren nid cs m = if isExpanded nid m then cs else []

    mutual
      renderNode : ℕ → TreeNode A → Node M A
      renderNode depth node =
        div ( class "agdelte-tree__node"
            ∷ style "padding-left" (depthPadding depth)
            ∷ [] )
          ( div ( class "agdelte-tree__header" ∷ [] )
              ( (if hasChildren node
                 then button ( attrBind "class" (mkBinding
                                 (λ m → if isExpanded (nodeId node) m
                                        then "agdelte-tree__toggle agdelte-tree__toggle--open"
                                        else "agdelte-tree__toggle")
                                 eqStr)
                             ∷ onClick (toggleNode (nodeId node))
                             ∷ [] )
                        ( text "▶" ∷ [] )
                      ∷ []
                 else span ( class "agdelte-tree__spacer" ∷ [] ) [] ∷ [])
              ++ ( button ( class "agdelte-tree__label"
                          ∷ attr "draggable" "true"
                          ∷ on "dragstart" (onDrag (mkTreeDrag (nodeId node) ""))
                          ∷ on "dragover" (onDrag (mkTreeDrag "" (nodeId node)))
                          ∷ on "drop" (onDrag (mkTreeDrag "" (nodeId node)))
                          ∷ onClick (onNodeClick (nodeId node))
                          ∷ [] )
                     ( text (nodeLabel node) ∷ [] )
                 ∷ [] ) )
          ∷ (if hasChildren node
             then div ( class "agdelte-tree__children" ∷ [] )
                    ( foreach (lazyChildren (nodeId node) (nodeChildren node))
                        (λ child _ → renderNode (suc depth) child)
                    ∷ [] )
                  ∷ []
             else []) )

      renderNodes : ℕ → List (TreeNode A) → List (Node M A)
      renderNodes _ [] = []
      renderNodes depth (n ∷ ns) = renderNode depth n ∷ renderNodes depth ns

------------------------------------------------------------------------
-- Convenience constructors
------------------------------------------------------------------------

-- | Create leaf node (no children)
leaf : ∀ {A} → String → String → TreeNode A
leaf id lbl = mkTreeNode id lbl []

-- | Create branch node (has children)
branch : ∀ {A} → String → String → List (TreeNode A) → TreeNode A
branch id lbl children = mkTreeNode id lbl children
