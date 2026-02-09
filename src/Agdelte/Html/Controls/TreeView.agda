{-# OPTIONS --without-K #-}

-- TreeView: Hierarchical tree structure display
-- CSS classes: .agdelte-tree, .agdelte-tree__node,
--              .agdelte-tree__toggle, .agdelte-tree__label,
--              .agdelte-tree__children

module Agdelte.Html.Controls.TreeView where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node

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
    nodeData     : Maybe A    -- optional associated data

open TreeNode public

------------------------------------------------------------------------
-- Helper
------------------------------------------------------------------------

private
  eqStr : String → String → Bool
  eqStr a b with a ≟ b
  ... | yes _ = true
  ... | no _  = false

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
  div ( class "agdelte-tree" ∷ attr "role" "tree" ∷ [] )
    (renderNodes 0 roots)
  where
    open import Agda.Builtin.String using (primShowNat)
    open import Data.Nat using (_*_)
    open import Data.String using (_++_)

    depthPadding : ℕ → String
    depthPadding d = primShowNat (d * 16) ++ "px"

    hasChildren : TreeNode A → Bool
    hasChildren n with nodeChildren n
    ... | [] = false
    ... | _ = true

    {-# TERMINATING #-}
    mutual
      renderNode : ℕ → TreeNode A → Node M A
      renderNode depth node =
        div ( class "agdelte-tree__node"
            ∷ attr "role" "treeitem"
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
collapsibleTree : ∀ {M A}
                → (String → M → Bool)   -- is node expanded
                → (String → A)          -- toggle expansion
                → (String → A)          -- node click
                → List (TreeNode A)
                → Node M A
collapsibleTree {M} {A} isExpanded toggleNode onNodeClick roots =
  div ( class "agdelte-tree" ∷ attr "role" "tree" ∷ [] )
    (renderNodes 0 roots)
  where
    open import Agda.Builtin.String using (primShowNat)
    open import Data.Nat using (_*_)
    open import Data.String renaming (_++_ to _++ˢ_)
    open import Data.List using (_++_)

    depthPadding : ℕ → String
    depthPadding d = primShowNat (d * 16) ++ˢ "px"

    hasChildren : TreeNode A → Bool
    hasChildren n with nodeChildren n
    ... | [] = false
    ... | _ = true

    {-# TERMINATING #-}
    mutual
      renderNode : ℕ → TreeNode A → Node M A
      renderNode depth node =
        div ( class "agdelte-tree__node"
            ∷ attr "role" "treeitem"
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
             then when (isExpanded (nodeId node))
                    (div ( class "agdelte-tree__children" ∷ [] )
                      (renderNodes (suc depth) (nodeChildren node)))
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
leaf id lbl = mkTreeNode id lbl [] nothing

-- | Create leaf node with data
leafWithData : ∀ {A} → String → String → A → TreeNode A
leafWithData id lbl dat = mkTreeNode id lbl [] (just dat)

-- | Create branch node (has children)
branch : ∀ {A} → String → String → List (TreeNode A) → TreeNode A
branch id lbl children = mkTreeNode id lbl children nothing
