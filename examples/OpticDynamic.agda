{-# OPTIONS --without-K #-}

-- OpticDynamic: Dynamic optic navigation
-- Demonstrates: ixList (indexed access), Traversal (batch ops),
--   _∘O_ (runtime optic composition), peek (safe access)

module OpticDynamic where

open import Data.Nat using (ℕ; zero; suc; pred; _+_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; [_]; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_; id)

open import Agdelte.Core.Event
open import Agdelte.Reactive.Node
open import Agdelte.Reactive.Optic

------------------------------------------------------------------------
-- Item (with stable ID for keyed reconciliation)
------------------------------------------------------------------------

record Item : Set where
  constructor mkItem
  field
    itemId    : ℕ
    itemLabel : String
    itemValue : ℕ

open Item public

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    items    : List Item
    selected : ℕ          -- selected item ID (not positional index!)
    nextId   : ℕ

open Model public

initialModel : Model
initialModel = mkModel
  ( mkItem 0 "Alpha" 3
  ∷ mkItem 1 "Beta" 7
  ∷ mkItem 2 "Gamma" 1
  ∷ [] )
  0
  3

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  Select      : ℕ → Msg    -- select by item ID
  IncSelected : Msg
  DecSelected : Msg
  ResetAll    : Msg
  AddItem     : Msg

------------------------------------------------------------------------
-- Helpers: find item by stable ID
------------------------------------------------------------------------

lookupById : ℕ → List Item → Maybe Item
lookupById _ [] = nothing
lookupById tid (i ∷ is) = if itemId i ≡ᵇ tid then just i else lookupById tid is

-- Find positional index by item ID (for ixList)
findIndexById : ℕ → List Item → ℕ
findIndexById _ [] = 0
findIndexById tid (i ∷ is) = if itemId i ≡ᵇ tid then 0 else suc (findIndexById tid is)

-- Show item value by ID (for reactive binding inside foreachKeyed)
showValueById : ℕ → Model → String
showValueById tid m with lookupById tid (items m)
... | nothing = "?"
... | just i  = show (itemValue i)

------------------------------------------------------------------------
-- Optics: dynamic navigation
------------------------------------------------------------------------

-- Lens into Model's items list
itemsLens : Lens Model (List Item)
itemsLens = mkLens items (λ is m → record m { items = is })

-- Dynamic optic: navigate to the n-th item inside Model
--   Composes at RUNTIME based on current selection:
--   fromAffine (ixList n) ∘O fromLens itemsLens
--
-- This is the key difference from static Lens composition:
-- the target changes based on user interaction!
nthItemOptic : ℕ → Optic Model Item
nthItemOptic n = fromAffine (ixList n) ∘O fromLens itemsLens

-- Optic to selected item: find position by ID, then use ixList
selectedOptic : Model → Optic Model Item
selectedOptic m = nthItemOptic (findIndexById (selected m) (items m))

-- Traversal over all items for batch operations
allItemsTraversal : Traversal Model Item
allItemsTraversal = mkTraversal items (λ f m → record m { items = map f (items m) })

------------------------------------------------------------------------
-- Update: optic-based modification
------------------------------------------------------------------------

incValue : Item → Item
incValue i = record i { itemValue = suc (itemValue i) }

decValue : Item → Item
decValue i = record i { itemValue = pred (itemValue i) }

resetValue : Item → Item
resetValue i = record i { itemValue = 0 }

updateModel : Msg → Model → Model
-- Select: change focus by item ID
updateModel (Select tid) m = record m { selected = tid }
-- Inc/Dec: dynamic optic navigates to selected item
updateModel IncSelected m = over (selectedOptic m) incValue m
updateModel DecSelected m = over (selectedOptic m) decValue m
-- ResetAll: traversal modifies ALL items at once
updateModel ResetAll m = over (fromTraversal allItemsTraversal) resetValue m
-- AddItem: prepend new item, select it by ID
updateModel AddItem m = mkModel
  (mkItem (nextId m) ("Item-" ++ show (nextId m)) 0 ∷ items m)
  (nextId m)
  (suc (nextId m))

------------------------------------------------------------------------
-- Template
------------------------------------------------------------------------

sumValues : List Item → ℕ
sumValues [] = 0
sumValues (i ∷ is) = itemValue i + sumValues is

totalText : Model → String
totalText m = "Total: " ++ show (sumValues (items m))

selectedText : Model → String
selectedText m with peek (selectedOptic m) m
... | nothing   = "Selected: (none)"
... | just item = "Selected: " ++ itemLabel item ++ " = " ++ show (itemValue item)

countText : Model → String
countText m = show (length (items m)) ++ " items"

itemKey : Item → String
itemKey i = show (itemId i)

viewItem : Item → ℕ → Node Model Msg
viewItem item _idx =
  let iid = itemId item in
  li ( onClick (Select iid)
     ∷ classBind (λ m → if selected m ≡ᵇ iid then "item selected" else "item")
     ∷ [] )
    ( span [ class "item-label" ] [ text (itemLabel item) ]
    ∷ span [ class "item-value" ] [ bindF (showValueById iid) ]
    ∷ [] )

opticDynamicTemplate : Node Model Msg
opticDynamicTemplate =
  div [ class "optic-dynamic-demo" ]
    ( div [ class "info-panel" ]
        ( p [ class "total" ] [ bindF totalText ]
        ∷ p [ class "selected-info" ] [ bindF selectedText ]
        ∷ p [ class "count-info" ] [ bindF countText ]
        ∷ [] )

    ∷ div [ class "controls" ]
        ( button (onClick IncSelected ∷ class "btn" ∷ []) [ text "+1 Selected" ]
        ∷ button (onClick DecSelected ∷ class "btn" ∷ []) [ text "−1 Selected" ]
        ∷ button (onClick ResetAll ∷ class "btn reset-btn" ∷ []) [ text "Reset All" ]
        ∷ button (onClick AddItem ∷ class "btn add-btn" ∷ []) [ text "+ Add Item" ]
        ∷ [] )

    ∷ ul [ class "items-list" ]
        [ foreachKeyed items itemKey viewItem ]

    ∷ div [ class "explanation" ]
        ( p [] [ text "selectedOptic m = nthItemOptic (findIndexById (selected m) (items m))" ]
        ∷ p [] [ text "nthItemOptic n = fromAffine (ixList n) ∘O fromLens itemsLens" ]
        ∷ p [] [ text "Inc → over (selectedOptic m) incValue m" ]
        ∷ p [] [ text "ResetAll → over (fromTraversal allItemsTraversal) resetValue m" ]
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

app : ReactiveApp Model Msg
app = mkReactiveApp initialModel updateModel opticDynamicTemplate
