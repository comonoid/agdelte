{-# OPTIONS --without-K #-}

-- Event: дискретные события как AST (описание подписок)
-- Runtime интерпретирует это описание и создаёт реальные подписки

module Agdelte.Core.Event where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; if_then_else_)
open import Data.String using (String)
open import Agda.Builtin.String using (primStringEquality)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; id)

private
  variable
    A B C : Set

------------------------------------------------------------------------
-- WebSocket Message
------------------------------------------------------------------------

data WsMsg : Set where
  WsConnected : WsMsg
  WsMessage   : String → WsMsg
  WsClosed    : WsMsg
  WsError     : String → WsMsg

------------------------------------------------------------------------
-- KeyboardEvent
------------------------------------------------------------------------

record KeyboardEvent : Set where
  constructor mkKeyboardEvent
  field
    key   : String
    code  : String
    ctrl  : Bool
    alt   : Bool
    shift : Bool
    meta  : Bool

open KeyboardEvent public

------------------------------------------------------------------------
-- Event как data type (AST) — остаётся в Set
------------------------------------------------------------------------

data Event (A : Set) : Set where
  -- Пустое событие
  never : Event A

  -- === Примитивы времени ===
  interval : ℕ → A → Event A
  timeout  : ℕ → A → Event A

  -- === Клавиатура ===
  -- Обработчик возвращает Maybe A (nothing = игнорировать)
  onKeyDown : (KeyboardEvent → Maybe A) → Event A
  onKeyUp   : (KeyboardEvent → Maybe A) → Event A

  -- === HTTP ===
  httpGet  : String → (String → A) → (String → A) → Event A
  httpPost : String → String → (String → A) → (String → A) → Event A

  -- === WebSocket ===
  -- wsConnect url → Event с сообщениями о состоянии соединения
  wsConnect : String → (WsMsg → A) → Event A

  -- === Routing ===
  -- Событие при изменении URL (popstate)
  onUrlChange : (String → A) → Event A

  -- === Комбинаторы ===
  merge    : Event A → Event A → Event A
  debounce : ℕ → Event A → Event A    -- задержка после паузы
  throttle : ℕ → Event A → Event A    -- ограничение частоты

------------------------------------------------------------------------
-- mapE — функция, не конструктор (чтобы Event ∈ Set)
------------------------------------------------------------------------

mapE : (A → B) → Event A → Event B
mapE f never = never
mapE f (interval n a) = interval n (f a)
mapE f (timeout n a) = timeout n (f a)
mapE f (onKeyDown h) = onKeyDown (λ e → Data.Maybe.map f (h e))
  where import Data.Maybe
mapE f (onKeyUp h) = onKeyUp (λ e → Data.Maybe.map f (h e))
  where import Data.Maybe
mapE f (httpGet url onOk onErr) = httpGet url (f ∘ onOk) (f ∘ onErr)
mapE f (httpPost url body onOk onErr) = httpPost url body (f ∘ onOk) (f ∘ onErr)
mapE f (wsConnect url h) = wsConnect url (f ∘ h)
mapE f (onUrlChange h) = onUrlChange (f ∘ h)
mapE f (merge e₁ e₂) = merge (mapE f e₁) (mapE f e₂)
mapE f (debounce n e) = debounce n (mapE f e)
mapE f (throttle n e) = throttle n (mapE f e)

------------------------------------------------------------------------
-- filterE — через mapE с Maybe
------------------------------------------------------------------------

filterE : (A → Bool) → Event A → Event A
filterE p never = never
filterE p (interval n a) = if p a then interval n a else never
filterE p (timeout n a) = if p a then timeout n a else never
filterE p (onKeyDown h) = onKeyDown (λ e → filterMaybe p (h e))
  where
    filterMaybe : (A → Bool) → Maybe A → Maybe A
    filterMaybe p nothing = nothing
    filterMaybe p (just a) = if p a then just a else nothing
filterE p (onKeyUp h) = onKeyUp (λ e → filterMaybe p (h e))
  where
    filterMaybe : (A → Bool) → Maybe A → Maybe A
    filterMaybe p nothing = nothing
    filterMaybe p (just a) = if p a then just a else nothing
filterE p (httpGet url onOk onErr) = httpGet url onOk onErr  -- фильтр применится в runtime
filterE p (httpPost url body onOk onErr) = httpPost url body onOk onErr
filterE p (wsConnect url h) = wsConnect url h  -- фильтр на WsMsg не имеет смысла
filterE p (onUrlChange h) = onUrlChange h      -- фильтр на URL не имеет смысла
filterE p (merge e₁ e₂) = merge (filterE p e₁) (filterE p e₂)
filterE p (debounce n e) = debounce n (filterE p e)
filterE p (throttle n e) = throttle n (filterE p e)

------------------------------------------------------------------------
-- Удобные конструкторы для клавиатуры
------------------------------------------------------------------------

-- Подписка на конкретную клавишу (создаёт один listener)
onKey : String → A → Event A
onKey k msg = onKeyDown (λ e → if primStringEquality k (KeyboardEvent.key e) then just msg else nothing)

-- Подписка на несколько клавиш (ОДИН listener, эффективно!)
-- Использование: onKeys (("ArrowUp" , MoveUp) ∷ ("ArrowDown" , MoveDown) ∷ [])
onKeys : List (String × A) → Event A
onKeys pairs = onKeyDown (λ e → lookupKey (KeyboardEvent.key e) pairs)
  where
    lookupKey : String → List (String × A) → Maybe A
    lookupKey _ [] = nothing
    lookupKey k ((k' , v) ∷ rest) =
      if primStringEquality k k' then just v else lookupKey k rest

-- Гибкая подписка с предикатом (для сочетаний клавиш)
-- Использование: onKeyWhen (λ e → ctrl e ∧ key e ≡ᵇ "s") Save
onKeyWhen : (KeyboardEvent → Bool) → A → Event A
onKeyWhen pred msg = onKeyDown (λ e → if pred e then just msg else nothing)

-- Сочетания с модификаторами
onCtrlKey : String → A → Event A
onCtrlKey k msg = onKeyWhen (λ e → ctrl e ∧ primStringEquality k (key e)) msg
  where open import Data.Bool using (_∧_)

onAltKey : String → A → Event A
onAltKey k msg = onKeyWhen (λ e → alt e ∧ primStringEquality k (key e)) msg
  where open import Data.Bool using (_∧_)

onShiftKey : String → A → Event A
onShiftKey k msg = onKeyWhen (λ e → shift e ∧ primStringEquality k (key e)) msg
  where open import Data.Bool using (_∧_)

onMetaKey : String → A → Event A
onMetaKey k msg = onKeyWhen (λ e → meta e ∧ primStringEquality k (key e)) msg
  where open import Data.Bool using (_∧_)

-- Стрелки (для удобства, но лучше использовать onKeys для множества)
onArrowUp : A → Event A
onArrowUp msg = onKey "ArrowUp" msg

onArrowDown : A → Event A
onArrowDown msg = onKey "ArrowDown" msg

onArrowLeft : A → Event A
onArrowLeft msg = onKey "ArrowLeft" msg

onArrowRight : A → Event A
onArrowRight msg = onKey "ArrowRight" msg

-- Специальные клавиши
onEnter : A → Event A
onEnter msg = onKey "Enter" msg

onEscape : A → Event A
onEscape msg = onKey "Escape" msg

onSpace : A → Event A
onSpace msg = onKey " " msg

------------------------------------------------------------------------
-- Хелперы для keyUp (для отслеживания одновременных нажатий)
------------------------------------------------------------------------

-- Подписка на отпускание конкретной клавиши
onKeyReleased : String → A → Event A
onKeyReleased k msg = onKeyUp (λ e → if primStringEquality k (KeyboardEvent.key e) then just msg else nothing)

-- Подписка на отпускание нескольких клавиш (один listener)
onKeysUp : List (String × A) → Event A
onKeysUp pairs = onKeyUp (λ e → lookupKey (KeyboardEvent.key e) pairs)
  where
    lookupKey : String → List (String × A) → Maybe A
    lookupKey _ [] = nothing
    lookupKey k ((k' , v) ∷ rest) =
      if primStringEquality k k' then just v else lookupKey k rest

-- Гибкая подписка на keyUp с предикатом
onKeyUpWhen : (KeyboardEvent → Bool) → A → Event A
onKeyUpWhen pred msg = onKeyUp (λ e → if pred e then just msg else nothing)

------------------------------------------------------------------------
-- Комбинаторы
------------------------------------------------------------------------

-- Слияние списка событий
mergeAll : List (Event A) → Event A
mergeAll [] = never
mergeAll (e ∷ es) = merge e (mergeAll es)

-- Инфиксный merge
_<|>_ : Event A → Event A → Event A
_<|>_ = merge

infixr 3 _<|>_

-- Инфиксный mapE
_<$>_ : (A → B) → Event A → Event B
_<$>_ = mapE

infixl 4 _<$>_

------------------------------------------------------------------------
-- Периодические события
------------------------------------------------------------------------

everySecond : A → Event A
everySecond msg = interval 1000 msg

everyMinute : A → Event A
everyMinute msg = interval 60000 msg
