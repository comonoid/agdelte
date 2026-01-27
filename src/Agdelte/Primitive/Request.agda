{-# OPTIONS --without-K --guardedness #-}

-- Request: HTTP запросы

module Agdelte.Primitive.Request where

open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe)
open import Agdelte.Core.Event

------------------------------------------------------------------------
-- HTTP Request Types
------------------------------------------------------------------------

-- Метод запроса
data Method : Set where
  GET POST PUT DELETE PATCH : Method

-- Конфигурация запроса
record RequestConfig : Set where
  constructor mkRequest
  field
    method  : Method
    url     : String
    body    : Maybe String
    headers : List (String × String)

open RequestConfig public

-- Результат запроса
data Response (A : Set) : Set where
  success : A → Response A
  failure : String → Response A

------------------------------------------------------------------------
-- HTTP Request Events
------------------------------------------------------------------------

postulate
  -- Выполнить HTTP запрос
  httpRequest : ∀ {A B : Set}
              → RequestConfig
              → (String → A)    -- onSuccess (JSON string)
              → (String → A)    -- onError
              → Event A

  -- GET запрос
  httpGet : ∀ {A : Set}
          → String           -- URL
          → (String → A)     -- onSuccess
          → (String → A)     -- onError
          → Event A

  -- POST запрос
  httpPost : ∀ {A : Set}
           → String          -- URL
           → String          -- Body (JSON)
           → (String → A)    -- onSuccess
           → (String → A)    -- onError
           → Event A

{-# COMPILE JS httpRequest = _ => _ => config => onSuccess => onError => ({
  type: 'request',
  config: {
    method: config.method,
    url: config.url,
    body: config.body,
    headers: config.headers,
    onSuccess,
    onError
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS httpGet = _ => url => onSuccess => onError => ({
  type: 'request',
  config: {
    method: 'GET',
    url,
    onSuccess,
    onError
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS httpPost = _ => url => body => onSuccess => onError => ({
  type: 'request',
  config: {
    method: 'POST',
    url,
    body,
    headers: { 'Content-Type': 'application/json' },
    onSuccess,
    onError
  },
  now: [],
  get next() { return this; }
}) #-}

------------------------------------------------------------------------
-- Утилиты
------------------------------------------------------------------------

-- Простой GET без обработки ошибок (возвращает Maybe)
simpleGet : ∀ {A : Set}
          → String
          → (String → A)
          → A              -- Значение при ошибке
          → Event A
simpleGet url onSuccess onError =
  httpGet url onSuccess (λ _ → onError)
