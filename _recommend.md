# Code Review: проблемы в .agda и .hs файлах (логика ядра)

Область: `src/Agdelte/` — Core, Concurrent, Reactive, FFI, Anim, Data, Css + `hs/`.
Ревизия: 2026-03-11 (полный анализ всех ~60 файлов ядра).

---

## 1. [Critical] Css/Show.agda: Отсутствует `Data.Text` импорт в GHC FOREIGN прагме

**Файл:** `src/Agdelte/Css/Show.agda:32-33`

```agda
{-# FOREIGN GHC import Numeric (showFFloat) #-}
{-# COMPILE GHC showFloat = \f -> Data.Text.pack (showFFloat Nothing f "") #-}
```

`Data.Text.pack` используется в COMPILE GHC, но `Data.Text` не импортирован через FOREIGN GHC.
Это приведёт к ошибке компиляции при сборке для GHC бэкенда.

**Исправление:** Добавить импорт `Data.Text`:

```agda
{-# FOREIGN GHC import Numeric (showFFloat) #-}
{-# FOREIGN GHC import qualified Data.Text #-}
{-# COMPILE GHC showFloat = \f -> Data.Text.pack (showFFloat Nothing f "") #-}
```

---

## 2. [High] FFI/Server.agda wireAgent: stepIO не защищён от исключений — deadlock MVar

**Файл:** `src/Agdelte/FFI/Server.agda:290-298`

```agda
stepIO input =
  takeMVar agentMVar >>= λ a →
  let result   = stepAgent a input
      newAgent = proj₁ result
      output   = proj₂ result
  in writeIORef stateRef output >>
     putMVar agentMVar newAgent >>
     pure output
```

Комментарий утверждает: "step/writeIORef are pure/non-throwing — exception safety is not a concern here". Это **неверно** в общем случае:

- `debugTrap` из `Wiring.Debug` компилируется как `throw new Error(...)` (JS) / рантайм-исключение (GHC). Агент, использующий `_⊕!_`, может бросить исключение при несовпадении тегов.
- При исключении между `takeMVar` и `putMVar`, MVar остаётся пустым навсегда → **deadlock** всех последующих `stepIO` и `observeIO`.
- Stack overflow в глубокой рекурсии чистой функции тоже бросит исключение.

`observeIO` корректно использует `bracket` — `stepIO` должен делать то же самое.

**Исправление:** Использовать `bracket` или `onException`:

```agda
stepIO input =
  bracket (takeMVar agentMVar)
          (putMVar agentMVar)   -- восстановить MVar даже при исключении
          (λ a →
    let result   = stepAgent a input
        newAgent = proj₁ result
        output   = proj₂ result
    in writeIORef stateRef output >>
       putMVar agentMVar newAgent >>  -- bracket вернёт старый, но мы уже положили новый
       pure output)
```

Примечание: здесь возникает тонкость — если step успешен, `putMVar` внутри лямбды кладёт новый агент, а cleanup от bracket пытается положить старого повторно (MVar уже не пуст). Нужна более аккуратная схема, например:

```haskell
stepIO input = mask $ \restore -> do
  a <- takeMVar agentMVar
  let result = stepAgent a input
      newAgent = proj₁ result
      output = proj₂ result
  (writeIORef stateRef output >> putMVar agentMVar newAgent >> pure output)
    `onException` putMVar agentMVar a
```

Это потребует добавить `mask` и `onException` в FFI/Server.agda postulates.

---

## 3. [High] Reactive/Inspector.agda slotStatefulOptic: та же проблема с MVar

**Файл:** `src/Agdelte/Reactive/Inspector.agda:91-95`

```agda
(λ input →
  takeMVar mv >>= λ st →
  let newSt = step a st input
  in putMVar mv newSt >>
     pure (just (observe a newSt)))
```

`ioOver` в `slotStatefulOptic` использует ту же паттерн `takeMVar ... putMVar` без защиты от исключений. Если `step a st input` бросит исключение (аналогично п. 2), MVar останется пустым.

В отличие от `wireAgent`, здесь `ioPeek` тоже уязвим — `bracket (takeMVar mv) (putMVar mv) (...)` корректен только если action не модифицирует MVar, что здесь так (peek только читает). Но `ioOver` не использует bracket.

**Исправление:** Аналогично п. 2 — обернуть в bracket или onException.

---

## 4. [Medium] Node.agda zoomNode': TERMINATING прагма устранима

**Файл:** `src/Agdelte/Reactive/Node.agda:346`

```agda
{-# TERMINATING #-}
zoomNode' : ∀ {M M' Msg Msg'} → (M → M') → (Msg' → Msg) → Node M' Msg' → Node M Msg
```

Комментарий верно отмечает, что `map` скрывает структурную рекурсию. Однако TERMINATING — это глобальное ослабление проверки терминации. Если в будущем добавится баг с бесконечной рекурсией, Agda не поймает его.

**Исправление:** Вынести рекурсию по спискам в mutual-определение:

```agda
mutual
  zoomNode' : ... → Node M' Msg' → Node M Msg
  zoomNode' get wrap (elem tag attrs children) =
    elem tag (zoomAttrs get wrap attrs) (zoomNodes get wrap children)
  ...

  zoomNodes : ... → List (Node M' Msg') → List (Node M Msg)
  zoomNodes get wrap [] = []
  zoomNodes get wrap (n ∷ ns) = zoomNode' get wrap n ∷ zoomNodes get wrap ns

  zoomAttrs : ... → List (Attr M' Msg') → List (Attr M Msg)
  zoomAttrs get wrap [] = []
  zoomAttrs get wrap (a ∷ as) = zoomAttr get wrap a ∷ zoomAttrs get wrap as
```

Это устранит TERMINATING без изменения семантики.

---

## 5. [Medium] Task._>>=_: onErr продолжает через bind — неочевидная семантика

**Файл:** `src/Agdelte/Core/Task.agda:80`

```agda
httpGet url onOk onErr >>= f = httpGet url (λ s → onOk s >>= f) (λ e → onErr e >>= f)
```

Bind **пропускает** результат error-хэндлера через `f`. Это значит:

```agda
-- Пример: httpGet с recovery
let task = httpGet url (λ s → pure s) (λ _ → pure "fallback")
-- task >>= f  при ошибке: onErr "..." >>= f = pure "fallback" >>= f = f "fallback"
```

Вызывающий код может не ожидать, что `f` будет вызван со значением из error-хэндлера. Документировано через `_>>=!_` (альтернатива), но в `_>>=_` это **неочевидное поведение по умолчанию**.

Код задокументирован, но рекомендация: **инвертировать дефолт** — сделать `_>>=_` error-terminal (текущий `_>>=!_`), а текущий `_>>=_` переименовать в `_>>=+_` или `bindPreserve`. Причина: подавляющее большинство Task bind-цепочек не ожидают, что ошибки продолжат выполнение pipeline.

---

## 6. [Medium] Concurrent/CoSession.agda splice: молчаливый drop right-веток для send/recv

**Файл:** `src/Agdelte/Concurrent/CoSession.agda:147-153`

```agda
right (splice s k) with head s
... | doneStep    = right k
... | sendStep _  = coDone
... | recvStep _  = coDone
... | _           = splice (right s) k
```

Для `sendStep` и `recvStep` правая ветка **принудительно заменяется на `coDone`**, даже если оригинальная CoSession имела нетривиальную правую ветку. Комментарий предупреждает об инварианте, но:

- Инвариант не проверяется — конструктор `CoSession` является coinductive record и позволяет произвольные `right`.
- `splice` молча обрезает данные без предупреждения.
- `embedSession` (строка 163) гарантирует инвариант, но `repeatN` работает с произвольными `CoSession`.

**Рекомендация:** Добавить `assert` или документированный предикат `wellFormed : CoSession → Bool`, который проверяет инвариант `right = coDone` для `sendStep`/`recvStep`.

---

## 7. [Medium] FFI/Browser.agda: чистые постулаты с побочными эффектами

**Файл:** `src/Agdelte/FFI/Browser.agda:62-66`

```agda
postulate
  consoleLog   : String → ⊤
  consoleWarn  : String → ⊤
  consoleError : String → ⊤
```

Типы объявлены как **чистые функции** (`String → ⊤`), но выполняют IO. Комментарий предупреждает о будущих оптимизациях JS backend (CSE/DCE), но проблема актуальна **уже сейчас**:

- Agda может выполнить CSE: `let x = consoleLog "a" in x ; x` → один вызов вместо двух.
- Мёртвый код: если результат `⊤` не используется, компилятор может удалить вызов.

Текущий JS backend не оптимизирует, но это **бомба замедленного действия**.

**Исправление:** Использовать `IO ⊤` вместо `⊤`:

```agda
postulate consoleLog : String → IO ⊤
{-# COMPILE JS consoleLog = function(s) { return () => { console.log(s); return null; }; } #-}
```

Это требует изменения сигнатур вызывающего кода — можно добавить `unsafePerformIO`-обёртки для обратной совместимости.

---

## 8. [Low] Forms.agda isFieldValid: untouched поле возвращает false

**Файл:** `src/Agdelte/Forms.agda:322-323`

```agda
isFieldValid : ∀ {A : Set} → FormField A → Bool
isFieldValid f = fieldTouched f ∧ null (fieldErrors f)
```

`newField "name" "valid-value" required` создаёт поле с `fieldTouched = false`, `fieldErrors = []`. Вызов `isFieldValid` возвращает `false`, хотя значение валидно.

Следствие: `getValidValue` на начальное состояние формы всегда возвращает `nothing`, даже если все поля имеют валидные начальные значения.

Это задокументировано, но при программировании формы с предзаполненными данными (edit form) это ловушка. Пользователю нужно вызвать `touchField` для каждого предзаполненного поля.

**Рекомендация:** Добавить `initFieldTouched` или `isFieldValueValid` (без проверки touched):

```agda
isFieldValueValid : ∀ {A : Set} → FormField A → Bool
isFieldValueValid f = null (fieldValidator f (fieldValue f))
```

---

## 9. [Low] Json.agda decodeValue: рекурсивный toJS без ограничения глубины

**Файл:** `src/Agdelte/Json.agda:401-415`

```javascript
function toJS(v) { return v(dispatch); }
```

`toJS` рекурсивно обходит `jArray` и `jObject`. Для глубоко вложенных JSON-структур (> ~10000 уровней) это вызовет stack overflow в JS. Это маловероятно для реальных данных, но вредоносный JSON (или ошибка генерации) может крашнуть приложение.

**Рекомендация:** Низкоприоритетно. При необходимости — итеративный обход с explicit stack.

---

## 10. [Low] Css/Color.agda: hex-значения не валидируются

**Файл:** `src/Agdelte/Css/Color.agda:31`

```agda
showColor (hex s) = s
```

`hex "не-цвет"` скомпилируется без ошибок и произведёт невалидный CSS. Комментарий предупреждает об этом (строка 30), но нет compile-time или runtime проверки.

**Рекомендация:** Низкоприоритетно. Для строгих проектов — добавить смарт-конструктор с проверкой формата:

```agda
hexValid : String → Maybe Color
hexValid s = if isHexColor s then just (hex s) else nothing
```

---

## 11. [Low] DateTime.agda: subDuration может создать дату до epoch

**Файл:** `src/Agdelte/DateTime.agda:192-194`

```javascript
{-# COMPILE JS subDuration = function(dur) { return function(d) {
  const ms = dur({mkDuration: ms => ms});
  return new Date(d.getTime() - Number(ms));
}; } #-}
```

`subDuration (days 100) (fromMillis 0)` создаст дату с отрицательным timestamp. JS `Date` это поддерживает, но `getTime` вернёт отрицательное число. Тип `getTime : Date → ℕ` (натуральное число) не может представить отрицательное значение — `BigInt(Math.max(0, d.getTime()))` (строка 157) обрежет до 0.

Следствие: `getTime (subDuration d₁ d₂)` может вернуть 0 вместо реального timestamp, молча теряя информацию.

**Рекомендация:** Либо ограничить `subDuration` через `Maybe Date` (ничего при underflow), либо изменить `getTime` на `ℤ` (целое число).

---

## 12. [Info] Общие замечания по прагмам безопасности

Следующие прагмы используются осознанно и задокументированы, но стоит отслеживать:

| Прагма | Файл | Причина |
|---|---|---|
| `NO_POSITIVITY_CHECK` | `Core/Event.agda:205` | `switchE : Event (Event A)` — самоприменение |
| `NO_UNIVERSE_CHECK` | `Core/Event.agda:206` | `foldE` количественно по скрытому `B : Set` |
| `NO_POSITIVITY_CHECK` | `Json.agda:26` | `jArray : Array JsonValue → JsonValue` |
| `NO_UNIVERSE_CHECK` | `Concurrent/CoSession.agda:37` | `SessionStep` хранит `Set`-level типы |
| `NO_UNIVERSE_CHECK` | `Reactive/Node.agda:76,96` | `foreach`/`glCanvas` количественно по `A : Set` |
| `NO_UNIVERSE_CHECK` | `Concurrent/Obligation.agda:34` | `bindS` количественно по `B : Set` |
| `TERMINATING` | `Reactive/Node.agda:346` | `zoomNode'` — `map` скрывает рекурсию (устранимо, п. 4) |
| `postulate debugTrap` | `Concurrent/Wiring/Debug.agda:29` | Inhabits every type — **unsafe** |

Рекомендация: для `debugTrap` убедиться, что модули, использующие `_⊕!_`, **не попадают** в production builds.
