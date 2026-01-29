# Agdelte Examples

> See [doc/examples.md](../doc/examples.md) for detailed guide.

Примеры демонстрируют возможности Agdelte:

| Пример | Описание | Особенности |
|--------|----------|-------------|
| ReactiveCounter | Счётчик | Reactive bindings (no VDOM) |
| Timer | Секундомер | Event subs (interval) |
| Todo | Список задач | Списки, фильтрация, input handling |
| Keyboard | Управление стрелками | onKeyDown, global keyboard events |
| HttpDemo | HTTP запросы | Cmd (httpGet) |
| TaskDemo | Цепочка HTTP | Task с do-нотацией |
| WebSocketDemo | Echo-клиент | wsConnect, wsSend |
| RouterDemo | SPA роутинг | pushUrl, onUrlChange |
| CompositionDemo | Два счётчика | _∥_ параллельная композиция |

## Компиляция

### Из корня проекта (рекомендуется)

```bash
# Отдельные примеры
npm run build:counter
npm run build:timer
npm run build:todo
npm run build:keyboard
npm run build:http
npm run build:task
npm run build:websocket
npm run build:router
npm run build:composition

# Все сразу
npm run build:all
```

### Из директории examples

```bash
# Counter
agda --js --js-es6 --js-optimize --compile-dir=../build Counter.agda

# Timer
agda --js --js-es6 --js-optimize --compile-dir=../build Timer.agda

# Todo
agda --js --js-es6 --js-optimize --compile-dir=../build Todo.agda
```

### Только проверка типов (без JS)

```bash
agda Counter.agda
agda Timer.agda
agda Todo.agda
```

## Запуск в браузере

1. Запустить сервер из корня проекта:
   ```bash
   npm run dev
   ```

2. Открыть в браузере:
   - http://localhost:8080/ — главная страница
   - http://localhost:8080/examples_html/counter.html — Counter
   - http://localhost:8080/examples_html/timer.html — Timer
   - http://localhost:8080/examples_html/todo.html — Todo
   - http://localhost:8080/examples_html/keyboard.html — Keyboard
   - http://localhost:8080/examples_html/http.html — HTTP
   - http://localhost:8080/examples_html/task.html — Task Chain
   - http://localhost:8080/examples_html/websocket.html — WebSocket
   - http://localhost:8080/examples_html/router.html — Router
   - http://localhost:8080/examples_html/composition.html — Composition

## Структура примера

Каждый пример использует Reactive Bindings (как Svelte):

```agda
-- Model: состояние приложения
Model = ℕ  -- или record

-- Msg: сообщения (события)
data Msg : Set where
  Inc Dec : Msg

-- update: обновление состояния
update : Msg → Model → Model

-- template: декларативный шаблон с привязками
template : Node Model Msg
template =
  div [ class "counter" ]
    ( button [ onClick Dec ] [ text "-" ]
    ∷ span [ class "count" ] [ bindF show ]   -- auto-updates!
    ∷ button [ onClick Inc ] [ text "+" ]
    ∷ [] )

-- app: сборка приложения
app : ReactiveApp Model Msg
app = mkReactiveApp init update template
```

**Ключевое отличие от Virtual DOM**: `template` — это данные, не функция. Биндинги отслеживают, какие DOM-узлы нужно обновить.
