# Agdelte Examples

Примеры демонстрируют возможности Agdelte:

| Пример | Описание | Особенности |
|--------|----------|-------------|
| Counter | Простой счётчик | Базовый Elm Architecture |
| Timer | Секундомер | Event subs (interval) |
| Todo | Список задач | Списки, фильтрация, input handling |
| Keyboard | Управление стрелками | onKeyDown, global keyboard events |
| HttpDemo | HTTP запросы | Cmd (httpGet), one-shot effects |

## Компиляция

### Из корня проекта (рекомендуется)

```bash
# Отдельные примеры
npm run build:counter
npm run build:timer
npm run build:todo
npm run build:keyboard
npm run build:http

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
   - http://localhost:8080/counter.html — Counter
   - http://localhost:8080/timer.html — Timer
   - http://localhost:8080/todo.html — Todo
   - http://localhost:8080/keyboard.html — Keyboard
   - http://localhost:8080/http.html — HTTP

## Структура примера

Каждый пример следует Elm Architecture:

```agda
-- Model: состояние приложения
record Model : Set where ...

-- Msg: сообщения (события)
data Msg : Set where ...

-- update: обновление состояния (остаётся простым!)
update : Msg → Model → Model

-- view: рендеринг HTML
view : Model → Html Msg

-- subs: подписки на события (interval, keyboard)
subs : Model → Event Msg

-- command: команды (HTTP, one-shot effects) — опционально
command : Msg → Model → Cmd Msg

-- app: сборка приложения
app : App Model Msg
app = mkApp init update view subs          -- простые приложения
app = mkCmdApp init update view subs cmd   -- с HTTP
```
