# Модель времени

> Справочник. Концептуальное понимание: [README.md](README.md)

## Такт (Tick)

**Такт** — атомарная единица дискретного времени. Один такт = одна итерация event loop.

```
Такт 0 → Такт 1 → Такт 2 → ...
   │        │        │
   ▼        ▼        ▼
 events   events   events
```

Границы такта определяются **событиями**:
- Каждое внешнее событие (клик, таймер, HTTP ответ) начинает новый такт
- За один такт: получить события → update → обновить подписки → render
- Между тактами система в состоянии покоя (idle)

В терминах браузера: такт ≈ обработка одного события из event queue.

---

## Push-семантика

События "проталкиваются" (push) извне в систему:
- **Внешний мир** → генерирует события (клики, таймеры, HTTP ответы)
- **Runtime** → получает и направляет события в `update`
- **Приложение** → реактивно обновляется

Приложение не опрашивает источники (pull), а получает уведомления (push).

---

## Одновременные события

Если несколько внешних событий происходят "одновременно":

- **Браузер** сериализует их в очередь событий
- **Каждое событие** обрабатывается отдельным тактом
- **Порядок** сохраняется (FIFO)

Исключение: события внутри одного DOM event (например, `input` с несколькими символами при paste) — приходят как один такт со списком.

---

## Почему дискретное время?

Agdelte использует **дискретное время**, а не непрерывное время классического FRP (Conal Elliott).

Классический FRP:
```haskell
type Behavior a = Time → a  -- Time ∈ ℝ (непрерывное)
```

**Проблемы непрерывного времени:**

| Проблема | Описание |
|----------|----------|
| Невычислимость | Компьютер дискретен — непрерывное время это иллюзия |
| Time leaks | `Behavior` может требовать всю историю значений |
| Неопределённость | Когда именно вычислять? При каждом событии? 60 FPS? |
| Накопление thunks | Ленивость приводит к утечкам памяти |

**Решение Agdelte:** время дискретно, такт — атомарная единица.

```
Непрерывное (Conal Elliott):     Дискретное (Agdelte):

  Behavior a = Time → a            Signal a = now + next
  "значение в КАЖДЫЙ момент"       "значение в КАЖДЫЙ ТАКТ"

  Реальность: сэмплируем           Реальность: именно так
  в дискретные моменты             и вычисляем
```

---

## Уровни времени

```
┌─────────────────────────────────────────────────────────────┐
│                  Agdelte Time Architecture                   │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Level 1: Logical Time (такты)                              │
│  ─────────────────────────────                              │
│  • Событие = один такт                                      │
│  • UI: клики, input, HTTP, WebSocket                        │
│  • Между событиями — idle (эффективно!)                     │
│  • Примитивы: interval, keyboard, request                   │
│                                                              │
│  Level 2: Frame Time (кадры)                                │
│  ─────────────────────────────                              │
│  • requestAnimationFrame                                     │
│  • dt = миллисекунды с прошлого кадра                       │
│  • Для: CSS-анимации, transitions, плавные эффекты          │
│  • Примитив: animationFrame                                  │
│                                                              │
│  Level 3: Physics Time (фиксированный шаг)                  │
│  ─────────────────────────────────────────                  │
│  • Фиксированный dt (например, 16ms = 60Hz)                 │
│  • Детерминизм: одинаковый input → одинаковый результат     │
│  • Для: игры, симуляции, физика                             │
│  • Модуль: Agdelte.Physics                                   │
│                                                              │
│  Level 4: Continuous Time — НЕТ                             │
│  ──────────────────────────────                             │
│  • Аппроксимируется через Level 2/3                         │
│  • "Интеграл" = сумма по dt                                 │
│  • Это честно, и это работает                               │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## animationFrame

```agda
animationFrame : Event FrameInfo

record FrameInfo : Set where
  field
    dt  : ℕ    -- миллисекунды с прошлого кадра (обычно 16-17)
    fps : ℕ    -- текущий FPS
```

**Пример: анимация**

```agda
data Msg = Tick FrameInfo | StartAnimation | StopAnimation

record Model : Set where
  field
    position  : ℕ      -- пиксели
    velocity  : ℕ      -- пиксели/секунду
    animating : Bool

app : App Msg Model
app = record
  { init = { position = 0; velocity = 200; animating = false }

  ; update = λ where
      (Tick frame) m → record m
        { position = m.position + m.velocity * frame.dt / 1000 }
      StartAnimation m → record m { animating = true }
      StopAnimation m → record m { animating = false }

  ; view = λ m → div []
      [ div [ style [("transform", "translateX(" ++ show m.position ++ "px)")] ]
          [ text "●" ]
      , button [ onClick (if m.animating then StopAnimation else StartAnimation) ]
          [ text (if m.animating then "Stop" else "Start") ]
      ]

  ; events = λ m →
      if m.animating
      then mapE Tick animationFrame
      else never  -- браузер idle, батарея не тратится
  }
```

**Отличие от interval:**

| | `interval 16` | `animationFrame` |
|--|---------------|------------------|
| Точность | ±4ms (setTimeout) | Синхронизирован с дисплеем |
| FPS info | Нет | Да |
| Батарея | Работает в фоне | Пауза в фоновых вкладках |
| Использование | Периодические задачи | Анимации, игры |

---

## Fixed Timestep (для игр и физики)

Проблема variable timestep:

```
Frame 1: dt = 16ms  → position += velocity * 0.016
Frame 2: dt = 100ms → position += velocity * 0.100  // лаг!
         ↑
    Объект "пролетает" сквозь стену
```

Решение — fixed timestep:

```agda
module Agdelte.Physics where

PHYSICS_HZ : ℕ
PHYSICS_HZ = 60

FIXED_DT : ℕ
FIXED_DT = 1000 / PHYSICS_HZ  -- 16ms

record PhysicsModel (A : Set) : Set where
  field
    current     : A      -- текущее состояние
    previous    : A      -- предыдущее (для интерполяции)
    accumulator : ℕ      -- накопленное время

PhysicsStep : Set → Set
PhysicsStep A = A → A

updatePhysics : PhysicsStep A → ℕ → PhysicsModel A → PhysicsModel A
updatePhysics step dt model = go (record model { accumulator = model.accumulator + dt })
  where
    go m = if m.accumulator >= FIXED_DT
           then go (record m
             { current = step (m.current)
             ; previous = m.current
             ; accumulator = m.accumulator - FIXED_DT
             })
           else m

interpolate : Lerp A → PhysicsModel A → A
interpolate lerp m =
  let alpha = m.accumulator * 1000 / FIXED_DT
  in lerp (m.previous) (m.current) alpha

Lerp : Set → Set
Lerp A = A → A → ℕ → A  -- from → to → alpha(0-1000) → result
```

**Пример: прыгающий мяч**

```agda
record Ball : Set where
  field
    y  : ℤ    -- позиция (миллиметры)
    vy : ℤ    -- скорость (мм/с)

GRAVITY : ℤ
GRAVITY = -9800  -- мм/с²

ballStep : PhysicsStep Ball
ballStep b =
  let newVy = b.vy + GRAVITY * FIXED_DT / 1000
      newY  = b.y + newVy * FIXED_DT / 1000
      (y', vy') = if newY < 0
                  then (0, negate newVy * 80 / 100)  -- отскок
                  else (newY, newVy)
  in record { y = y'; vy = vy' }

lerpBall : Lerp Ball
lerpBall a b alpha = record
  { y  = a.y + (b.y - a.y) * alpha / 1000
  ; vy = b.vy
  }
```

**Преимущества fixed timestep:**

| Свойство | Variable dt | Fixed dt |
|----------|-------------|----------|
| Детерминизм | Зависит от FPS | Всегда одинаково |
| Replay | Нужно сохранять dt | Только input |
| Стабильность | Глитчи при лагах | Физика не ломается |
| Сетевая игра | Рассинхрон | Lockstep возможен |

---

## Сравнение с другими FRP-системами

| Система | Модель времени | Комментарий |
|---------|----------------|-------------|
| Fran (Conal Elliott) | Непрерывное | Красиво математически, проблемы на практике |
| Yampa | Дискретное (SF) | Signal Functions, нет time leaks |
| Reflex | Дискретное | Spider timeline, практичный |
| Elm | Дискретное | Такты по событиям |
| Игровые движки | Fixed timestep | Индустриальный стандарт |
| **Agdelte** | **Дискретное + fixed** | Такты + опциональный fixed timestep |

---

## Итог

```
Событийное время (UI):     Кадровое время (анимации):    Физическое время (игры):

  Event ───► Такт            animationFrame               Fixed timestep
     │                            │                            │
     ▼                            ▼                            ▼
  update                    update(dt)                   updatePhysics(dt)
  render                      render                    interpolate + render
     │                            │                            │
     ▼                            ▼                            ▼
   idle                    requestAnimationFrame         while(acc >= FIXED_DT)
 (ждём событие)              (следующий кадр)              step(FIXED_DT)
```

**Философия:** время дискретно на всех уровнях. Непрерывное время — полезная абстракция для математики, но не для реализации.
