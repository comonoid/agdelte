# Модель времени

> Справочник. Концептуальное понимание: [README.md](README.md)

## Главный принцип: всё дискретно

**В Agdelte нет непрерывного времени.** Вся система построена на дискретных событиях.

```
Event ───► Event ───► Event ───► Event
  │          │          │          │
  ▼          ▼          ▼          ▼
Такт 0    Такт 1    Такт 2    Такт 3
```

- **Signal** — дискретный поток значений (одно значение на такт)
- **Event** — дискретные события (список событий за такт)
- **animationFrame** — дискретный Event, срабатывает каждый кадр
- **interval** — дискретный Event, срабатывает каждые N мс

Никаких функций `Time → A`. Никакого "непрерывного Behavior". Только дискретные события.

---

## Такт (Tick)

**Такт** — атомарная единица времени. Один такт = одна итерация event loop.

```
Внешний мир          Runtime              Приложение
     │                  │                     │
     │  событие         │                     │
     ├─────────────────►│                     │
     │                  │  update(msg, model) │
     │                  ├────────────────────►│
     │                  │                     │
     │                  │  newModel           │
     │                  │◄────────────────────┤
     │                  │                     │
     │                  │  render(view)       │
     │                  ├─────────────────────►
     │                  │                     │
     │                  │  idle...            │
```

Границы такта:
- Каждое внешнее событие (клик, таймер, HTTP ответ) — один такт
- За такт: событие → update → обновить подписки → render
- Между тактами — система idle

---

## Почему не непрерывное время?

Классический FRP (Conal Elliott):
```haskell
type Behavior a = Time → a  -- Time ∈ ℝ (непрерывное)
```

**Проблемы:**

| Проблема | Описание |
|----------|----------|
| Невычислимость | Компьютер дискретен — ℝ не представимо |
| Time leaks | Behavior может требовать всю историю |
| Неопределённость | Когда вычислять? 60 FPS? 120 FPS? |
| Накопление thunks | Ленивость → утечки памяти |

**Решение Agdelte:** отказ от иллюзии непрерывности.

```
Классический FRP:              Agdelte:

  Behavior a = Time → a          Signal a = now + next
  "значение в КАЖДЫЙ момент"     "значение в КАЖДЫЙ ТАКТ"

  Реальность: сэмплируем         Реальность: именно так
  в дискретные моменты           и вычисляем
```

---

## animationFrame — дискретный Event

`animationFrame` — это **обычный Event**, который срабатывает каждый кадр браузера.

```agda
animationFrame : Event FrameInfo

record FrameInfo : Set where
  field
    dt  : ℕ    -- миллисекунды с прошлого события (измерение!)
    fps : ℕ    -- текущий FPS (измерение!)
```

**Ключевое понимание:**
- `animationFrame` — это **не** "непрерывный источник"
- Это дискретные события, ~60 раз в секунду
- `dt` — не "непрерывное время", а измерение интервала между событиями
- `fps` — измеренная частота событий

```agda
events m =
  if m.animating
  then mapE Tick animationFrame  -- подписка на дискретные события
  else never                      -- никаких событий, браузер idle
```

Когда `animating = false`, никаких событий не происходит. Система в idle. Батарея не тратится.

---

## Анимации: интерполяция между дискретными событиями

Для плавных анимаций используем `dt` для интерполяции:

```agda
update (Tick frame) m = record m
  { position = m.position + m.velocity * frame.dt / 1000 }
```

Это **не** непрерывное движение. Это:
1. Получили дискретное событие с `dt = 16`
2. Вычислили новую позицию: `position += velocity * 0.016`
3. Отрендерили
4. Ждём следующее дискретное событие

**Визуально** выглядит плавно (60 FPS достаточно для глаза). **Технически** — дискретные шаги.

---

## Fixed Timestep — паттерн для физики

Проблема variable dt:

```
Событие 1: dt = 16ms  → position += velocity * 0.016
Событие 2: dt = 100ms → position += velocity * 0.100  // лаг!
                        ↑
              Объект "пролетает" сквозь стену
```

**Решение:** фиксированный шаг физики (как в игровых движках).

```agda
-- Это паттерн использования, не примитив!

FIXED_DT : ℕ
FIXED_DT = 16  -- 60 Hz

record PhysicsModel (A : Set) : Set where
  field
    current     : A      -- текущее состояние физики
    previous    : A      -- для интерполяции рендера
    accumulator : ℕ      -- накопленное время

updatePhysics : (A → A) → ℕ → PhysicsModel A → PhysicsModel A
updatePhysics step dt model = go (record model { accumulator = model.accumulator + dt })
  where
    go m = if m.accumulator >= FIXED_DT
           then go (record m
             { current = step m.current
             ; previous = m.current
             ; accumulator = m.accumulator - FIXED_DT
             })
           else m
```

**Как это работает:**

```
animationFrame даёт dt = 100ms (лаг!)

accumulator += 100  -- теперь 100

while accumulator >= 16:
  step()            -- физика с фиксированным dt=16
  accumulator -= 16

-- Выполнилось 6 шагов физики
-- accumulator = 4 (остаток для интерполяции рендера)
```

Физика всегда детерминирована. Один и тот же input → один и тот же результат.

---

## Интерполяция рендера

После физики `accumulator` содержит "остаток" времени. Используем для плавного рендера:

```agda
interpolate : Lerp A → PhysicsModel A → A
interpolate lerp m =
  let alpha = m.accumulator * 1000 / FIXED_DT  -- 0..1000
  in lerp m.previous m.current alpha

Lerp : Set → Set
Lerp A = A → A → ℕ → A  -- from → to → alpha → result
```

```
previous ●────────────────● current
              ↑
         alpha = 0.25
              ↓
           render здесь
```

---

## Пример: прыгающий мяч

```agda
record Ball : Set where
  y  : ℤ    -- позиция (миллиметры)
  vy : ℤ    -- скорость (мм/с)

GRAVITY : ℤ
GRAVITY = -9800  -- мм/с²

ballStep : Ball → Ball
ballStep b =
  let newVy = b.vy + GRAVITY * FIXED_DT / 1000
      newY  = b.y + newVy * FIXED_DT / 1000
  in if newY < 0
     then record { y = 0; vy = negate newVy * 80 / 100 }  -- отскок
     else record { y = newY; vy = newVy }

-- В update:
update (Tick frame) m = record m
  { physics = updatePhysics ballStep frame.dt m.physics }

-- В view:
view m =
  let ball = interpolate lerpBall m.physics
  in div [ style [("transform", "translateY(" ++ show ball.y ++ "mm)")] ]
       [ text "●" ]
```

---

## Сравнение с другими системами

| Система | Модель времени | Комментарий |
|---------|----------------|-------------|
| Fran (Conal Elliott) | Непрерывное (Time → A) | Красиво математически, проблемы на практике |
| Yampa | Дискретное (Signal Functions) | Нет time leaks |
| Reflex | Дискретное | Spider timeline |
| Elm | Дискретное | Такты по событиям |
| Игровые движки | Дискретное + fixed timestep | Индустриальный стандарт |
| **Agdelte** | **Дискретное** | Event + паттерн fixed timestep |

---

## Итог

```
┌─────────────────────────────────────────────────────────────┐
│  БАЗИС: дискретные события (Event)                          │
│                                                             │
│  interval 1000      → Event ⊤     (каждую секунду)         │
│  animationFrame     → Event FrameInfo (каждый кадр)        │
│  keyboard           → Event Key   (при нажатии)            │
│  request            → Event Response (при ответе)          │
│                                                             │
│  Всё — дискретные события. Никакой непрерывности.          │
├─────────────────────────────────────────────────────────────┤
│  ПАТТЕРН: fixed timestep (для физики)                       │
│                                                             │
│  • Накапливаем dt из animationFrame                         │
│  • Выполняем шаги физики с фиксированным FIXED_DT           │
│  • Интерполируем рендер                                     │
│                                                             │
│  Детерминизм, replay, сетевая синхронизация.               │
├─────────────────────────────────────────────────────────────┤
│  "НЕПРЕРЫВНОСТЬ": иллюзия                                   │
│                                                             │
│  • 60 событий/сек визуально неотличимо от непрерывности     │
│  • dt позволяет интерполировать между событиями             │
│  • Технически — дискретные шаги                             │
│                                                             │
│  Это честно. И это работает.                                │
└─────────────────────────────────────────────────────────────┘
```

**Философия:** непрерывное время — полезная абстракция для математики, но иллюзия для реализации. Мы не притворяемся. Всё дискретно.
