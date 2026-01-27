# FFI Reference

> Справочник JavaScript реализаций. Концептуальное понимание: [README.md](README.md)
>
> **Статус:** Этот документ содержит как реализованные примитивы, так и референсные реализации для будущих фаз.
>
> | Примитив | Статус |
> |----------|--------|
> | interval | ✅ MVP |
> | animationFrame | ✅ MVP |
> | keyboard | 📋 Phase 2 |
> | request | 📋 Phase 2 |
> | websocket | 📋 Phase 2 |
> | debounce, throttle, delay | 📋 Phase 2 |

## Структура примитива

Каждый примитив Event реализуется через FFI:

```agda
-- Agda: объявление
postulate interval : ℕ → Event ⊤
```

```javascript
// JavaScript: реализация
const interval = (ms) => ({
  // Уникальный идентификатор для diff
  _type: 'interval',
  _args: [ms],

  // Вызывается при подписке
  subscribe: (emit) => {
    const id = setInterval(() => emit([null]), ms)
    return id  // возвращаем handle для отписки
  },

  // Вызывается при отписке
  unsubscribe: (id) => {
    clearInterval(id)
  }
})
```

---

## Примитивы

### interval

```javascript
const interval = (ms) => ({
  _type: 'interval',
  _args: [ms],

  subscribe: (emit) => {
    const id = setInterval(() => emit([null]), ms)
    return id
  },

  unsubscribe: (id) => {
    clearInterval(id)
  }
})
```

### animationFrame

```javascript
const animationFrame = {
  _type: 'animationFrame',
  _args: [],

  subscribe: (emit) => {
    let lastTime = performance.now()
    let rafId = null

    // FPS tracking
    let frameCount = 0
    let fpsTime = lastTime
    let currentFps = 60

    const loop = (now) => {
      const dt = Math.round(now - lastTime)
      lastTime = now

      frameCount++
      if (now - fpsTime >= 1000) {
        currentFps = frameCount
        frameCount = 0
        fpsTime = now
      }

      emit([{ dt, fps: currentFps }])
      rafId = requestAnimationFrame(loop)
    }

    rafId = requestAnimationFrame(loop)
    return { rafId, cancel: () => cancelAnimationFrame(rafId) }
  },

  unsubscribe: (handle) => {
    handle.cancel()
  }
}
```

### keyboard

```javascript
const keyboard = {
  _type: 'keyboard',
  _args: [],

  subscribe: (emit) => {
    const handler = (e) => {
      const key = parseKeyEvent(e)
      emit([key])
    }
    document.addEventListener('keydown', handler)
    return handler
  },

  unsubscribe: (handler) => {
    document.removeEventListener('keydown', handler)
  }
}

function parseKeyEvent(e) {
  let key = parseBaseKey(e.key)
  if (e.ctrlKey) key = { tag: 'Ctrl', value: key }
  if (e.altKey) key = { tag: 'Alt', value: key }
  if (e.shiftKey && e.key.length > 1) key = { tag: 'Shift', value: key }
  if (e.metaKey) key = { tag: 'Meta', value: key }
  return key
}

function parseBaseKey(keyStr) {
  if (keyStr.length === 1) {
    return { tag: 'Char', value: keyStr }
  }
  switch (keyStr) {
    case 'Enter': return { tag: 'Enter' }
    case 'Escape': return { tag: 'Escape' }
    case 'Tab': return { tag: 'Tab' }
    case 'Backspace': return { tag: 'Backspace' }
    case 'Delete': return { tag: 'Delete' }
    case 'ArrowUp': return { tag: 'Arrow', value: { tag: 'Up' } }
    case 'ArrowDown': return { tag: 'Arrow', value: { tag: 'Down' } }
    case 'ArrowLeft': return { tag: 'Arrow', value: { tag: 'Left' } }
    case 'ArrowRight': return { tag: 'Arrow', value: { tag: 'Right' } }
    case 'F1': case 'F2': case 'F3': case 'F4': case 'F5': case 'F6':
    case 'F7': case 'F8': case 'F9': case 'F10': case 'F11': case 'F12':
      return { tag: 'F', value: parseInt(keyStr.slice(1)) }
    default: return { tag: 'Other', value: keyStr }
  }
}
```

### request

```javascript
const request = (req) => ({
  _type: 'request',
  _args: [req.method, req.url, req.body],

  subscribe: (emit) => {
    const controller = new AbortController()
    let completed = false

    fetch(req.url, {
      method: req.method,
      body: req.body,
      signal: controller.signal
    })
    .then(resp => resp.json())
    .then(data => {
      if (!completed) {
        completed = true
        emit([{ tag: 'ok', status: 200, body: JSON.stringify(data) }])
      }
    })
    .catch(err => {
      if (!completed && err.name !== 'AbortError') {
        completed = true
        emit([{ tag: 'error', status: 0, msg: err.message }])
      }
    })

    return { controller, isCompleted: () => completed }
  },

  unsubscribe: (handle) => {
    if (!handle.isCompleted()) {
      handle.controller.abort()
    }
  }
})
```

**Одноразовость:** request генерирует ровно одно событие. После этого примитив молчит.

### websocket

```javascript
const wsConnections = new Map()

const websocket = (url) => ({
  recv: {
    _type: 'websocket_recv',
    _args: [url],

    subscribe: (emit) => {
      let conn = wsConnections.get(url)
      if (!conn) {
        const ws = new WebSocket(url)
        conn = { ws, refCount: 0, emitters: new Set() }
        wsConnections.set(url, conn)

        ws.onopen = () => {
          conn.emitters.forEach(e => e([{ tag: 'Connected' }]))
        }
        ws.onmessage = (e) => {
          conn.emitters.forEach(e => e([{ tag: 'Message', value: e.data }]))
        }
        ws.onerror = (e) => {
          conn.emitters.forEach(e => e([{ tag: 'Error', value: e.message || 'Unknown error' }]))
        }
        ws.onclose = () => {
          conn.emitters.forEach(e => e([{ tag: 'Closed' }]))
          wsConnections.delete(url)
        }
      }

      conn.refCount++
      conn.emitters.add(emit)
      return { url, emit }
    },

    unsubscribe: (handle) => {
      const conn = wsConnections.get(handle.url)
      if (conn) {
        conn.emitters.delete(handle.emit)
        conn.refCount--
        if (conn.refCount <= 0) {
          conn.ws.close()
          wsConnections.delete(handle.url)
        }
      }
    }
  },

  send: (msg) => ({
    _type: 'websocket_send',
    _args: [url, msg],

    subscribe: (emit) => {
      const conn = wsConnections.get(url)
      if (conn && conn.ws.readyState === WebSocket.OPEN) {
        conn.ws.send(msg)
        emit([null])
      } else {
        const checkAndSend = () => {
          const c = wsConnections.get(url)
          if (c && c.ws.readyState === WebSocket.OPEN) {
            c.ws.send(msg)
            emit([null])
          } else {
            setTimeout(checkAndSend, 10)
          }
        }
        checkAndSend()
      }
      return null
    },

    unsubscribe: () => {}
  })
})
```

### debounce

```javascript
const debounce = (ms) => (event) => ({
  _type: 'debounce',
  _args: [ms, event],

  subscribe: (emit) => {
    let timerId = null
    let lastValue = null

    const innerUnsub = event.subscribe((values) => {
      if (values.length > 0) {
        lastValue = values[values.length - 1]
        if (timerId) clearTimeout(timerId)
        timerId = setTimeout(() => {
          emit([lastValue])
          timerId = null
        }, ms)
      }
    })

    return { innerUnsub, timerId }
  },

  unsubscribe: ({ innerUnsub, timerId }) => {
    if (timerId) clearTimeout(timerId)
    innerUnsub()
  }
})
```

### throttle

```javascript
const throttle = (ms) => (event) => ({
  _type: 'throttle',
  _args: [ms, event],

  subscribe: (emit) => {
    let lastEmit = 0

    const innerUnsub = event.subscribe((values) => {
      const now = performance.now()
      if (values.length > 0 && now - lastEmit >= ms) {
        emit([values[0]])
        lastEmit = now
      }
    })

    return innerUnsub
  },

  unsubscribe: (innerUnsub) => innerUnsub()
})
```

### delay

```javascript
const delay = (ms) => (event) => ({
  _type: 'delay',
  _args: [ms, event],

  subscribe: (emit) => {
    const timers = []

    const innerUnsub = event.subscribe((values) => {
      values.forEach((v) => {
        const timerId = setTimeout(() => emit([v]), ms)
        timers.push(timerId)
      })
    })

    return { innerUnsub, timers }
  },

  unsubscribe: ({ innerUnsub, timers }) => {
    timers.forEach(t => clearTimeout(t))
    innerUnsub()
  }
})
```

---

## Runtime

### runApp

```javascript
function runApp(app) {
  let model = app.init
  let currentEvents = null
  const subscriptions = new Map()

  function tick(msgs) {
    for (const msg of msgs) {
      model = app.update(msg, model)
    }

    const newEvents = app.events(model)
    updateSubscriptions(currentEvents, newEvents)
    currentEvents = newEvents

    const html = app.view(model)
    render(html)
  }

  function mount(selector) {
    const root = document.querySelector(selector)

    currentEvents = app.events(model)
    subscribe(currentEvents, subscriptions, tick)

    const html = app.view(model)
    root.innerHTML = ''
    root.appendChild(createElement(html, tick))
  }

  return { mount }
}
```

### diffEvents

```javascript
function diffEvents(oldEvent, newEvent, subscriptions, emit) {
  if (oldEvent.type === 'never' && newEvent.type === 'never') {
    return
  }

  if (oldEvent.type === 'never' && newEvent.type !== 'never') {
    subscribe(newEvent, subscriptions, emit)
    return
  }

  if (oldEvent.type !== 'never' && newEvent.type === 'never') {
    unsubscribe(oldEvent, subscriptions)
    return
  }

  if (oldEvent.type === 'merge' && newEvent.type === 'merge') {
    diffEvents(oldEvent.left, newEvent.left, subscriptions, emit)
    diffEvents(oldEvent.right, newEvent.right, subscriptions, emit)
    return
  }

  if ((oldEvent.type === 'map' && newEvent.type === 'map') ||
      (oldEvent.type === 'filter' && newEvent.type === 'filter')) {
    diffEvents(oldEvent.source, newEvent.source, subscriptions, emit)
    return
  }

  if (oldEvent.type === 'primitive' && newEvent.type === 'primitive') {
    const same = oldEvent.primitive._type === newEvent.primitive._type &&
                 deepEqual(oldEvent.primitive._args, newEvent.primitive._args)
    if (same) return

    unsubscribe(oldEvent, subscriptions)
    subscribe(newEvent, subscriptions, emit)
    return
  }

  unsubscribe(oldEvent, subscriptions)
  subscribe(newEvent, subscriptions, emit)
}
```

### subscribe / unsubscribe

```javascript
function subscribe(event, subscriptions, emit) {
  if (event.type === 'never') return

  if (event.type === 'primitive') {
    const handle = event.primitive.subscribe((msgs) => emit(msgs))
    subscriptions.set(event, handle)
    return
  }

  if (event.type === 'merge') {
    subscribe(event.left, subscriptions, emit)
    subscribe(event.right, subscriptions, emit)
    return
  }

  if (event.type === 'map') {
    subscribe(event.source, subscriptions, (msgs) => emit(msgs.map(event.f)))
    return
  }

  if (event.type === 'filter') {
    subscribe(event.source, subscriptions, (msgs) => emit(msgs.filter(event.p)))
    return
  }
}

function unsubscribe(event, subscriptions) {
  if (event.type === 'never') return

  if (event.type === 'primitive') {
    const handle = subscriptions.get(event)
    if (handle) {
      event.primitive.unsubscribe(handle)
      subscriptions.delete(event)
    }
    return
  }

  if (event.type === 'merge') {
    unsubscribe(event.left, subscriptions)
    unsubscribe(event.right, subscriptions)
    return
  }

  if (event.type === 'map' || event.type === 'filter') {
    unsubscribe(event.source, subscriptions)
    return
  }
}
```

---

## Представление Event в runtime

Event в runtime — это дерево:

```javascript
// Примитив (лист)
{ type: 'primitive', primitive: interval(1000) }

// merge (узел)
{ type: 'merge', left: Event, right: Event }

// mapE (узел)
{ type: 'map', f: Function, source: Event }

// filterE (узел)
{ type: 'filter', p: Function, source: Event }

// never (специальный лист)
{ type: 'never' }
```

---

## COMPILE прагмы

```agda
postulate
  interval : ℕ → Event ⊤

{-# COMPILE JS interval =
  function(ms) {
    return {
      _type: 'interval',
      _args: [ms],
      subscribe: function(emit) {
        return setInterval(function() { emit([null]); }, ms);
      },
      unsubscribe: function(id) {
        clearInterval(id);
      }
    };
  }
#-}
```

Для типов данных:

```agda
data Response : Set where
  ok    : Status → Body → Response
  error : Status → String → Response

{-# COMPILE JS Response = data
  | ok    = function(status, body) { return { tag: 'ok', status: status, body: body }; }
  | error = function(status, msg)  { return { tag: 'error', status: status, msg: msg }; }
#-}
```

---

## Сводка примитивов

| Примитив | Тип | Подписка | Отписка |
|----------|-----|----------|---------|
| `interval n` | `Event ⊤` | setInterval | clearInterval |
| `animationFrame` | `Event FrameInfo` | requestAnimationFrame | cancelAnimationFrame |
| `keyboard` | `Event Key` | addEventListener | removeEventListener |
| `request r` | `Event Response` | fetch | AbortController.abort |
| `ws.recv` | `Event WsEvent` | new WebSocket | ws.close |
| `ws.send msg` | `Event ⊤` | ws.send | — |
| `debounce ms` | `Event A → Event A` | setTimeout | clearTimeout |
| `throttle ms` | `Event A → Event A` | — | — |
| `delay ms` | `Event A → Event A` | setTimeout | clearTimeout |
