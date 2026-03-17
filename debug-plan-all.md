# Полный план отладки кодовой базы Agdelte

**77K LOC**, 268 файлов, 124 темы. Колонка **П** — количество подходов к анализу. Пустая = ещё не смотрели.

## Как работать с этим документом

### Быстрый старт

```
# 1. Запусти тесты — если что-то красное, это уже баг
node test/runtime.test.js
node test/fuzz-runtime.mjs
node test/test-clone-formats.mjs
node test/gl-math.test.js
node test/smoke.test.js

# 2. Выбери тему из таблиц ниже (пустая колонка П = ещё не смотрели)
# 3. Используй промпт-шаблон
# 4. Найденный баг → исправь → добавь тест → прогони тесты
# 5. Обнови колонку П в этом документе
```

### Промпт-шаблон (копируй и подставляй)

Для JS/Haskell (код можно запустить):
```
Прочитай [файл], строки [N-M] (тема [ID]).
Найди всё что неправильно. Для каждой находки:
- Номер строки
- Конкретный input/сценарий который ломается
- Ожидаемое vs фактическое поведение
Затем исправь все подтверждённые баги.
Каждый фикс проверь: node -c [файл] + запуск тестов.
```

Для Agda (нельзя запустить, но можно проверить логику):
```
Прочитай [файл] (тема [ID]).
Проверь: 1) каждый конструктор/postulate соответствует JS runtime
         2) логические ошибки в алгоритмах
         3) пропущенные edge cases
Для FFI: сравни сигнатуру postulate с реализацией в JS/Haskell.
```

### Выбор следующей темы

Приоритет:
1. 🔴 Темы с П = пусто и высшим приоритетом (FFI: A21-A23, Haskell: H1-H6, JS: R6, G4, G6, G10, G14)
2. 🟡 Agda Core (A1-A20) — фреймворк, от которого зависит всё
3. Темы с П = 1, которые давно анализировались (могли появиться новые баги)
4. 🟢 Examples, Scripts — низкий приоритет

### После нахождения бага

1. Исправить код
2. Написать тест в `test/fuzz-runtime.mjs` или `test/runtime.test.js`
3. Прогнать все тесты: `node test/runtime.test.js && node test/fuzz-runtime.mjs && node test/gl-math.test.js && node test/smoke.test.js`
4. Записать результат в `_recommend.md`
5. Обновить колонку П в этом файле (увеличить на 1)

### Ключевые файлы проекта

| Файл | Назначение |
|------|-----------|
| `debug-plan-all.md` | Этот документ — каталог тем и прогресс |
| `bugstrat.md` | Стратегия и покрытие фаззингом |
| `_recommend.md` | Журнал найденных и исправленных багов |
| `CLAUDE.md` | Инструкции по проекту (NixOS, generated files, build commands) |
| `package.json` | Build scripts (`npm run build:*`, `npm run css:*`) |

### Контекст: что уже сделано (раунды 15-29)

24 бага найдено и исправлено в JS runtime:
- Shader uniforms (3), normal matrix transpose (2), textured no-lights (1), blend state (1)
- zoomRT try/finally (2), mutable cycle (1), object-format cloneSlot (1)
- Event deduplication (1), event fingerprint (2), P1 freeze (1)
- BigInt serialization (1), httpPost Content-Type (1)
- deepEqual depth direction (1), ensureString robustness (1), listToArray crash guard (1)

549 тестов зелёные (42 runtime + 86 fuzz + 20 GL math + 381 smoke + 20 clone).

---

## 1. JavaScript Runtime (9,775 LOC)

### reactive.js (2,174 LOC)

| # | Тема | Строки | LOC | П | Что искать |
|---|------|--------|-----|---|------------|
| R1 | SMIL + namespace | 20-97 | 80 | 1 | Syncbase ref cycle в startSmilAnimations; foreignObject сбрасывает namespace обратно на HTML — а что с вложенным svg внутри foreignObject? Правильный ли порядок: сначала собрать все анимации, потом запустить по зависимостям? Может ли RAF не выполниться если container ещё не в DOM? |
| R2 | executeTask + executeCmd | 98-280 | 180 | 2 | `querySelector(sel)` — а если sel содержит спецсимволы (кавычки, скобки)? `focus` после delay — элемент мог быть удалён. `httpGet`/`httpPost` — что если url пустой или содержит newlines? `attempt` — task chain без ограничения глубины? `getItem` — `localStorage.getItem` может бросить `SecurityError` в private browsing. `wsSend` на CLOSING WebSocket. `channelSend` на terminated worker. `readClipboard` fallback пустая строка — caller не отличит успех от ошибки |
| R3 | wrapMutable + reconcile + cloneSlot | 304-450 | 150 | 2 | `wrapMutable` object-format: wrapper `{ [ctor]: fn }` — при reconcile `.apply()` вызывается? `cloneSlot` для object-format (исправлено r28) — проверить что fix корректен. `reconcile` при смене arity — `oldSlots.length !== newSlots.length` — а если newSlots null? Shared reference: два слота → один объект, мутация одного видна через другой. `_visited` WeakMap не чистится — GC handles? |
| R4 | createScope + destroyScope | 460-510 | 50 | 1 | `destroyScope` — копирует `children` перед итерацией (`[...scope.children]`), но что если destroyScope вложенного child модифицирует `scope.children` через splice? Гонка. `abortCtrl.abort()` — что если listener callback уже в callstack? `conditionals` cleanup — `enterTimeoutId`/`leaveTimeoutId` могут быть 0 (falsy но валидный ID) — `clearTimeout(0)` безопасен? |
| R5 | Priority dispatch + batch | 620-870 | 250 | 2 | `applyBatch` — `preBatchModel` захвачен до цикла, но `model` мутируется в цикле — следующий `cmdFunc(msg)(preBatchModel)` видит старую модель, это by design? `MAX_BATCH_SIZE = 10000` — `_droppedP1`/`_droppedP2` считают drops но нигде не сбрасываются. `flushP1` try/catch (исправлено r28) — а `flushP2` тоже вызывает `processBatch` без catch (строка 759) — если крэш в P2? `dispatchBackground` fallback `setTimeout` для Safari — timeout 100ms, а в `flushP2` `timeRemaining()` всегда 50 — обрабатывает ли это больше 1 сообщения? |
| R6 | renderNode: elem, bind, text, empty | 881-930 | 50 | | `bind` — `extract(model)` при первом рендере, но model может быть zoomRT-projected — правильный ли тип? `text` — создаёт TextNode из str, но если str содержит `null`/`undefined`/`BigInt` — textContent обработает? `elem` — `listToArray(attrs)` и `listToArray(children)` — а если attrs не list? Namespace для `math` элемента — все ли MathML теги создаются с MATHML_NS? |
| R7 | renderNode: when, whenT | 930-990 | 60 | 1 | `when` — `!!cond(model)` — а если `cond(model)` возвращает BigInt 0n? `0n` falsy но не `false`. `whenT` — `enterClass` applied и `duration > 0` для setTimeout — а что если duration = 0.5 (дробное)? `setTimeout(fn, 0.5)` → 0 или 1? `rendered` flag vs DOM state — могут разойтись при быстром toggle? |
| R8 | renderNode: foreach, foreachKeyed, scope, scopeProj, zoomRT, glCanvas | 990-1120 | 130 | 1 | `foreach` — `BigInt(idx)` — а если idx > Number.MAX_SAFE_INTEGER? `foreachKeyed` — `keyFn(item)` может вернуть object/function — `Map.set` по reference. `zoomRT` try/finally (исправлено r22) — проверить что finally корректно восстанавливает. `glCanvas` — `dispatch` captured at render time, а `__glDispatch` — тот же? `scope` — `fingerprint(model)` вызывается дважды: при рендере и при первом update — а если fingerprint side-effectful? |
| R9 | setAttr + applyAttr | 1122-1260 | 140 | 1 | `setAttr` — `BOOL_ATTRS` set: полный ли список? Отсутствует `inert`, `popover`? `name === 'value' && 'value' in el` — а для `<progress>`, `<meter>` — свойство `value` есть но семантика другая. `onValue` wheel — `e.deltaMode` 0/1/2 — правильный ли множитель для mode 2 (`window.innerHeight`)? `onValueScreen` — для touch events `e.clientX` undefined — fallback '0,0'. `onKeyFiltered` — `keyArray.includes(e.key)` — если keys содержит '' (пустую строку)? |
| R10 | updateScope + lists | 1276-1690 | 410 | 1 | `updateScopeImmediate` try/finally для zoomRT (исправлено r22). `ensureSlots` — `detectSlots` вызывается с `newModel`, а binding создан с `oldModel` — если конструктор сменился, slots = null, повторное обнаружение. `updateKeyedList` — `oldKeyMap.set(oldItems[i].key, oldItems[i])` — если два oldItems имеют одинаковый key, первый теряется. `updateUnkeyedList` — `parent.insertBefore(itemNode, insertBefore)` — если insertBefore уже не дочерний parent (removed) — DOM throws. `makeTruncatedMarker` — создаёт `<li>` — а если parent не `<ul>`/`<ol>`? |
| R11 | serializeEvent + updateSubscriptions | 1691-1790 | 100 | 2 | `serializeEvent` — `onKeys` fingerprint исправлен (r24), но другие handlers: `onKeyDown`/`onClick` — handler function identity не в fingerprint — если handler closure пересоздаётся каждый вызов subsFunc, fingerprint не меняется но handler устаревает. `parallel`/`race` — fingerprint `'parallel'`/`'race'` без содержимого — при смене внутренних events не переподписывается. `Proxy` fallback — `target[prop] || fallback` — что если handler возвращает пустую строку `''` (falsy)? |
| R12 | BigLens + time-travel | 1840-2020 | 180 | 1 | `serializeModelValue` — `seen` Set для cycle detection, но functions не добавляются в seen — может ли function→function→... зациклиться? `MAX_DEPTH = 64` — достаточно? `JSON.stringify` на большой модели — может ли заблокировать main thread? `timeTravel_undo` — `historyPast.shift()` — restore model без `wrapMutable` — restored model mutable? `timeTravelDispatch` использует `dispatch` (P1), а не `dispatchImmediate` — undo через rAF, не мгновенный |
| R13 | hotReload + destroy + mountReactive | 2023-2175 | 150 | 1 | `hotReload` — `rootScope.abortCtrl = freshScope.abortCtrl` — а старый abortCtrl уже aborted через destroyScope? Новые listeners на старом scope? `destroy` — `cancelAnimationFrame(p1RafId)` — а если `p1RafId` === 0 (initial value)? `cancelAnimationFrame(0)` — no-op? `mountReactive` — `import(modulePath)` — если путь relative, зависит от base URL страницы. Error display — stack trace может содержать sensitive paths |

### events.js (775 LOC)

| # | Тема | Строки | LOC | П | Что искать |
|---|------|--------|-----|---|------------|
| E1 | interpretEvent combinators | 46-375 | 330 | 2 | `merge` — если e1 synchronous и dispatches, а e2 ещё не subscribed — порядок подписок. `debounce` — `lastMsg` не обнуляется при unsubscribe — closure holds reference. `throttle` — `pendingMsg` аналогично. `foldE` — `state = step(inputVal)(state)` — если step возвращает promise? `mapFilterE` — `maybeResult({just, nothing})` — а если maybeResult object-format Scott? `switchE` — `currentSub.unsubscribe()` перед созданием нового — а если unsubscribe triggers dispatch? `parallel` — `results` Array fixed size, done Array — а если event dispatches multiple times? `race` — `subs.forEach(s => s.unsubscribe())` вызывается из `raceDispatch` — а subs ещё наполняется в цикле. `onKeys` — пустой pairs list → пустой keyMap → addEventListener всё равно добавляется |
| E2 | makeLeafHandlers | 378-670 | 290 | 1 | `interval` — `setInterval` — drift accumulation на длинных интервалах. `timeout` — `ensureNumber(ms)` на BigInt — `Number(9007199254740993n)` потеря precision. `springLoop` — `position` captured как `ensureNumber(position)` но `range` тоже `ensureNumber(position)` — double conversion. `httpPost` auto-detect JSON — `body[0] === '"'` — строка `"not json` пройдёт JSON.parse? Нет: JSON.parse бросит, catch проглотит. Но: `try { JSON.parse(body) }` парсит ВЕСЬ body для проверки Content-Type — может быть медленно на большом body. `wsConnect` — `ws.onclose` удаляет из `wsConnections`, но если `onclose` вызван ПОСЛЕ `unsubscribe` — double delete. `workerChannel` — `prev.terminate()` — а если prev не terminated а в середине работы? |
| E3 | interpretSub + helpers | 672-740 | 70 | 1 | `mkKeyboardEvent` — поля: key, code, ctrlKey, altKey, shiftKey, metaKey, repeat, location — порядок должен совпадать с Agda record. `BigInt(e.location)` — `e.location` всегда integer? На мобильных может быть 0. `mkMouseEvent` — `BigInt(e.clientX)` — спецификация говорит `double`, но браузеры возвращают integers для MouseEvent. А для PointerEvent? Если код когда-нибудь перейдёт на PointerEvent — fractional clientX сломает BigInt. `dispatchWorkerProgress` — `data.type === 'progress'` — а если worker шлёт `{type: 'progress', value: undefined}`? `String(undefined)` = `'undefined'` |
| E4 | Exported utilities | 742-775 | 30 | 1 | `debounce` exported — возвращает function без cancel method. `throttle` exported — аналогично. Обе не чистят таймеры при garbage collection. Используются ли вообще за пределами events.js? |

### agda-values.js (638 LOC)

| # | Тема | Строки | LOC | П | Что искать |
|---|------|--------|-----|---|------------|
| V1 | Probing | 14-200 | 190 | 1 | `getCtor` — Proxy handler `get(_, name) { return (...args) => { ctor = name; }; }` — а если Scott function вызывает handler с Symbol key (e.g., Symbol.toPrimitive)? `getSlots` — возвращает args array из Proxy — а если constructor не вызывает handler (returns early)? `probe` — аналогично. `_slotProbe` — global shared Proxy — thread-safe? (JS single-threaded, OK). `probeSlots` для object-format — `value[keys[0]](_slotProbe)` — а если keys[0] === '__proto__' или 'constructor'? |
| V2 | deepEqual + slot tracking | 203-389 | 190 | 2 | `deepEqual` — `return true` при превышении глубины (исправлено r29). `a(probeA)` / `b(probeB)` — если a или b не чистые (side effects при вызове) — deepEqual может мутировать state. `detectSlots` — sentinel Symbol injected в каждый слот — а если extract function caches result? First call returns baseValue, sentinel call returns cached same value — dependency missed. `changedSlotsFromCache` — `scope.cachedArgs = newArgs` — mutates scope in-place — а если changedSlotsFromCache вызван дважды в одном update cycle? |
| V3 | List/Nat/Number ops | 391-533 | 140 | 1 | `listToArray` — try/catch добавлен (r29) — но `MAX_LIST_ITEMS = 100000` — это мало или много? Зависит от use case. `arrayToList` — `construct('_∷_', arr[i], result)` — строит список справа налево — О(n) но каждый element создаёт closure — memory. `natToNumber` — `MAX_NAT_VALUE = 100000` — если Nat > 100000, возвращает 100000 с warning — silent data loss. `ensureNumber` — `natToNumber(n)` для function input — а если function не Scott-encoded ℕ? `natToNumber` returns 0 после break — неожиданно |
| V4 | String/Maybe/Bool ops | 535-625 | 90 | 1 | `ensureString` hardened (r29) — `typeof data === 'symbol'` → `data.toString()` — но `Symbol.prototype.toString` может быть monkey-patched? Маловероятно. `fromMaybe` — `matchOr(maybe, {just, nothing}, null)` — если maybe object-format, match handles? `toMaybe` — `value != null` (loose) — catches undefined too — correct? `fromBool` — `matchOr(bool, {true, false}, false)` — а если bool Scott-encoded с другими constructor names? `toBool` — `value ? construct('true') : construct('false')` — а если value BigInt 0n? `0n` falsy → 'false'. Correct. |

### reactive-gl.js (5,419 LOC)

| # | Тема | Строки | LOC | П | Что искать |
|---|------|--------|-----|---|------------|
| G1 | Scott interpreters | 60-365 | 300 | 1 | `interpretSceneNode` — все конструкторы (mesh, group, icon, light, bindTransform, bindMaterial, text3D, bindText3D, bindLight, bindChildren, animate, interactiveGroup, named, instanced, bindInstanced, batched) — есть ли пропущенные? Если Agda добавит новый конструктор, JS бросит при вызове. `interpretGeometry` — plain object check `geom.type` — откуда берутся plain objects? Из Geometry.Primitives (roundedBox и др.) — правильный ли маппинг? `interpretMaterial` — textured: `url: texHandle` — texHandle это строка URL? Или Scott-encoded? |
| G2 | GLSL шейдеры | 369-825 | 460 | 1 | Phong frag — `for (int i = 0; i < 8; i++) { if (i >= u_numLights) break; }` — loop unrolling в GLSL — все ли GPU поддерживают dynamic break? Formально да по ES 3.0 spec. PBR frag — `pow(1.0 - cosTheta, 5.0)` — а если cosTheta > 1.0 из-за precision? `clamp` нет. Instanced vert — `mat3(a_instanceMatrix)` как approximation для normal matrix — неправильно при non-uniform scale (documented approximation). Pick frag — `u_objectId` float precision — 24-bit ID в 8-bit channels — есть ли precision loss при float→byte conversion? Text frag — `alpha < 0.1` threshold — hard-coded, не configurable |
| G3 | Матричная математика | 830-1030 | 200 | 1 | `mat4Perspective` — `fov` в radians или degrees? Caller responsibility. `mat4LookAt` — `up` parallel to view direction → `len = 0` → `ix = 0` → NaN в результате. `mat4Invert` — `det < 1e-10` threshold — может быть слишком строгий для далёких объектов? `mat4Multiply` — O(64) operations — hot path? Может ли быть bottleneck для scene с 1000 объектов? `unprojectPoint` — `ww < 1e-10` — а если ww отрицательный (за камерой)? |
| G4 | Ray intersection | 1031-1290 | 260 | | `raySphere` — `a = dir.x² + dir.y² + dir.z²` — если dir normalized, a ≈ 1.0 — но нигде не гарантируется нормализация. `rayAABB` — `Math.abs(d) < 1e-10` — а если луч почти параллелен грани? `tmin > tmax` check может пропустить edge case. `rayPlane` — `ray.dir.y` only — а если плоскость не XZ (повёрнутая)? Нужен transform в local space. `rayToLocal` — `localRay.scale` — используется для конвертации t обратно в world — а если scale неравномерный по осям? `rayIntersectEntry` — cylinder approximated как box — пропускает hits по скруглённым краям. `rayPickEntries` — linear scan O(n) — может быть медленно для >1000 объектов. `rayPickGroup` — recursive без ограничения глубины |
| G5 | Базовая геометрия + upload | 1291-1460 | 170 | 1 | `createBoxGeometry` — normals hard-coded — правильные ли для каждой грани? UV mapping — каждая грань 0-1 — а если нужен atlas? `createSphereGeometry` — `slices=24, stacks=16` — достаточно для гладкой сферы? При radius < 0.01 degenerate? `createPlaneGeometry` — UV tiled по size — `size.x, size.y` как tile repeat — а если size < 0? `uploadGeometry` — `_indexType` stored — но `drawElements` at call site checks string equality — typo risk |
| G6 | Extended geometry | 1460-2250 | 790 | | `createTorusGeometry` — normals `(cosV*cosU, sinV, cosV*sinU)` — правильно ли? Должен указывать от центра tube к поверхности. `createCapsuleGeometry` — `halfHeight = height * 0.5 - radius` — а если height < 2*radius? Negative halfHeight → inverted caps. `createConeGeometry` — normals для sloped surface: `len = sqrt(1 + slope²)` — а если slope = 0 (flat)? `createPyramidGeometry` — face normal cross product — winding order consistent? `createTubeGeometry` — inner wall reversed winding — correct? `createRingGeometry` — flat ring, normals все (0,1,0) — а если ring не в XZ plane? `createTetrahedronGeometry` — vertex coords `a = radius/sqrt(3)` — правильная формула? `createRoundedBoxGeometry` — SDF solver с binary search fallback — сходимость за 50 итераций? Edge cases: radius > min(dims)/2? |
| G7 | Текстуры + шрифты + текст | 2250-2700 | 450 | 1 | `createTextureCache` — LRU eviction `cache.delete(oldest); cache.set(url, entry)` — Map insertion order. `img.crossOrigin = 'anonymous'` — а если сервер не шлёт CORS headers? Ошибка тихая (errorTex). `createFontAtlas` — `atlasSize = 1024` fixed — а если шрифт очень большой или символов много? `if (curY + h > atlasSize) break` — символы после break не в atlas → fallback `glyphs.get('?')`. `buildTextGeometry` — `Math.max(0, ...lines.map(l => l.width))` — spread на большом массиве → stack overflow? `createTextVAO` — dummy normals `(0,0,1)` — а если текст повёрнут? Освещение неправильное |
| G8 | Shader compilation + programs + pick FB | 2700-2970 | 270 | 1 | `compileShader` — `gl.getShaderInfoLog` — может вернуть null? `linkAndCleanShaders` — detach+delete shaders after link — correct GL lifecycle. `createPickFramebuffer` — `width <= 0 || height <= 0` → null — все caller проверяют null? `createPhongProgram` — light uniform arrays hardcoded `i < 8` — matches CONFIG.MAX_LIGHTS? `geometryKey` — cache key as string concatenation — collision risk если dims содержат запятую? |
| G9 | Geometry cache + easing + lerp/slerp | 2975-3250 | 275 | 1 | `getOrCreateGeometry` — `GEO_CACHE_MAX = 256` — eviction стратегия? Или просто растёт? `makeCubicBezier` — Newton-Raphson solver — сходимость для extreme control points? `resolveEasing` — `easingFunctions[easing]` — а если easing неизвестная строка? Returns undefined → NaN. `slerpQuat` — `dot < 0` → negate b — shortest path. Но: `Math.acos(dot)` — если dot > 1 из-за precision → NaN. Нужен clamp. `lerpTransform` — независимая интерполяция pos/rot/scale — корректно для большинства случаев |
| G10 | Instance buffers + collect | 3250-3810 | 560 | | `buildInstanceMatrices` — `Float32Array(count * 16)` — если count = 0? Пустой массив OK. `transformToMat4` — delegates to `mat4FromTRS` — проверить что transform всегда имеет pos/rot/scale. `setupInstanceAttributes` — location 2-5 для mat4 — конфликт с UV attribute (location 2)? Нет: instanced shader не использует UV. `collectBindings` — recursive traversal — stack overflow на глубокой сцене? `collectNode` — `overrideTransform` — используется для animate — а если и parent и child имеют transform? `registerPickable` — `pickRegistry.nextId++` без bounds check — overflow at 2^24. `pickIdToRGB` — `((id >> 16) & 0xFF)` — 24-bit max |
| G11 | updateGLBindings + tick | 3836-4150 | 310 | 1 | `updateGLBindings` — `transformEqual`/`materialEqual` — shallow comparison — если nested object refs change but values same? `tickSingleAnimation` — `elapsed / durationMs` — если durationMs = 0? Division → Infinity → clamp to 1.0? Нет clamp — easing(Infinity). `tickAnimateNodes` — `dt = timeSeconds - anim.lastTimestamp` — first frame dt = 0 → skip. Second frame dt correct. `anim.accumTime += dt` — unbounded growth — для hover-only animations, runs forever while hovered |
| G12 | uploadLights + renderEntry + renderScene | 4154-4490 | 340 | 1 | `uploadLights` — `Math.min(lights.length, 8)` — lights > 8 silently dropped. `renderEntry` text — blending removed from text rendering (r25) — а если text rendered in opaque pass? Line 4459 always puts text in transparent. `isTransparent` — checks only mesh and group — instanced, text3D, icon not checked. `entryDepth` — uses transform.pos only — а если entry type has no transform? Returns (0,0,0) distance. `renderScene` — `gl.clearColor(0.1, 0.1, 0.1, 1.0)` hardcoded — not configurable |
| G13 | Pick-pass rendering | 4490-4640 | 150 | 1 | `renderPickEntry` — recursive for groups — depth limit? `renderPickBuffer` — `gl.enable(gl.DEPTH_TEST)` — а `gl.depthMask(true)`? Если предыдущий прогон оставил `depthMask(false)` — picking сломан. (renderScene восстанавливает, но edge case). `readPickId` — `pickFB.height - 1 - y` — off-by-one если height = 0? pickFB null-guard exists. `rgbToPickId` — `r | (g << 8) | (b << 16)` — а если r/g/b > 255? Impossible from readPixels UNSIGNED_BYTE |
| G14 | initGLCanvas + events + resize | 4640-5420 | 780 | | `initGLCanvas` — `canvas.getContext('webgl2')` — fallback если WebGL2 недоступен? Нет — бросает. Drag state machine: mousedown → mousemove → mouseup — а если mouseup вне canvas? `pointerup` на document? `setPointerCapture`? HiDPI resize — `canvas.width = drawW; canvas.height = drawH` — а если drawW/drawH = 0 (element hidden)? GL error. `ResizeObserver` — callback может вызваться при каждом frame если element анимируется — throttle? MutationObserver — `document.body` subtree — может быть тяжело для DOM с 10K нод. `disposeGLCanvas` — все ли GL ресурсы freed? Programs, geometries, textures, FBOs, VBOs. Focus: `tabIndex = 0` — а если canvas уже имеет tabIndex? Keyboard: `onKeyDown` в focused canvas — а если canvas теряет focus между keydown и keyup? |

### Остальной JS (5 тем)

| # | Тема | Файл | LOC | П | Что искать |
|---|------|------|-----|---|------------|
| O1 | Worker pool | worker-pool.js | 224 | 1 | `submit` — `activeWorker` closure variable — а если onmessage и onerror вызываются оба? (network error + partial response). `_processQueue` — `while` loop — если tryRun вызывает enqueue → infinite loop? `_cleanup` — `Date.now() - this.lastUsed > POOL_IDLE_TIMEOUT` — а если clock jumps backward (NTP sync)? `destroy` — `entry.task.onError('Pool destroyed')` в try/catch — если onError бросает, catch проглатывает |
| O2 | Buffer registry | buffer-registry.js | 270 | 1 | `allocate` — `SharedArrayBuffer(size)` — если size = 0? SAB(0) валиден? `nextHandle` — overflow при `Number.MAX_SAFE_INTEGER`? Практически нет. `getView` — switch без default return — last line `default: return new Uint8Array(buffer)` есть. `copyImageData` — `imageData.data.length === view.length` — а если buffer resized между allocate и copy? `getImageData` — `entry.buffer.slice(0)` — на SAB дорого — копирует весь буфер |
| O3 | SVG events | svg-events.js | 196 | 1 | `screenToSvg` — `ctm.inverse()` — может бросить если CTM singular (zero-sized SVG). `findSvgRoot` — `tagName === 'svg' || tagName === 'SVG'` — а в namespace? `element.tagName` в HTML lowercase, в XML uppercase — покрыты оба? `createSvgDrag` — `target.setPointerCapture(e.pointerId)` — может бросить если pointer уже captured. `onPointerUp` — `target.releasePointerCapture(e.pointerId)` — если capture уже released → exception. `createSvgPinch` — `initialDistance > 1e-6` — а если distance exactly 0? Division в getCenter safe (just midpoint) |
| O4 | Agda RTS primitives | agda-rts.js | 372 | 1 | `uprimIntegerQuot` — `x / y` BigInt division truncates toward zero — correct for quot. Но: `y === 0n` → throws `RangeError`. Нет guard. `_primFloatDecode` — loop `while (!Number.isInteger(mantissa))` — для subnormals может быть очень много итераций (1074 max для float64). Performance? `primFloatToWord64` — DataView approach correct for bit reinterpretation. `uprimFloatEncode` — `mantissa * (2 ** exponent)` — 2^1024 = Infinity, returns Infinity not null. `primNatMinus` — `x - y < 0n → 0n` — correct для natural subtraction. `primFaceForall` — `f(true) == true` — loose equality, но operands both bool, so OK |
| O5 | Update worker + reactive-auto | update-worker.js + reactive-auto.js | 80 | 1 | `update-worker.js` — `import(modulePath)` — path relative to worker location — correct? `updateFn = NodeModule.ReactiveApp.update(appRecord)` — а если appRecord не имеет update? `reactive-auto.js` — `document.querySelectorAll('[data-agdelte]')` — runs at script load time — а если DOM ещё не ready? |

---

## 2. Haskell Agent Server (1,476 LOC)

| # | Тема | Файл | LOC | П | Что искать |
|---|------|------|-----|---|------------|
| H1 | AgentServer | hs/Agdelte/AgentServer.hs | 503 | | STM транзакции: атомарность read-modify-write для agent state? Race между HTTP POST и WebSocket push. Exception handling: что если agent step бросает — recovery или crash? WebSocket broadcast: если один client медленный, блокирует ли остальных? Memory: растёт ли state unbounded? Agent garbage collection? Route parsing: path traversal через `..`? Content-Type validation на POST body? |
| H2 | Process | hs/Agdelte/Process.hs | 328 | | Agent execution model: pure coalgebra step — а если step diverges (infinite loop)? Timeout? State snapshots: deep copy или reference? Mutable state через IORef/TVar — consistency при concurrent access? Agent lifecycle: create/destroy/restart — resource cleanup? |
| H3 | Http | hs/Agdelte/Http.hs | 150 | | Request parsing: malformed JSON body? Oversized body? Missing Content-Type header? Response: correct status codes? CORS headers? Error response format consistency? Path routing: case sensitivity? Trailing slash? Query params? |
| H4 | STM | hs/Agdelte/STM.hs | 101 | | `retry` semantics: может ли STM transaction retry бесконечно? Starvation? TVar: memory leak если transaction allocates then retries? Composability: nested transactions correct? Exception in transaction: rollback complete? |
| H5 | WebSocket | hs/Agdelte/WebSocket.hs | 77 | | Connection lifecycle: open → message → close — все states handled? Ping/pong: keepalive timeout? Client disconnect без close frame — detection? Concurrent send: thread-safe? Broadcast: if N clients, O(N) sends — blocking? Message size limit? Binary vs text frames? |
| H6 | Server tests | hs/test/Spec.hs | 317 | | Coverage: все ли HTTP endpoints тестируются? WebSocket scenarios? Concurrent access? Error cases? Agent lifecycle? Тесты проходят? Не flaky? |

---

## 3. Agda Core Library (35,144 LOC)

Специфика: type system ловит type errors, но не логические ошибки. Искать: семантические баги, FFI mismatches, неоптимальный generated JS.

### Core Framework

| # | Тема | Файл | LOC | П | Что искать |
|---|------|------|-----|---|------------|
| A1 | Event | src/Agdelte/Core/Event.agda | 565 | | Event datatype: все ли конструкторы имеют корректную Scott-encoding семантику? Event↔Sub split: конструкторы в Event vs Sub — правильное ли разделение? Каждый Sub constructor должен быть leaf (без рекурсивного Event). `merge` ассоциативность: `merge (merge a b) c ≡ merge a (merge b c)` — в runtime порядок подписки может отличаться. `foldE` — начальное состояние и step function — типы совпадают с runtime interpretEvent? `mapFilterE` — Maybe return — nothing = filter out — runtime проверяет `isJust`? `switchE` — метa-event returns new Event — тип рекурсивный? |
| A2 | Signal | src/Agdelte/Core/Signal.agda | 180 | | Signal абстракция: continuous vs discrete? Memory semantics — удерживает ли Signal ссылку на все предыдущие значения? `accum` — accumulator leak. `map`, `filter`, `merge` — правильная ли семантика для одновременных events? |
| A3 | Task | src/Agdelte/Core/Task.agda | 181 | | Task монада: `pure`, `fail`, `httpGet`, `httpPost`, `>>=` — все ли правильно компилируются в Scott-encoding? Error propagation: `fail` должен прерывать цепочку — runtime executeTask проверяет? `httpPost` body type — String? А если нужен binary? |
| A4 | Cmd | src/Agdelte/Core/Cmd.agda | 153 | | `_<>_` — моноидальная композиция — ассоциативна ли в runtime? `ε` — identity. Полнота: все ли нужные side effects покрыты (focus, blur, scroll, clipboard, localStorage, routing, WS, workers, buffers)? Нет ли дубликатов? `delay` — тип ms: ℕ? А если нужен Float delay? |
| A5 | Result | src/Agdelte/Core/Result.agda | 64 | | `ok`/`err` конструкторы — правильный ли маппинг на JS `cb['ok'](value)` / `cb['err'](error)`? Result.Event — event that dispatches Result — composition с Task? |
| A6 | App | src/Agdelte/App.agda | ~100 | | `ReactiveApp` record: `init`, `update`, `template`, `cmd`, `subs` — все ли optional? Что если `cmd` = nothing? `subs` = nothing? Runtime checks `if (!subsFunc) return`. `template` — type: `Node Model Msg` — right? |

### Reactive System

| # | Тема | Файл | LOC | П | Что искать |
|---|------|------|-----|---|------------|
| A7 | Node | src/Agdelte/Reactive/Node.agda | 421 | | Все Node конструкторы: `text`, `bind`, `elem`, `empty`, `when`, `whenT`, `foreach`, `foreachKeyed`, `scope`, `scopeProj`, `zoomRT`, `glCanvas` — каждый должен match с handler в reactive.js `renderNode`. Binding type: `extract : Model → String` — а если нужен non-string binding (числовой атрибут)? Attr type: `attr`, `attrBind`, `on`, `onValue`, `onValueScreen`, `onKeyFiltered`, `style`, `styleBind` — match с `applyAttr`. `Transition` record fields — match с `NodeModule.Transition.*` extractors в JS |
| A8 | Diagram | src/Agdelte/Reactive/Diagram.agda | 253 | | Diagram composition operators — правильная семантика? Diagram → Node conversion — полная ли? |
| A9 | Optic | src/Agdelte/Reactive/Optic.agda | 183 | | Lens laws: get-set, set-get, set-set — доказаны или postulated? `zoomRT` optic — get/wrap pair — consistent? |
| A10 | Inspector + TimeTravel + BigLens | Inspector+TimeTravel+BigLens.agda | 422 | | BigLens protocol: peek → JSON serialize model → WS send. Всё ли сериализуемо? Over: JSON → message → dispatch — type safety потеряна на JSON boundary. TimeTravel: history depth — configurable? |
| A11 | Lens + ProcessOptic + RemoteOptic | Lens+ProcessOptic+RemoteOptic.agda | 286 | | Composition chains — правильный ли порядок get/set? Remote sync — eventual consistency или strong? Conflict resolution? |

### Concurrent & Agent System

| # | Тема | Файл | LOC | П | Что искать |
|---|------|------|-----|---|------------|
| A12 | Agent | src/Agdelte/Concurrent/Agent.agda | 48 | | Coalgebra interface: `step : Input → State → State`, `observe : State → Output` — минимальный ли набор? Нет ли missing operations (init, destroy)? |
| A13 | Session | src/Agdelte/Concurrent/Session.agda | 224 | | Session types: `send`, `recv`, `end`, `choice`, `offer` — полный ли набор? Дуальность: `dual(send A S) = recv A (dual S)` — доказана? Deadlock freedom — гарантируется ли типами? |
| A14 | SessionExec | src/Agdelte/Concurrent/SessionExec.agda | 240 | | Execution: session type → runtime behavior. FFI calls для send/recv — правильный ли маппинг? Error handling: что если send fails? Channel закрыт? |
| A15 | SharedAgent + DepAgent | SharedAgent+DepAgent.agda | 355 | | Shared state: read/write atomicity? Dependent agent: dependency cycle detection? Resolution order? |
| A16 | CoSession | src/Agdelte/Concurrent/CoSession.agda | 219 | | Co-session = dual perspective — symmetry с Session.agda? Protocol compatibility check? |
| A17 | SessionForm | src/Agdelte/Concurrent/SessionForm.agda | 173 | | Form fields → session messages — mapping complete? Validation на Agda side vs JS side? |
| A18 | Obligation | src/Agdelte/Concurrent/Obligation.agda | 159 | | Obligation: must-do before proceed — enforcement mechanism? Compile-time vs runtime? |
| A19 | Wiring | src/Agdelte/Concurrent/Wiring.agda | 321 | | Agent composition topology — correct routing? Fan-out/fan-in? Error propagation через wiring? Debug module — overhead в production? |
| A20 | ProcessOpticLinear | ProcessOpticLinear.agda | 87 | | Linear types — resource must be used exactly once — enforced by Agda? Или convention? |

### FFI Boundary (🔴 высший приоритет)

| # | Тема | Файл | LOC | П | Что искать |
|---|------|------|-----|---|------------|
| A21 | FFI.Browser | src/Agdelte/FFI/Browser.agda | 154 | | Каждый `postulate` — сигнатура совпадает с JS реализацией? Типы: `ℕ` → BigInt, `Float` → Number, `String` → String, `Bool` → Scott-encoded — все ли маппинги правильные? `Maybe` — JS null или Scott nothing? Callback arity — curried в Agda, curried в JS? Или uncurried? |
| A22 | FFI.Server | src/Agdelte/FFI/Server.agda | 307 | | Haskell FFI: `foreign import` correctness? Type marshalling Agda→Haskell→IO? Blocking calls — правильная ли concurrency model? Exception propagation through FFI boundary? |
| A23 | FFI.Shared | src/Agdelte/FFI/Shared.agda | 66 | | Cross-platform: функции используемые и в browser и в server — одинаковая ли семантика? Platform-specific behavior hidden behind shared interface? |

### HTML Controls

| # | Тема | Файлы | LOC | П | Что искать |
|---|------|-------|-----|---|------------|
| A24 | DatePicker | Html/Controls/DatePicker.agda | 722 | | Календарная логика: дней в месяце (leap year!), первый день недели (locale?), переход month→month, year→year. Edge: 2024-02-29. Timezone: Date в JS — local timezone, а DatePicker показывает какой? Selection: range selection, disabled dates. Generated HTML: accessibility (ARIA), keyboard navigation |
| A25 | Slider | Html/Controls/Slider.agda | 446 | | Min > max — handled? Step = 0 — division by zero? Drag precision: float rounding при step. Vertical slider? Range slider (two thumbs)? Touch events? Accessibility: aria-valuenow, aria-valuemin, aria-valuemax |
| A26 | Dropdown + Popover + Modal | Dropdown+Popover+Modal.agda | 588 | | Dropdown: click-outside close — event handler cleanup? Search/filter в dropdown? Popover: positioning — overflow viewport? Focus trap в modal — tab cycle. Escape key — все ли закрывают? Nested modals? Z-index stacking? |
| A27 | Accordion + TabBar + Sidebar | Accordion+TabBar+Sidebar.agda | 488 | | Accordion: multiple open vs single? Animation height transition. TabBar: active tab state sync. Sidebar: responsive collapse. Keyboard navigation: arrow keys, home/end? |
| A28 | Table + DataGrid | Table+DataGrid.agda | 300 | | Sorting: stable sort? Multi-column? Pagination: off-by-one в page count? Empty data display. Column resize: min width? DataGrid: virtualization для больших datasets? |
| A29 | TreeView + Breadcrumb | TreeView+Breadcrumb.agda | 330 | | TreeView: expand/collapse state. Lazy loading children? Drag-drop reorder? Breadcrumb: path sync с model. Truncation при overflow? |
| A30 | Toast + Tooltip + Spinner + Skeleton | Toast+Tooltip+Spinner+Skeleton.agda | 640 | | Toast: auto-dismiss timer — cleanup при unmount? Stacking multiple toasts? Tooltip: delay before show? Position flip при viewport edge? Spinner: accessible `role="status"`? Skeleton: layout shift при content load? |
| A31 | Checkbox + Radio + Stepper + Progress + Pagination | CheckboxRadioStepperProgressPagination.agda | 795 | | Checkbox: indeterminate state? RadioGroup: none selected allowed? Stepper: bounds enforcement min/max. Progress: value > max? Negative value? Pagination: total = 0 → 0 pages or 1? |

### SVG System

| # | Тема | Файлы | LOC | П | Что искать |
|---|------|-------|-----|---|------------|
| A32 | SVG core | Svg/Elements+Attributes+Events+Transform.agda | 711 | | Element names: typos в SVG element strings? Attribute names: camelCase vs kebab-case (SVG uses kebab). Event handler attributes vs addEventListener — which approach? Transform: matrix composition order? |
| A33 | SVG ViewBox + Accessibility + Filter + Gradient | ViewBox+Accessibility+Filter+Gradient.agda | 486 | | viewBox: `min-x min-y width height` — negative width/height? preserveAspectRatio? Accessibility: role, aria-label — на каких SVG elements? Filter: filter URL reference — `url(#id)` — id uniqueness? Gradient: stop offset 0-1 — clamped? |
| A34 | SVG Smil + Path + Morph | Smil+Path+Morph.agda | 667 | | SMIL: begin/dur/end attributes — string format correct? Path: `M`, `L`, `C`, `A` commands — float precision in generated strings. Morph: path interpolation — same number of commands required? Different command types? |
| A35 | SVG Controls: Button, Tooltip, Progress, Slider | Svg/Controls/core.agda | 1212 | | SVG Button: click hit area = visual area? SVG Tooltip: text positioning. SVG Progress: arc calculation (2π * progress). SVG Slider: drag → value mapping — linear? Logarithmic? |
| A36 | SVG Controls: interactive | Svg/Controls/interactive.agda | 1175 | | Draggable: bounds enforcement? Snapping? Checkbox SVG: check/uncheck animation. RadioGroup: group constraint. Toggle: on/off transition. Knob: circular drag → angle → value — atan2 correct? |
| A37 | SVG Controls: display | Svg/Controls/display.agda | 1013 | | Legend: item overflow? Connector: path routing (straight, bezier, orthogonal). Axis: tick count algorithm — nice numbers? Log scale? Gauge: needle rotation math. RangeSlider: min thumb can't exceed max thumb? |
| A38 | SVG Gauges | Svg/Controls/Gauges/*.agda | 1022 | | Gauge: arc from angle to angle — direction (CW/CCW)? Value clamp to min/max? ProgressRing: stroke-dasharray calculation. Sparkline: data normalization — min=max? Zero data points? |
| A39 | SVG Charts: basic | Charts/Line+Area+Bar+Scatter.agda | 1054 | | Axis scaling: auto range from data min/max — zero included? Negative values? Log scale? Bar chart: bar width calculation — overlapping bars? Stacked? Scatter: point overlap? Jitter? Line: missing data points — gap or interpolate? |
| A40 | SVG Charts: advanced | Charts/Pie+Radar+Timeline+Heatmap.agda | 983 | | Pie: slices sum > 100%? Sum = 0? Single slice = full circle? Labels overlap? Radar: polygon area — concave for negative? Timeline: overlapping events? Zoom/pan? Heatmap: color scale — linear? Discrete? Missing cells? |
| A41 | SVG Charts: complex | Charts/Network+OrgChart+Sankey+Treemap+Flowchart.agda | 1617 | | Network: force layout converging? Node overlap? Edge crossing minimization? OrgChart: tree layout — wide trees overflow? Sankey: flow conservation (sum inputs = sum outputs per node)? Treemap: squarified algorithm — degenerate cases? Flowchart: edge routing — overlap with nodes? |

### CSS System

| # | Тема | Файлы | LOC | П | Что искать |
|---|------|-------|-----|---|------------|
| A42 | CSS core | Css/core.agda | 816 | | Property names: typos? Vendor prefixes needed? Unit generation: `px`, `em`, `rem`, `%`, `vh`, `vw` — all handled? Color: hex, rgb, rgba, hsl, hsla — string generation correct? Easing: `cubic-bezier(x1,y1,x2,y2)` — string format? Animate: @keyframes generation — unique names? |
| A43 | CSS Controls | Css/Controls/*.agda | 1400 | | Class naming: consistent convention (BEM? Flat?)? CSS variable names: `--agdelte-*` prefix consistent? Responsive breakpoints: consistent across controls? Hover/focus/active states — all controls? Dark theme support via variables? |

### WebGL System

| # | Тема | Файлы | LOC | П | Что искать |
|---|------|-------|-----|---|------------|
| A44 | WebGL Types + Builder | WebGL/Types+Builder.agda | 413 | | Scene type: all node types covered? Camera: perspective + orthographic — missing types? Material: unlit, flat, phong, pbr, textured — complete? Light: ambient, directional, point, spot — complete? Transform: position, rotation (quaternion), scale — Euler angles support? |
| A45 | WebGL Geometry | WebGL/Builder/Geometry/*.agda | 636 | | Primitives: box, sphere, plane, cylinder + extended (roundedBox, torus, capsule, cone, pyramid, tube, ring, tetrahedron, octahedron, icosahedron, dodecahedron) — parameter types correct? Degenerate params handled? Procedural: параметрическая генерация — формулы correct? CSG: boolean ops (union, intersect, subtract) — edge cases (touching surfaces, coplanar faces)? |
| A46 | WebGL Layout | WebGL/Builder/Layout/*.agda | 393 | | Grid: row/col count calculation. Spacing. Cell position. Radial: angle distribution — even? Custom? Stack: z-offset between layers. Overlap handling? |
| A47 | WebGL Optimization | WebGL/Builder/Optimize/*.agda | 353 | | Batching: which nodes can be batched? Same material requirement. Culling: frustum test — bounding sphere vs AABB. False positives/negatives. LOD: distance thresholds — smooth transition or pop? |
| A48 | WebGL Controls: Input | WebGL/Controls/input.agda | 1719 | | 3D Buttons: click detection via pick ID — correct wiring? Input: text input in 3D — keyboard events routed to focused element. Menus: 3D menu positioning — camera-facing? Sliders: drag in 3D space → value mapping. Toggles: on/off state + visual. Tabs: tab switching logic |
| A49 | WebGL Controls: Display | WebGL/Controls/display.agda | 393 | | Text: font atlas reference — matches reactive-gl.js font system? State: visual state indicators in 3D. Theme: color/material variables — resolved at compile time or runtime? |
| A50 | WebGL Charts + Audio | Charts+Audio/*.agda | 1910 | | Bar3D: bar positioning in 3D space. Scatter3D: point placement. Network3D: force layout in 3D — convergence? Surface: mesh generation from data grid. Spectrum: FFT data → visual mapping. Waveform: sample rate handling, buffer size |
| A51 | WebGL Gizmos + Import | Gizmos+Import/*.agda | 1449 | | Transform gizmo: axis handles — correct hit testing? Rotation: quaternion from drag delta. Selection: multi-select, bounding box. Measure: distance/angle calculation. GLTF: parse correctness — all node types? Materials? Animations? NamedParts: part identification in complex models |

### Data + Forms + Misc

| # | Тема | Файлы | LOC | П | Что искать |
|---|------|-------|-----|---|------------|
| A52 | Animation | Anim/Spring+Tween+Easing.agda | 257 | | Spring: stiffness/damping параметры — совпадают ли с JS runtime springLoop? Settle threshold? Tween: duration, easing — тип easing совпадает с JS interpretEasing? |
| A53 | Data (Json, DateTime, Array, Buffer) | Json+DateTime+Array+Buffer.agda | 1596 | | JSON: parse/emit — roundtrip fidelity? Unicode escaping? Large numbers? DateTime: leap year, DST transitions, timezone handling. Array: bounds checking — out of range? Negative index? Buffer: size calculation — overflow? |
| A54 | Forms | Forms.agda | 360 | | Field validation: type-safe validators? Runtime validation vs compile-time? Submit: all fields valid check. Error display: per-field errors? Form-level errors? Reset: clear all fields + errors? |
| A55 | Primitive input | Primitive/Keyboard+Mouse+AnimationFrame.agda | 197 | | KeyboardEvent record: поля совпадают с mkKeyboardEvent в events.js? MouseEvent record: поля совпадают с mkMouseEvent? AnimationFrame: handler type — receives timestamp (Float)? |
| A56 | Experimental | Experimental/Widget+IncLens.agda | 221 | | Widget: API stable? Или breaking changes expected? IncLens: incremental lens — performance benefit demonstrated? Edge cases? |
| A57 | Theory + Tests | Theory/*.agda + Test/*.agda | 1218 | | Proofs: holes (`?`), `postulate`s (axioms without proof), `trustMe` (escape hatch)? Какие леммы доказаны, какие postulated? Test modules: что тестируют? Coverage? |

---

## 4. Examples (8,722 LOC)

| # | Тема | Файлы | LOC | П | Что искать |
|---|------|-------|-----|---|------------|
| X1 | Styles (CSS generation) | Styles+IndexStyles.agda | 1940 | | Генерируемый CSS: typos в property names/values? Missing selectors? Unused styles? Conflicting rules? Responsive breakpoints consistent? Color palette — accessible contrast ratios? |
| X2 | Core examples | Counter+Timer+Keyboard+Http+Task.agda | 561 | | Counter: increment/decrement correct? Timer: interval cleanup on unmount? Keyboard: all key events handled? Http: error display? Loading state? Task: chain error propagation? |
| X3 | List examples | Todo+Router+Transitions.agda | 600 | | Todo: add/remove/toggle — state consistent? Filter (all/active/completed)? Router: URL → view mapping complete? 404 handling? Transitions: enter/leave classes — timing? |
| X4 | Async examples | Parallel+Worker+WebSocket.agda | 532 | | Parallel: all tasks complete? Partial failure? Worker: message protocol — type mismatch? WebSocket: reconnect logic? Message ordering? Disconnect handling? |
| X5 | SVG examples | Svg*.agda | 1050 | | Chart: data → SVG rendering correct? Empty data? LineDraw: drawing state machine? Undo? PanZoom: coordinate transforms — zoom center correct? Smil: animation timing? Chaining? |
| X6 | WebGL examples | WebGL*+ControlsDemo.agda | 1755 | | GL scene setup: camera positioned correctly? Lights configured? Objects visible? Interaction: click → correct object? Drag → correct transform? Controls: all demo controls functional? |
| X7 | Agent examples | Agent+Session*.agda | 775 | | Agent wiring: messages route correctly? Session: protocol followed? Dual session: symmetry works? Form: submit triggers session correctly? |
| X8 | Advanced examples | OpticDynamic+Composition+Combinators+StressTest.agda | 1000 | | Optic composition: get/set roundtrip? StressTest: performance metrics? Memory growth? Combinators: all combinator types exercised? |

---

## 5. Server Examples (18,343 LOC)

| # | Тема | Файл | LOC | П | Что искать |
|---|------|------|-----|---|------------|
| S1 | Main server | server/Main.agda | 1559 | | Server config: port, host binding. Agent initialization order — dependencies respected? Graceful shutdown — all connections closed? |
| S2 | HttpAgent | server/HttpAgent.agda | 2102 | | HTTP handler: request parsing — malformed input? State transitions — valid? Response format — consistent JSON? Error codes — correct HTTP status? |
| S3 | MultiAgent + SharedAgent | MultiAgent+SharedAgentDemo.agda | 9279 | | Multi-agent coordination: message ordering between agents? Shared state: concurrent read/write — consistency? Race conditions in agent interaction? Deadlock in agent communication? |
| S4 | InspectorDemo | server/InspectorDemo.agda | 5403 | | Inspector: model serialization complete? Peek response format — matches JS parser? Over command — type safety at JSON boundary? Performance: large model serialization — blocking? |

---

## 6. Build Pipeline (530 LOC)

| # | Тема | Файл | LOC | П | Что искать |
|---|------|------|-----|---|------------|
| B1 | CSS generation | scripts/generate-css.js | 129 | | Input: compiled Agda module with CSS declarations. Output: `.css` file. Selector escaping — special chars in class names? Property ordering — specificity? @import/@font-face — handled? Comments — stripped? Minification? |
| B2 | Animation data gen | scripts/generate-anim-data.js | 79 | | JSON output: valid JSON? Numeric precision? Empty animation list? Large datasets — memory? |
| B3 | Build verification | scripts/verify-build.sh + typecheck-all.sh | 185 | | All modules listed? New modules auto-discovered? Exit codes — correct? Error messages — actionable? Parallel execution — race conditions in file system? |
| B4 | ESM conversion | scripts/cjs-to-esm.cjs + fix-esm.cjs | 102 | | `require()` → `import` — all patterns handled? `module.exports` → `export` — named vs default? Dynamic require? Circular dependencies? Source maps — preserved? |

---

## 7. Tests (3,172 LOC)

| # | Тема | Файл | LOC | П | Что искать |
|---|------|------|-----|---|------------|
| T1 | Runtime tests | test/runtime.test.js | 760 | | Покрытие: какие функции НЕ тестируются? Assertions: правильные ли expected values? Flaky: timing-dependent tests? Isolation: тесты влияют друг на друга через shared state? |
| T2 | Fuzz tests | test/fuzz-runtime.mjs | 783 | | Покрытие: все ли exported функции фаззятся? Quality inputs: достаточно ли edge cases? Missing types: WeakRef, Proxy, generators, async iterators? |
| T3 | GL math tests | test/gl-math.test.js | 164 | | Edge cases: NaN input, Infinity, zero vectors, parallel vectors для lookAt, singular matrices, extreme aspect ratios. Precision: tolerance в float comparison — 1e-6 достаточно? |
| T4 | Data tests | test/json+array+datetime+forms.test.js | 657 | | JSON roundtrip: special chars, unicode, nested objects, arrays, null, numbers. DateTime: leap year, DST, timezone edge cases. Array: empty, single element, out of bounds. Forms: empty submit, invalid field types |
| T5 | CSS + clone + smoke | test/css-pipeline+clone+smoke.test.js | 703 | | CSS pipeline: all module CSS generates valid CSS? Clone: both Scott-encoding formats? Smoke: all 381 modules load — но тестирует ли что-то кроме загрузки? |

---

## Сводка

| Категория | Тем | LOC | П>0 | Приоритет |
|-----------|-----|-----|-----|-----------|
| JS Runtime | 40 | 9,775 | 35 | 🔴 Высший |
| Haskell Server | 6 | 1,476 | 0 | 🔴 Высший |
| Agda FFI | 3 | 527 | 0 | 🔴 Высший |
| Agda Core | 54 | 34,617 | 0 | 🟡 Средний |
| Examples | 8 | 8,722 | 0 | 🟢 Низкий |
| Server examples | 4 | 18,343 | 0 | 🟡 Средний |
| Scripts | 4 | 530 | 0 | 🟢 Низкий |
| Tests | 5 | 3,172 | 0 | 🟡 Средний |
| **Итого** | **124** | **77,162** | **35** |
