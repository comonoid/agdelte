# Code Improvement Plan

**Цель:** систематический review всей кодовой базы на code smells (не баги, а качество кода).

**~63K LOC**, 268+ файлов. Разбито на 7 зон, 42 темы.

## Как работать с этим документом

### Отличие от debug-plan-all.md

| | Bug hunting | Code improvement |
|---|---|---|
| Вопрос | "Что сломается?" | "Что лишнее, дублировано, усложнено?" |
| Действие | Исправить баг, добавить тест | Упростить, извлечь, переименовать, удалить |
| Риск | Высокий (может сломать) | Низкий (рефакторинг) |
| Тесты | Обязательно прогнать до и после | Обязательно прогнать после |

### Категории smell'ов (что искать)

| Код | Категория | Пример |
|-----|-----------|--------|
| DUP | Дублирование | Одинаковый блок в 3+ файлах |
| DEAD | Dead code | Неиспользуемая функция, unreachable ветка, закомментированный код |
| MAGIC | Magic values | `0.6`, `270.0`, `"Select..."` без имени |
| INCON | Inconsistency | Один контрол — record config, соседний — позиционные аргументы |
| OVER | Overcomplicated | 14 вариантов функции где хватит 2 с параметром |
| NAME | Naming | `sin'` в одном файле, `sin` в другом; `mk*` vs `create*` |
| LONG | Long function | >100 строк, делает 5 вещей |
| STRUCT | Structure | Модуль 700 строк без секций; helpers не извлечены в общий модуль |

### Промпт-шаблон

```
Ты делаешь CODE QUALITY review (не баг-хантинг) файлов [список].

Ищи конкретные code smells:
1. DUP: одинаковые блоки кода в разных файлах (>5 строк)
2. DEAD: неиспользуемые функции, конструкторы, импорты
3. MAGIC: хардкод значения без имени
4. INCON: одно и то же сделано по-разному в похожих файлах
5. OVER: избыточные варианты функций, глубокая вложенность
6. NAME: несогласованные имена для одного и того же
7. LONG: функции >100 строк
8. STRUCT: логика не извлечена в shared module

Для каждой находки:
- Категория (DUP/DEAD/MAGIC/...)
- Файл:строка (или диапазон)
- Конкретное описание: "строка 42 в File1 идентична строке 78 в File2"
- Что сделать: "извлечь в Shared.agda", "удалить", "переименовать X → Y"

Фокус на ПАТТЕРНАХ между файлами, не на отдельных файлах.
НЕ редактируй файлы, только отчёт.
```

### Порядок работы

1. Выбери зону из таблиц ниже (пустая колонка П = ещё не смотрели)
2. Прочитай все файлы зоны
3. Запиши findings в эту таблицу (колонка "Findings")
4. Исправь что можно, прогони тесты
5. Увеличь П

### После рефакторинга

1. Прогнать тесты: `node test/runtime.test.js && node test/fuzz-runtime.mjs && node test/gl-math.test.js`
2. Для Agda: `npm run build:<name>` для затронутых модулей
3. Обновить П в этом документе

---

## 1. SVG Controls (Agda) — 12 файлов, ~4400 LOC

Самая выгодная зона: 12 похожих файлов, огромное дублирование math helpers.

| # | Тема | Файлы | LOC | П | Findings |
|---|------|-------|-----|---|----------|
| Q1 | Math helpers duplication | Controls/*.agda, Charts/*.agda, Gauges/*.agda | ~200 | | DUP: π, sin', cos', normalize скопированы в 6+ файлов. clamp/clamp01 — в 6 файлов. findMin/findMax/zeroMin/zeroMax — в 5 файлов. case_of_ — в 3 файлов. Действие: извлечь в Agdelte/Svg/Math.agda |
| Q2 | Naming inconsistency | Controls/*.agda | ~100 | | NAME: sin'/cos' vs sin/cos (разные файлы). findMin/findMax vs findMinMax (Scatter). scaleX/scaleY vs scaleVal. Действие: унифицировать имена |
| Q3 | Magic numbers | Knob, Gauge, Progress, Timeline | ~50 | | MAGIC: 270.0 (knob angle range), 0.6 (indicator scale), 8.0 (padding), -135.0 (start angle), 60.0 (label threshold), -20.0/25.0 (label offsets). Действие: именованные константы |
| Q4 | Chart code patterns | Charts/Line, Area, Scatter, Bar, Pie | ~300 | | DUP: scaleX/scaleY, zeroMin/zeroMax, axis rendering — повторяются в каждом chart. INCON: Line uses lsFill string check, should be ADT. Действие: shared chart helpers |

## 2. HTML Controls (Agda) — 22 файла, ~6500 LOC

| # | Тема | Файлы | LOC | П | Findings |
|---|------|-------|-----|---|----------|
| Q5 | Variant explosion | Slider, Popover, Spinner, Breadcrumb | ~2000 | | OVER: Slider 14 вариантов, Popover 7, Spinner 8, Breadcrumb 3. Большинство — обёртки с 1-2 изменёнными параметрами. Действие: record config + 1-2 базовые функции |
| Q6 | API inconsistency | All Controls | ~500 | | INCON: одни контролы — record config (DatePicker, DataGrid), другие — позиционные args (Accordion, Slider). mk* vs plain name vs *With*. Действие: единый паттерн |
| Q7 | Shared helpers missing | Modal, Sidebar, TreeView, Pagination, DataGrid | ~200 | | DUP: focus sentinels (Modal), iconNodes (Sidebar×2), hasChildren (TreeView×2), empty-state rendering (Pagination, DataGrid, Table), case_of_ (4 файла). Действие: извлечь в Util |
| Q8 | Magic strings | DatePicker, Dropdown, Skeleton, Stepper, TreeView | ~100 | | MAGIC: "Select..." (Dropdown ×3), weekday names (DatePicker), "No data available" (DataGrid/Table), depth padding 16 (Stepper/TreeView ×3). Действие: именованные константы или параметры |
| Q9 | Local redefinitions | DatePicker, Checkbox, Progress, Breadcrumb | ~50 | | DUP: _==ℕ_ (DatePicker вместо ≡ᵇ), showℕ (Pagination + Stepper), eqStr import (inline vs module-level). Действие: использовать стандартные определения |

## 3. JS Runtime — 3 файла, ~3600 LOC

| # | Тема | Файлы | LOC | П | Findings |
|---|------|-------|-----|---|----------|
| Q10 | Long functions | reactive.js | ~800 | | LONG: renderNode (243 LOC, 16 cases), updateScopeImmediate (216), applyAttr (112), executeCmd (132). Действие: извлечь case-ветки в отдельные функции |
| Q11 | Event handler duplication | events.js | ~100 | | DUP: onKeyDown/onKeyUp/onMouseDown/onMouseUp/onClick — 6 идентичных паттернов (47 LOC). httpGet/httpPost — почти идентичны. WS cleanup ×2. Действие: factory function |
| Q12 | State flag naming | events.js | ~30 | | NAME: completed, running, terminated, finished — одно и то же разными именами в разных handlers. Действие: единое имя (cancelled/done) |
| Q13 | Magic numbers (JS) | events.js, reactive.js | ~20 | | MAGIC: spring threshold 0.001/0.01, dt cap 64, tick 4, Safari budget 8 (×2), rIC timeout 1000 (×2), MAX_DEPTH 64, maxHistory 100. Действие: именованные константы |

## 4. WebGL Runtime — 1 файл, ~5400 LOC

| # | Тема | Файлы | LOC | П | Findings |
|---|------|-------|-----|---|----------|
| Q14 | Long functions (GL) | reactive-gl.js | ~1000 | | LONG: makeLeafHandlers (322), initGLCanvas (~780), collectNode (~400), renderEntry (~230). Действие: split по типам |
| Q15 | Shader string duplication | reactive-gl.js | ~460 | | DUP: GLSL шейдеры как template literals — phong/pbr/text/pick шейдеры повторяют uniform declarations, MVP setup. Действие: shared GLSL snippets |
| Q16 | Geometry creation patterns | reactive-gl.js | ~800 | | DUP: 15 create*Geometry функций с одинаковым upload boilerplate. Действие: extractCommonGeometrySetup |
| Q17 | Config constants | reactive-gl.js | ~20 | | MAGIC: MAX_LIGHTS=8, GEO_CACHE_MAX=256, atlasSize=1024, clearColor(0.1,0.1,0.1,1), text alpha threshold 0.1. Действие: CONFIG object |

## 5. Agda Core + FFI — ~40 файлов, ~6000 LOC

| # | Тема | Файлы | LOC | П | Findings |
|---|------|-------|-----|---|----------|
| Q18 | Event/Sub constructors | Core/Event.agda, events.js | ~600 | | STRUCT: 32 конструктора Event+Sub в одном файле. Действие: split на Event.agda + Sub.agda или хотя бы секции |
| Q19 | Cmd constructors | Core/Cmd.agda, reactive.js | ~150 | | STRUCT: 23 конструктора Cmd в одном файле. Аналогично Event |
| Q20 | Node constructors | Reactive/Node.agda | ~420 | | STRUCT: 13 Node + 8 Attr + Transition — всё в одном файле. Действие: Attr в отдельный модуль |
| Q21 | Concurrent modules | Concurrent/*.agda (9 файлов) | ~1800 | | DEAD: wizardProtocol (SessionForm, удалён). INCON: Agent ⊕ (Wiring) vs dep⊕ (DepAgent) — два способа делать одно |
| Q22 | FFI postulates | FFI/Browser.agda, FFI/Server.agda, FFI/Shared.agda | ~530 | | STRUCT: postulates без группировки. Действие: секции (DOM, Storage, Network, etc.) |

## 6. CSS System (Agda) — ~10 файлов, ~2200 LOC

| # | Тема | Файлы | LOC | П | Findings |
|---|------|-------|-----|---|----------|
| Q23 | Variable coverage | Css/Variables.agda, Controls/*.agda | ~200 | | INCON: var(--agdelte-surface) не определена (Checkbox). Некоторые controls используют голые цвета вместо variables. Действие: аудит всех var() ссылок |
| Q24 | Control CSS patterns | Css/Controls/*.agda (15 файлов) | ~1400 | | DUP: :focus-visible блоки, border-radius var(), transition patterns — повторяются. Действие: shared mixins |

## 7. Examples + Server + Build + Tests — ~30 файлов, ~3500 LOC

| # | Тема | Файлы | LOC | П | Findings |
|---|------|-------|-----|---|----------|
| Q25 | Example boilerplate | examples/*.agda (16 файлов) | ~2000 | | DUP: ReactiveApp record construction boilerplate в каждом example. Import списки. Действие: shared prelude |
| Q26 | Server examples | server/*.agda (4 файла) | ~1000 | | STRUCT: InspectorDemo 5400 LOC — слишком большой, смешивает несколько concerns |
| Q27 | Test organization | test/*.js (7 файлов) | ~2500 | | STRUCT: runtime.test.js и fuzz-runtime.mjs используют replicated versions вместо actual exports. Действие: export internal helpers for testing |
| Q28 | Build scripts | scripts/*.js, scripts/*.sh | ~530 | | INCON: generate-css.js и generate-anim-data.js — похожая структура (load module, extract, write), но разный error handling |

---

## Сводка

| Зона | Тем | LOC | Приоритет | Ожидаемый выигрыш |
|------|-----|-----|-----------|-------------------|
| SVG Controls | 4 | ~4400 | 🔴 Высший | ~150 строк дублей, unified math |
| HTML Controls | 5 | ~6500 | 🔴 Высший | Variant explosion → record config |
| JS Runtime | 4 | ~3600 | 🟡 Средний | Factory functions, split long funcs |
| WebGL Runtime | 4 | ~5400 | 🟡 Средний | Split initGLCanvas, shared GLSL |
| Agda Core + FFI | 5 | ~6000 | 🟢 Низкий | Better module structure |
| CSS System | 2 | ~2200 | 🟢 Низкий | Shared mixins, var audit |
| Examples+Tests | 4 | ~3500 | 🟢 Низкий | Export internal helpers |

**Общий принцип:** начинай с 🔴, там самый высокий ROI. Зоны 🟢 трогай только если зоны 🔴🟡 уже чисты.
