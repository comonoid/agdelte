# План: CRM-ядро на WAL (storage + домен + транзакции)

Исполняемый чеклист. Дизайн и механика — в
[concepts/storage-model.md](concepts/storage-model.md); решение — в
[adr/0001](adr/0001-storage-wal-in-memory.md). Этот файл **меняется по ходу**
(отмечаем сделанное); концепт-док — стабильный референс.

Принцип проверки на каждом шаге: **тайпчек + (где есть рантайм) живой прогон**, и
помним про устаревший `.agdai`-кэш — при сомнении `npm run clean` + чистая
регенерация (см. [POSTGRES-SPIKE.md](POSTGRES-SPIKE.md)).

## Уже сделано (контекст)

- [x] Task 0 — Postgres-спайк (запасной путь, hpgsql); cabal+freeze сборка.
- [x] §14.2 — раскладка `services-core/packs/app` + grep-стражи + раннер миграций.
- [x] §14.3 (0001) — SQL-схема идентичности (для Postgres-пути; на WAL-пути не нужна).
- [x] `Crm.Identity` — **выбросной прототип** `party` (записи + `CrmState`/`CrmOp`/`applyOp`).
      ⚠️ Его `CrmState`/`CrmOp`/`applyOp` **переедут в `Crm.Store`** (Base/CrmOp на `IndexedMap`), а
      `Crm.Identity` останется **только записями** — это **реструктуризация, не дополнение**.
- [x] ADR 0001 + concepts/storage-model.md — решение, концепция, механика.

## Фаза 0 — `IndexedMap` (генерик-инфра, `agdelte`)

- [x] `src/Agdelte/Storage/IndexedMap.agda` — **абстрактный Agda-модуль над `NatMap`**
      (приватные record'ы `Slot`/`IM` → конструктор не виден импортёрам); `empty (со
      списком экстракторов) / insert / delete / lookup / byIndex / entriesFrom / toList`,
      индексы поддерживаются **в Agda**. Нового `.hs` нет. ✓ типечек.
- [x] `insert`=upsert **снимает старые индекс-ключи** перед новыми (#N3) — **проверено
      рантайм-тестом** (update меняет индексируемое поле → нет stale). N7 (экстрактор
      пропускает soft-deleted) — это работа **экстрактора сущности** (слой домена), IndexedMap
      его поддерживает.
- [~] `entriesFrom` по `primary` (упорядочено по `id`) — есть. `IndexName` типизированный
      (#P3) — это **тонкая обёртка на слое сущности** (в IndexedMap индекс по позиции ℕ);
      живая пагинация пропускает soft-deleted на месте (#P4) — на слое запроса.
- [x] Property-тест — `server/IndexedMapTest.agda` (рантайм, т.к. NatMap — постулат): 5
      ассертов insert/update-retract/delete/byIndex, **все PASS** (`npm run test:im`).
- [x] Типечек.
- ⚠️ Попутно починен латентный баг `NatMap.agda`: `type`-декл в FOREIGN-блоке ломал GHC
      (MAlonzo дописывает импорт после) → тип задан инлайн в COMPILE-прагме. NatMap раньше
      был JS-only.
- **Ревью человека:** дизайн абстракции/инкапсуляции (§15.4).

## Фаза 1 — Записи домена (`services-core/Crm/Identity.agda`)

- [x] **`Crm.Identity` → records-only:** убраны `CrmState`/`CrmOp`/`applyOp` (переедут в
      `Crm.Store`, Фаза 2). ✓
- [x] Записи: `Party`, `Engagement`, `Activity` (FK `aEngagementId`), `Participation`
      (M:N-факт, синтетич. `prId`) + `PartyType`/`ActStatus`/`Role`. ✓ типечек.
- [~] **uuid-слой (#3) — УБРАН (2026-06-16).** Внешний id = внутренний `id` (`nextId`).
      Анализ показал: все плюсы uuid здесь будущие/не-доставляемые, а единственный «с зубами»
      (непрозрачность) — часть authz и должен ехать вместе с ним при появлении внешнего/
      недоверенного клиента. Поля `*Uuid`/`genUuid`/uuid-кодеки сняты. См. memory `crm-uuid-dropped`.
- [x] **Чистый Agda-кодек** `encode/decode` — `Agdelte.Storage.Wire` (генерик: `readℕ`,
      length-prefix `<len>:<s>`, ридер-монада, прим. кодеки) + `Crm.Wire` (enum'ы + 4 записи).
      GHC+JS, позиционный (Json/FFI.Shared — JS-only, аудит кодом). **Round-trip
      `server/CrmWireTest.agda` — 7/7 PASS на GHC** (`npm run test:crmwire`), incl. `:`/`|` в
      полях, `nothing`/`just`, все enum'ы (#N6). ✓
- [x] grep-страж нейтральности (нет вертикалей). ✓

## Фаза 2 — `Crm.Store` (сборка состояния)

- [x] `Base` = **самоиндексирующиеся `IndexedMap`** по сущностям (`activities` byEngagement;
      `participations` byEngagement/byParty — FK-индексы), `emptyBase`. **Отдельного
      `Indexes`/`reindex` НЕТ** (#2 — индексы внутри `IndexedMap`). `byUuid`-хеш отложен на
      слой API (Фаза 5). ✓
- [x] `data CrmOp` — **типизированные конструкторы на сущность** (`SetParty Party | …`, не
      generic `SetEntity tag value` — #N5) + `Del*`; `apply : CrmOp → Base → Base` через
      `IndexedMap.insert/delete`. **`apply` продвигает `nextId := max(nextId, id+1)`** на
      создающих ops (#N1) — **проверено рантайм-тестом** (`nextId=13` после реплея). ✓
- [~] **Недетерминизм (#N2):** механика — на слое `Txn`/handler (Фаза 3/5); здесь `uuid`/время
      уже **поля записей** (оседают в `Op` через `Set*`), генерации в `Store` нет. ✓ по части Store.
- [x] `data Err` (NotFound|Conflict|Insufficient|InvalidTransition|Forbidden|Invariant). ✓
- [x] `encodeOp`/`decodeOp` (теговый кодек операций для WAL #D) — **round-trip проверен**
      (`op-roundtrip` PASS, incl. `Del*`). `WalConfig`/`mkWalConfigNoSnapshot` — Фаза 3 (движок WAL).
- [x] Типечек + **рантайм-тест `server/CrmStoreTest.agda` 7/7 PASS** (`npm run test:crmstore`):
      M:N-индексы в обе стороны, 1:N, `nextId`, lookup, op-roundtrip.

## Фаза 3 — Транзакции (`Crm.Txn` + `walTxn` в `agdelte`)

- [x] **WAL: единица записи = ТРАНЗАКЦИЯ + ДВА уровня фрейминга (#1, B).** Внешняя рамка
      `<byteLen>:<payload>` — **байтовая, в FFI** (`appendWalRecord`/`readWalRecords`);
      внутренняя `concat lp(serializeOp opᵢ)` — символьная, в Agda (`serializeTxn`/`applyRecord`).
      Транзакция = **одна запись + один `fsync`**; рваный **хвост** дропается **целиком**
      (атомарность); `\n`/`:`/`|`/многобайт в payload безопасны.
- [x] **⚠️ Байт-vs-символ (находка ревью).** Исходно внешний префикс был символьным —
      ревью показал: ленивый UTF-8-декод **не сохраняет длину**, рваный многобайтный хвост
      мог посчитаться «полной» записью → `die` на восстановимом логе. Фикс: байтовая внешняя
      рамка. ✓ тест: кириллица переживает обрыв **посреди символа** (S1, `name-roundtrip`).
- [x] **⚠️ A (находка сверх плана): ленивый UTF-8-декод.** Строгий `TIO.readFile` бросал бы
      на рваном UTF-8-хвосте → `""` → **потеря всей истории**. `readWalRecords` читает raw-bytes,
      декодит **только полные** записи → потери нет.
- [x] **⚠️ D (находка сверх плана): порча в СЕРЕДИНЕ лога → отказ старта.** Недекодируемая
      запись → `die` (refuse to start), **не** молчаливый пропуск. ✓ тест ловит `die` (S2).
- [x] **⚠️ B1 (находка ревью): `fsync` родительской директории при создании лога.** Иначе
      dir-entry нового файла мог не дойти до диска → первая транзакция теряется при power-loss.
      `appendWalRecord` `fsync`-ает директорию при первом создании файла.
- [x] **`walTxn : WalHandle → (S → E ⊎ (S × List Op × A)) → IO (WalOutcome E A)`** поверх
      **`modifyMVarMasked`** — форсинг txn + durable-write под одной маской (C/E/F): durable
      ДО visible (новое состояние публикуется только после `fsync`); отказ диска → состояние
      восстановлено, `ioFailed`; reject → ничего не пишется. `walStep`/`walModify` — тонкие
      обёртки (call-sites Payment/Auth не тронуты). `walRead → readMVar`; снапшоты убраны,
      `WalConfig` сжат (G/H).
- [x] `Crm.Txn` — монада `Txn` (`returnT`/`_>>=T_`/`getBase`/`abort`/**`emit`**, `require`),
      `emit op = apply op + лог`. Аккумулятор ops — **difference-list** (O(1) snoc, #P1).
      `runTxn` даёт ровно ту сигнатуру, что ест `walTxn`. ✓ типечек.
- [x] **Fault-injection тест** `server/WalRecoveryTest.agda` (#8) — **11/11 PASS на GHC**
      (`npm run test:walrec`): commit, **кириллица через рваный мид-символ хвост** (S1),
      реконструкция `nextId`, отказ при порче в середине (S2), reject-путь (S3), ioFailed-путь
      (S4). `live ≡ replay` — by construction (`emit`=тот же `apply`, что и реплей).
- **Ревью человека (ГЕЙТ):** транзакционная семантика, durable-before-visible, `Err`/authz (§15.4).
- **Авто-ревью (2 агента) — разобрано:** байт-фрейминг + B1 + A + D **исправлены и
      покрыты тестами**. Отложено/задокументировано: S1-shallow-`evaluate` (ленивая ⊥ в новом
      состоянии — реплей воспроизводит детерминированно, не ломает `live≡replay`; полагаемся
      на тотальность `apply`), S2-`ioFailed`-семантика (= «не закоммичено», включает async-cancel,
      не только диск), нет CRC (бит-рот с заниженной длиной — редкий; см. ниже), Payment
      cross-resource (см. ниже).

## Фаза 4 — Реальные транзакции (мерило «естественно ли») ✓

Всё в `services-core/Crm/Commands.agda` (+ `Crm.Txn` комбинаторы `requireJust`/`guardT`/
`forEachT`). Тест `server/CrmCommandsTest.agda` — **10/10 PASS на GHC** (`npm run test:crmcommands`).

- [x] `addParticipant` — FK-проверка **обоих** концов (engagement и party существуют и live),
      id из `nextId b`. ✓ (reject `NotFound` на несуществующих).
- [x] `bookSession` — проверка «слот свободен» через **обратный индекс** `byEngagement`
      (нет live не-canceled активности в то же время). ✓ (conflict / другой слот / re-book
      после cancel).
- [x] `cancelActivity` — **гард перехода статуса** (`Scheduled → Canceled`; повтор →
      `InvalidTransition`). ✓
- [x] **Удаление (#E):** `hardDeleteEngagement` — транзакция **явно каскадит** через обратные
      индексы (`DelActivity`/`DelParticipation` по всем, потом `DelEngagement`) → нет dangling FK.
      ✓ тест `cascade-clean`. (Soft-delete = обычный `Set*` с `*DeletedAt`, уже есть.)
- [x] **value-инвариант correct-by-construction:** `charge` поверх `Account` (новая сущность —
      добавлена через весь стек Identity→Wire→Store **механически**). `debit : (bal amt : ℕ) →
      amt ≤ bal → ℕ` нельзя **вызвать** без доказательства; пруф даёт только ветка `yes` от
      `_≤?_`, ветка `no` обязана `abort Insufficient`. **Планка:** прошло с первого раза, БЕЗ
      `postulate`/`primTrustMe`/`{-# TERMINATING #-}`, без боёв с тайпчекером — паттерн
      разрешимости эргономичен. ✓ тест: debit 1000→700, overdraft→`Insufficient` (баланс цел),
      credit 1000→1050.

## Фаза 5 — Headless-вход (`Crm.Api`) + живой прогон ✓

`services-core/Crm/Api.agda` (обработчики+роутер+конверт) + `server/CrmServer.agda` (entry:
`walOpen`+`listen`). Cabal-таргет `crm-server`; live-скрипт `scripts/crm-live-run.sh`
(`npm run crm:live`).

- [x] HTTP-обработчики: `GET` → `walRead`+запрос; `POST` → парс JSON-тела → построить `Txn`
      → `walTxn`. Конверт `{data}`/`{error}` (§13); `Err`→HTTP-статус (404/409/402/…).
      Внешний id = внутренний `id` (uuid убран, см. выше).
- [x] Entry-модуль + cabal-таргет `crm-server` (`-threaded`, `LIBRARY_PATH` zlib на NixOS).
      ⚠️ попутно починен `FFI.Time` (трейлинг-def в FOREIGN стрэндил авто-`import Data.Text` →
      тело инлайнено в COMPILE-прагму; та же грабля, что NatMap/FileSystem).
- [x] **Живой прогон (`scripts/crm-live-run.sh`):** старт → `POST /accounts`+`/charge`+`/parties`
      (incl. overdraft → 402, кириллица «Полунин») → `GET` показывает balance 700 → **рестарт**
      → `GET` снова balance 700 и «Полунин» — **реплей из `crm.wal`
      совпал**. correct-by-construction инвариант денег держится **через HTTP**.
- [x] Инвариант индексов под доменными транзакциями — `byIndex` после серии операций даёт
      верный результат: покрыто `CrmCommandsTest` (slot/cascade через обратные индексы).
- [—] **`byUuid` — СНЯТО с повестки** (uuid убран). Адресация по внутреннему `id`. Вернётся
      вместе с uuid+authz при появлении внешнего клиента (тогда же осознанно выбрать вариант,
      возможно ULID); рецепт хеш-индекса — в memory `crm-uuid-dropped` / истории git.

## Гейты ревью (§15.4 — не мерджить автономно)

Дизайн FFI-границы (`IndexedMap`, `walTxn`) · `Err`/authz · доказательства (ловить
`postulate`/`primTrustMe`/`{-# TERMINATING #-}` — они обнуляют гарантию).

## Что НЕ в этом плане (parked, см. §15 концепта)

Снапшоты · пейджинг · конкуренция/SSI · `Free Applicative` · тяжёлые доказательства ·
кросс-коллекционные агрегаты · auto-index DSL · **бинарный формат WAL/компрессия**
(отложенная локальная замена кодека, концепт §18) · Postgres-путь · деньги/outbox/омни/UI
(следующие срезы после ходячего ядра).

## Открытые концы (спроектировать по ходу — концепт «Открытые концы»)

- **authz/ACL** — где проверять (вероятно handler→`Txn`→ACL против `Base` → `Err Forbidden`); механизм ACL не спроектирован.
- **эволюция схемы** — версионированный `Serialize` либо разовый WAL-конвертер при смене формата.
- **рост WAL** — снапшотов нет → лог пухнет, старт-реплей линеен; на верхней границе ниши нужен чекпойнт/ротация.
- **краш-тестирование recovery** — ✓ есть `server/WalRecoveryTest.agda` (рваный мид-символ
  хвост, порча в середине, reject, ioFailed); расширять при изменении формата WAL. Что НЕ
  покрыто: одновременный краш процесса (только симуляция обрыва файла), частичный `fsync`.
- **целостность WAL без CRC** — ревью: бит-рот, **занижающий** заявленную длину записи, может
  дать самосогласованный «другой» набор ops без `die` (обычный случай порчи всё же ловится).
  Решить нужен ли per-record checksum (CRC32) до выхода за пределы доверенного диска/ниши.
- **Payment cross-resource (ревью S3, легаси-модуль)** — `Payment.handlePurchase` зовёт ЮKassa
  `createPayment` **до** `walStep`; отказ WAL-записи после реального платежа бросает
  необёрнутое исключение, запись о покупке не персистится. WAL durability цела, но нужна
  компенсация/реконсиляция и 5xx на HTTP-слое. Не Phase-3-код; чинить при доводке Payment.

## Результат фазы 5

Ходячее персистентное транзакционное CRM-ядро на WAL: записи + индексы + транзакции +
recovery, с доказанным (тестом) инвариантом — и видно глазами, читается ли оно «как
обычная ФП-программа».
