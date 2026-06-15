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

- [ ] `hs/Agdelte/IndexedMap.hs` — `IntMap V` + объявленные вторичные индексы
      (`IntMap IntSet`), smart-конструкторы `insert/update/delete/lookup/byIndex`,
      авто-поддержка индексов. Представление скрыто (абстрактный тип).
- [ ] `src/Agdelte/Storage/IndexedMap.agda` — постулаты над ним (как `NatMap`):
      `IndexedMap : Set → Set`, операции, экстрактор индекса `V → List ℕ`.
- [ ] Типечек; (опц.) cabal-проба, что Haskell-структура компилируется.
- **Ревью человека:** дизайн FFI-границы (§15.4).

## Фаза 1 — Записи домена (`services-core/Crm/Identity.agda`)

- [ ] **Реструктурировать `Crm.Identity` в records-only:** убрать `CrmState`/`CrmOp`/
      `applyOp` (переедут в `Crm.Store`, Фаза 2), оставить только записи + их `Serialize`.
- [ ] Добавить записи: `Engagement`, `Activity` (FK `engagementId`), `Participation`
      (запись-факт M:N). `PartyRecord` — уже есть.
- [ ] `Serialize` для каждой (рекурсивный/выводимый), incl. вложенные значения.
- [ ] Типечек + grep-страж нейтральности (нет вертикалей в `services-core`).

## Фаза 2 — `Crm.Store` (сборка состояния)

- [ ] `Base` (таблицы на `IndexedMap`), `Indexes` (если что-то вне `IndexedMap`),
      `CrmState = Base × Indexes`, `emptyBase`.
- [ ] `data CrmOp` (`SetEntity`/`DeleteEntity` generic + доменные команды);
      `apply : CrmOp → Base → Base` (через `IndexedMap`); `reindex : Base → Indexes`.
- [ ] `data Err` (NotFound|Conflict|Insufficient|InvalidTransition|Forbidden|Invariant).
- [ ] `walSerializeOp`/`walDeserializeOp`; `WalConfig` через `mkWalConfigNoSnapshot`.
- [ ] Типечек.

## Фаза 3 — Транзакции (`Crm.Txn` + `walTxn` в `agdelte`)

- [ ] **WAL-фрейминг (prerequisite, см. концепт §18):** текущий лог строковый
      (`splitLines`/`\n`) — `\n` в payload (тела заметок/сообщений) расщепит запись,
      рваный хвост может распарситься неверно. Перейти на **length-prefix**
      (`<len>:<байты>`, идиома `FFI.Shared.encodeListLP`) **до** операций со свободным
      текстом. (Для `party`/`engagement` без переводов строк можно отложить, но заложить.)
- [ ] В `Storage.WAL` — **`walTxn : WalHandle → (Base → Either Err (Base × List Op × A)) → IO (Either Err A)`**
      (обобщение `walModify`; аппенд ops на коммит, no-op откат). Заодно по ADR:
      `walRead → readMVar`, убрать снапшотные следы (`walOpCount`, `loadSnapshot`).
- [ ] `Crm.Txn` — монада `Txn` (`return`/`_>>=_`/`getBase`/`abort`/**`emit`**, где
      `emit op = apply op + лог`), доменные «сеттеры»/команды поверх `emit`.
- [ ] Типечек; (по возможности) набросок property-теста `live ≡ replay`.
- **Ревью человека:** транзакционная семантика, `Err`/authz (§15.4).

## Фаза 4 — Реальные транзакции (мерило «естественно ли»)

- [ ] `addParticipant` (store-инвариант FK — рантайм-проверка).
- [ ] `scheduleActivity`/`bookSession` (проверка «слот свободен»).
- [ ] **Один value-инвариант correct-by-construction** через разрешимость
      (`charge`/`decBalance` с `amt ≤? bal` → proof). Измерить планку: сколько
      итераций, не сполз ли в `postulate`/`primTrustMe` (ревью обязано ловить).

## Фаза 5 — Headless-вход (`Crm.Api`) + живой прогон

- [ ] Минимальные HTTP-обработчики (как pg-spike): `GET` → `readMVar`+запрос; `POST`
      → `walTxn`. Конверт `{data}`/`{error}` (§13).
- [ ] Entry-модуль + cabal-таргет; сборка (`-threaded`, `LIBRARY_PATH` zlib на NixOS).
- [ ] **Живой прогон:** старт → записать (несколько транзакций) → рестарт → реплей →
      состояние совпало; запрос по вторичному индексу работает.
- [ ] **Property-тест `idx ≡ reindex base`** после произвольной последовательности op.

## Гейты ревью (§15.4 — не мерджить автономно)

Дизайн FFI-границы (`IndexedMap`, `walTxn`) · `Err`/authz · доказательства (ловить
`postulate`/`primTrustMe`/`{-# TERMINATING #-}` — они обнуляют гарантию).

## Что НЕ в этом плане (parked, см. §15 концепта)

Снапшоты · пейджинг · конкуренция/SSI · `Free Applicative` · тяжёлые доказательства ·
кросс-коллекционные агрегаты · auto-index DSL · Postgres-путь · деньги/outbox/омни/UI
(следующие срезы после ходячего ядра).

## Результат фазы 5

Ходячее персистентное транзакционное CRM-ядро на WAL: записи + индексы + транзакции +
recovery, с доказанным (тестом) инвариантом — и видно глазами, читается ли оно «как
обычная ФП-программа».
