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

- [ ] `src/Agdelte/Storage/IndexedMap.agda` — **абстрактный Agda-модуль над `NatMap`**
      (НЕ постулат-над-Haskell, концепт §3): record `{ primary : NatMap V ; indexes :
      … NatMap (List ℕ) ; extractors : … (V → List ℕ) }`; smart-конструкторы
      `insert/update/delete/lookup/byIndex/entriesFrom` (последняя — упорядоченная
      страница по `id` для пагинации §13, #K) держат индексы **в Agda**. Конструктор
      record'а **не экспортировать** (инкапсуляция). Нового `.hs` НЕ нужно.
- [ ] Две тонкости (концепт §3): `insert`=upsert **снимает старые индекс-ключи** перед
      добавлением новых (#N3 — иначе stale-записи); экстрактор **пропускает soft-deleted**
      (`deletedAt≠nothing → []`) → `byIndex` отдаёт только живые (#N7).
- [ ] `IndexName` — **типизированный тег** (не `String`, #P3); `entriesFrom` по `primary`
      включает soft-deleted → живая пагинация **пропускает удалённые** на ходу (#P4).
- [ ] Генерик property-тест: `indexes m ≡ rebuild (entries m)` после произвольной
      последовательности операций.
- [ ] Типечек.
- **Ревью человека:** дизайн абстракции/инкапсуляции (§15.4).

## Фаза 1 — Записи домена (`services-core/Crm/Identity.agda`)

- [ ] **Реструктурировать `Crm.Identity` в records-only:** убрать `CrmState`/`CrmOp`/
      `applyOp` (переедут в `Crm.Store`, Фаза 2), оставить только записи + их `Serialize`.
- [ ] Добавить записи: `Engagement`, `Activity` (FK `engagementId`), `Participation`
      (запись-факт M:N, синтетич. `id`). `PartyRecord` — уже есть.
- [ ] **uuid-слой (#3):** адресуемые сущности несут `uuid : String` (внешний id, §13).
- [ ] **`Agdelte.Json`-кодек** для каждой (комбинаторами; самоописывающий → аддитивная
      эволюция схемы обратно-совместима, #D). **Round-trip `decode (encode x) ≡ just x` на
      КАЖДЫЙ тип** (#N6 — кривой `decode` тихо испортит реплей).
- [ ] Типечек + grep-страж нейтральности (нет вертикалей в `services-core`).

## Фаза 2 — `Crm.Store` (сборка состояния)

- [ ] `Base` = **самоиндексирующиеся `IndexedMap`** по сущностям (`byUuid` на адресуемых;
      `byEngagement`/`byParty` на `participations`), `emptyBase`. **Отдельного
      `Indexes`/`reindex` НЕТ** (#2 — индексы внутри `IndexedMap`).
- [ ] `data CrmOp` — **типизированные конструкторы на сущность** (`SetParty Party | …`, не
      generic `SetEntity tag value` — #N5, нет рассогласования тег↔значение) + доменные
      команды; `apply : CrmOp → Base → Base` через `IndexedMap.insert/delete`. **`apply`
      продвигает `nextId := max(nextId, id+1)`** на создающих ops (#N1 — иначе коллизии id
      после рестарта).
- [ ] **Недетерминизм (#N2):** `uuid`/время/random — НЕ в чистой транзакции; их генерит
      IO-обработчик и **передаёт параметром** в построитель транзакции → оседают в `Op`.
- [ ] `data Err` (NotFound|Conflict|Insufficient|InvalidTransition|Forbidden|Invariant).
- [ ] `walSerializeOp`/`walDeserializeOp`; `WalConfig` через `mkWalConfigNoSnapshot`.
- [ ] Типечек.

## Фаза 3 — Транзакции (`Crm.Txn` + `walTxn` в `agdelte`)

- [ ] **WAL: единица записи = ТРАНЗАКЦИЯ + фрейминг (prerequisite, концепт §18; #1).**
      Сейчас лог строковый и пишет ops **по одной** → (1) краш между ops рвёт
      **атомарность** транзакции; (2) `\n` в payload портит парс. Фикс: весь `List Op`
      транзакции — **одна length-prefixed запись + один `fsync`**; рваный хвост
      отбрасывается **целиком**. До операций со свободным текстом (тела заметок/сообщений).
- [ ] В `Storage.WAL` — **`walTxn : WalHandle → (Base → Either Err (Base × List Op × A)) → IO (Either Err A)`**
      (обобщение `walModify`). **Порядок: durable ДО visible** — запись+`fsync`, и только при
      успехе `putMVar base'`; **отказ записи WAL** (диск/IO) → восстановить старый `MVar`
      (`onException`) + вернуть ошибку (#N4). **`onException` оборачивает ВСЮ секцию**
      (прогон txn тоже) — иначе бросивший txn → пустой `MVar` → deadlock (#P2). Заодно по
      ADR: `walRead → readMVar`, убрать снапшотные следы (`walOpCount`, `loadSnapshot`).
- [ ] `Crm.Txn` — монада `Txn` (`return`/`_>>=_`/`getBase`/`abort`/**`emit`**, где
      `emit op = apply op + лог`), доменные «сеттеры»/команды поверх `emit`. Аккумулятор
      ops — **difference-list** (не `++`), иначе bulk-каскад O(n²) (#P1).
- [ ] Типечек; (по возможности) набросок property-теста `live ≡ replay`.
- **Ревью человека:** транзакционная семантика, `Err`/authz (§15.4).

## Фаза 4 — Реальные транзакции (мерило «естественно ли»)

- [ ] `addParticipant` (store-инвариант FK — рантайм-проверка).
- [ ] `scheduleActivity`/`bookSession` (проверка «слот свободен»).
- [ ] **Удаление (#E):** soft-delete по умолчанию; hard-delete — транзакция **явно каскадит**
      / проверяет отсутствие ссылок через обратные индексы (иначе dangling FK).
- [ ] **Один value-инвариант correct-by-construction** через разрешимость
      (`charge`/`decBalance` с `amt ≤? bal` → proof). Измерить планку: сколько
      итераций, не сполз ли в `postulate`/`primTrustMe` (ревью обязано ловить).

## Фаза 5 — Headless-вход (`Crm.Api`) + живой прогон

- [ ] Минимальные HTTP-обработчики (как pg-spike): `GET` → `readMVar`+запрос; `POST`
      → `walTxn`. Конверт `{data}`/`{error}` (§13).
- [ ] Entry-модуль + cabal-таргет; сборка (`-threaded`, `LIBRARY_PATH` zlib на NixOS).
- [ ] **Живой прогон:** старт → записать (несколько транзакций) → рестарт → реплей →
      состояние совпало; запрос по вторичному индексу работает.
- [ ] Инвариант индексов — генерик property-тест `indexes m ≡ rebuild (entries m)` уже в
      Фазе 0; здесь убедиться, что доменные транзакции его не ломают (запрос по `byIndex`
      после серии операций даёт верный результат).

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
- **краш-тестирование recovery** — нет fault-injection-харнеса; durability не проверяется автоматически.

## Результат фазы 5

Ходячее персистентное транзакционное CRM-ядро на WAL: записи + индексы + транзакции +
recovery, с доказанным (тестом) инвариантом — и видно глазами, читается ли оно «как
обычная ФП-программа».
