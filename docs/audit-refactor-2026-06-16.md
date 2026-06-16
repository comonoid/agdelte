# Аудит рефакторинга: декомпозиция на библиотеки — 2026-06-16

Мульти-агентный адверсариальный аудит: 4 finder-агента по либам (store/payments/crm/courses) + 1 на стыки → независимая верификация каждой находки → синтез. 32 агента. 10 подтверждено (все LOW) из 26.

{
  "summary": "Adversarial multi-agent audit of the library decomposition (store/payments/crm/courses + integration)",
  "agentCount": 32,
  "logs": [],
  "result": {
    "confirmedCount": 10,
    "totalReported": 26,
    "summary": "# Отчёт аудита: декомпозиция монолита на библиотеки

Все 10 находок имеют severity **low**. Критических и средних дефектов нет. Группирую по темам, внутри — по практическому риску.

---

## A. Устаревшие зависимости в `agdelte.agda-lib` (находки 1, 4, 5, 7)

Четыре находки описывают одну и ту же проблему с разных сторон. Сводно:

- **`agdelte-payments` — мёртвая зависимость.** Ни один файл во всём репозитории agdelte (`src/`, `server/`, `examples/`, `test/`, `app/`, `packs/`) не импортирует `Agdelte.Payment.*`/`YooKassa`; единственный потребитель — `agdelte-courses`, который уже объявляет dep сам.
  Локация: `~/.agda/agdelte/agdelte.agda-lib` (`depend: agdelte-payments`).
  Фикс: убрать `agdelte-payments` из `depend`.

- **`agdelte-store` — реальная, но «не на том слое» зависимость.** В `src/` её тоже никто не импортирует (только комментарий в `src/Agdelte/FFI/FileSystem.agda:63`); реальные потребители — 7 файлов под `server/` (`CrmServer.agda:13` и тесты), а `server/` не входит в `include: src`. Сборка живого crm-server опирается на явные `-i src -i server` + регистрацию библиотек, а не на `include`.
  Локация: `~/.agda/agdelte/agdelte.agda-lib` (`include: src`, `depend: ... agdelte-store`).
  Фикс: либо `include: src server`, либо комментарий в `.agda-lib`, что store нужен app-слою `server/`, а не `src/`.

Замечание о согласованности: находки 1, 4, 5, 7 частично дублируют друг друга и местами противоречат в трактовке `agdelte-store` (находка 1 называет обе deps «реальными»; находки 5/7 уточняют, что store не используется в `src`, только в `server/`). Верификаторы сошлись на едином выводе — он отражён выше; дублирование не меняет существа.

---

## B. Устаревшая документация после выноса CRM (находки 6, 9)

- **`CLAUDE.md` описывает несуществующую in-repo раскладку CRM.** Слои `app → packs → services-core → agdelte` и «`services-core/`, `packs/`, `app/`, каждый со своим `.agda-lib`» больше не соответствуют: `services-core/` вынесен в `~/.agda/agdelte-crm`, а `app/`+`packs/` содержат лишь README/.gitkeep/SQL. Те же устаревшие ссылки в `docs/SPEC.md` (6) и `docs/plan-crm-core.md` (4).
  Локация: `~/.agda/agdelte/CLAUDE.md:7,29,34`.
  Фикс: переписать секции раскладки/нейтральности под новую декомпозицию зарегистрированных библиотек.

- **`docs/audit-2026-06-16.md` ссылается на мёртвые пути `services-core/Crm/*`.** Строки `:181/:144/:84/:70` указывают на файлы, теперь живущие в `~/.agda/agdelte-crm/Crm/Api.agda`.
  Локация: `~/.agda/agdelte/docs/audit-2026-06-16.md:19,25,31,34`.
  Фикс: обновить пути на `agdelte-crm` или пометить как «извлечено».
  *Уточнение (по верификатору):* часть находки про `SPEC.md §4` слабая — там `services-core` используется как **имя архитектурного слоя**, а не как путь к файлу; это не path-rot, и её из находки стоит исключить.

---

## C. Сломанный/устаревший страж нейтральности (находка 8)

- **Guard 2 в `check-neutrality.sh` стал постоянным no-op.** Он гейтится на `[ -d services-core ]`; после выноса CRM каталога нет, `&&` короткозамыкается, проверка `psych|vet|transfer|медцентр` не выполняется, а скрипт печатает `✓ OK`. Blast radius ограничен: `check:neutrality` — только ручной `npm run`, не в CI/precommit. Guard 1 (`src/`+`hs/`) ещё работает.
  Локация: `~/.agda/agdelte/scripts/check-neutrality.sh:18-21`.
  Фикс: нацелить guard 2 на `~/.agda/agdelte-crm/Crm` (или падать громко при отсутствии каталога), либо перенести скрипт в репозиторий agdelte-crm.

---

## D. Устаревшие комментарии и латентная хрупкость (находки 2, 10)

- **Устаревший doc-комментарий в `WAL.agda`.** `walStep/walModify` помечены «Kept for existing callers (Payment, Auth)», но store — domain-agnostic stdlib-only слой и этих потребителей не видит.
  Локация: `~/.agda/agdelte-store/Agdelte/Storage/WAL.agda:167`.
  Фикс: переписать нейтрально («convenience-обёртки для вызовов без txn-канала ошибок»), убрать имена Payment/Auth.
  *Уточнение (по верификатору):* доказательная база находки фактически неверна — реальные вызывающие живут вместе в `agdelte-courses` (`Agdelte/Payment.agda`, `Agdelte/Auth/Handler.agda`), а не в `agdelte-payments`/фреймворке; они не были разнесены. На суть (косметический nit) это не влияет.

- **Латентная хрупкость пространства имён `Agdelte.Payment.*`.** `agdelte-courses` владеет родительским модулем `Agdelte.Payment`, а `agdelte-payments` — дочерним `Agdelte.Payment.YooKassa` из другого репозитория. Сегодня компилируется (Agda это допускает), но если payments когда-нибудь добавит bare `Agdelte/Payment.agda` (фасад, упомянутый в его `.agda-lib`), будет настоящая коллизия полных имён.
  Локация: `~/.agda/agdelte-courses/Agdelte/Payment.agda:15` vs `~/.agda/agdelte-payments/Agdelte/Payment/YooKassa.agda`.
  Фикс: сейчас действий не требуется; на будущее — зарезервировать bare `Agdelte.Payment` за payments либо переименовать модуль courses в `Agdelte.Courses.Payment`.

---

## E. Положительное наблюдение (находка 3)

- **FOREIGN-блок в `YooKassa.agda` корректно консолидирован import-first.** Все 14 Haskell-импортов идут до первого определения (`type HttpManagerT` на строке 52); оригинал имел 6 разрозненных FOREIGN-блоков с дублем `import qualified Data.Text as T` и импортами после определений — классический сценарий MAlonzo-stranding под GHC. Это реальное упрочнение сборки.
  Локация: `/home/n/.agda/agdelte-payments/Agdelte/Payment/YooKassa.agda:36-161`.
  Фикс: не требуется.

---

## Вердикт

Декомпозиция **состоятельна**: разрезы по библиотекам корректны, зависимости-рёбра между ними объявлены верно (courses→payments, courses→store/crm), всё типизируется, а консолидация FFI в payments — явное улучшение. Все 10 находок имеют severity low и не содержат ни одного дефекта сборки или поведения: это гигиена конфигурации (мёртвый dep `agdelte-payments` и не-на-том-слое `agdelte-store` в `agdelte.agda-lib`), дрейф документации после выноса `services-core/` и один обессмысленный страж нейтральности. Рекомендуется быстрый clean-up sweep (убрать `agdelte-payments` из `depend`, починить guard 2, синхронизировать `CLAUDE.md`/docs), после чего декомпозицию можно считать чистой.",
    "confirmed": [
      {
        "title": "agdelte.agda-lib's depend on agdelte-store/agdelte-payments is satisfied only by server/, which is OUTSIDE the lib's include: src",
        "file": "~/.agda/agdelte/agdelte.agda-lib",
        "severity": "low",
        "evidence": "agdelte.agda-lib has `include: src` and `depend: standard-library agdelte-store agdelte-payments`, but a grep for `Agdelte.Storage`/`Agdelte.Payment` over src/ finds only a comment in src/Agdelte/FFI/FileSystem.agda (no actual import). The real consumers are under server/ (CrmServer, WalRecoveryTest, StoreTxnTest, etc.), which the lib does not include — server/ is built via explicit `agda -i src -i server` in package.json, relying on the cwd .agda-lib's depend for store/payments resolution. So the deps are real (the live crm-server binary needs them — `agda -i src -i server -i agdelte-crm server/CrmServer.agda` typechecks end-to-end) but they belong to the app/server layer, not the `src` framework. Not a build breakage today; a latent inconsistency if anyone trusts include:src to bound what the dep is for, or extracts src/ alone.",
        "fix": "Either add server to include (`include: src server`) so the declared deps correspond to in-include code, or document in the .agda-lib that agdelte-store/agdelte-payments are consumed by the server/ app layer (built with explicit -i), not by src/.",
        "dimension": "store",
        "verdict": {
          "isReal": true,
          "confidence": "high",
          "severityAdjusted": "low",
          "note": "Confirmed in actual code/config. ~/.agda/agdelte/agdelte.agda-lib has `include: src` and `depend: standard-library agdelte-store agdelte-payments` (verified verbatim). A grep over src/ for Agdelte.Storage/Agdelte.Payment finds only the comment at src/Agdelte/FFI/FileSystem.agda:63 plus unrelated localStorage hits — no real import in src/. The actual store consumers are 7 files under server/ (CrmServer.agda:13 `open import Agdelte.Storage.WAL`, plus StoreTxnTest/WalRecoveryTest/CrmStoreTest/CrmCommandsTest/IndexedMapTest/CoursesSmokeTest), and server/ is NOT in the lib's include. Build mechanism confirmed: package.json gen:crm-server runs `agda --compile ... -i src -i /home/n/.agda/agdelte-crm -i server server/CrmServer.agda` from cwd; with -i paths alone (run from /tmp) Agdelte.Storage.Txn fails FileNotFound (exit 42), but from cwd it typechecks (exit 0) — resolution relies on library registration + the cwd .agda-lib depend, exactly as claimed. CORRECTION/STRENGTHENING: the finding treats both deps as 'real deps the live server needs.' That holds for agdelte-store, but agdelte-payments is imported NOWHERE — grep for Agdelte.Payment/YooKassa over src/, server/, and agdelte-crm/ returns NONE. So agdelte-payments is an outright stale/unused dependency (could be deleted with zero effect), while agdelte-store is a real-but-wrong-layer dep (belongs to the server/app layer, also reachable transitively via agdelte-crm's own depend). Not a build breakage today; low severity is fair (latent layering inconsistency + one dead dep). Proposed fix is reasonable: either include server, or document that these deps serve the server/ app layer — and additionally drop agdelte-payments since nothing consumes it."
        }
      },
      {
        "title": "Stale doc comment in WAL.agda names moved-out callers (Payment, Auth)",
        "file": "~/.agda/agdelte-store/Agdelte/Storage/WAL.agda:167",
        "severity": "low",
        "evidence": "walStep/walModify carry the comment "Kept for existing callers (Payment, Auth)." Payment is now its own library (agdelte-payments) and Auth lives in the framework/courses; neither is a dependent of agdelte-store (store is stdlib-only and below them). The comment references consumers the store can no longer see, which is misleading for a domain-agnostic lib.",
        "fix": "Reword to a domain-neutral note, e.g. "single-op convenience wrappers kept for callers that don't need the txn error channel" — drop the Payment/Auth names.",
        "dimension": "store",
        "verdict": {
          "isReal": true,
          "confidence": "high",
          "severityAdjusted": "low",
          "note": "Confirmed the comment exists verbatim at ~/.agda/agdelte-store/Agdelte/Storage/WAL.agda:166-168 ("Kept for existing callers (Payment, Auth)."). agdelte-store.agda-lib depends only on standard-library and sits below all domains, so naming domain consumers in a domain-agnostic infra lib is a cosmetic doc smell — the reword is reasonable. HOWEVER the finding's evidence is factually WRONG about where those callers went. The Payment/Auth that actually call walStep/walModify are NOT agdelte-payments and NOT the framework: grep shows the only callers are in agdelte-courses (Agdelte/Payment.agda:142,189; Agdelte/Auth/Handler.agda:104; plus Storage/AppStore.agda:18). agdelte-payments/Agdelte/Payment/YooKassa.agda never calls these, and no src/Agdelte/Auth/* module imports Storage.WAL (verified: zero hits for Storage.WAL under agdelte/src). So the named callers still exist together in the (typecheck-only legacy) courses lib; they were not split apart as claimed. Net: a trivial cosmetic comment nit, no build/typecheck/behavioral impact. Severity stays low (borderline not-a-bug). Correct location is fine; correct the evidence: callers live in agdelte-courses, not agdelte-payments/framework."
        }
      },
      {
        "title": "FOREIGN block correctly consolidated import-first (GHC-ready); fixes original's interspersed-import MAlonzo stranding risk",
        "file": "/home/n/.agda/agdelte-payments/Agdelte/Payment/YooKassa.agda:36-161",
        "severity": "low",
        "evidence": "All 14 Haskell imports occupy lines 37-50 with the first definition (`type HttpManagerT`) only at line 52 — verified by an awk scan that found no `import` line after any `type`/`::` definition. The original split this across FOUR separate FOREIGN blocks (orig lines 49-58, 110-114, 143-211, 223-244, 255-271, 283-293) with `import qualified Data.Text as T` appearing twice and imports following definitions — exactly the layout that strands MAlonzo's auto `import Data.Text`. The consolidation is a genuine GHC-compile hardening, matching the comment at lines 31-34.",
        "fix": "None needed.",
        "dimension": "payments",
        "verdict": {
          "isReal": true,
          "confidence": "high",
          "severityAdjusted": "low",
          "note": "CONFIRMED against actual code. Current /home/n/.agda/agdelte-payments/Agdelte/Payment/YooKassa.agda has exactly ONE FOREIGN block (only one `FOREIGN GHC` at line 36); all 14 Haskell imports occupy lines 37-50 and the first definition `type HttpManagerT` is at line 52. An awk/grep scan found no `import` after any `type`/`::` definition. Original verified via git: pre-extraction src/Agdelte/Payment.agda (commit 5c5b359) had SIX FOREIGN blocks at lines 49, 110, 143, 223, 255, 283 — matching the evidence's line ranges. `import qualified Data.Text as T` appeared TWICE (lines 111 and 144), and block 6 (line 283) introduced imports (Crypto.MAC.HMAC, Crypto.Hash, Data.ByteArray) AFTER blocks 1-5 had already emitted definitions (newHttpManagerHS, createPaymentRawHS, getPaymentStatusRawHS, parseWebhookFieldsHS). Since MAlonzo concatenates FOREIGN blocks verbatim and GHC requires all imports before all top-level decls, that layout is the genuine stranding hazard the consolidation eliminates; the comment at lines 31-34 documents it accurately. The new file typechecks cleanly standalone (agda exit 0) and the .agda-lib depends only on standard-library, consistent with the stated independence. This is a correctly-verified POSITIVE observation (a real GHC-compile hardening), not a defect — no fix needed; severity 'low' is appropriate as informational."
        }
      },
      {
        "title": "INFORMATIONAL (not a payments-lib defect): nothing in the agdelte framework actually imports agdelte-payments, yet agdelte.agda-lib still depends on it",
        "file": "/home/n/.agda/agdelte/agdelte.agda-lib (depend lists agdelte-payments)",
        "severity": "low",
        "evidence": "`grep -rn 'Payment.YooKassa' src/` over the agdelte framework => NONE; the sole consumer of the YooKassa client is Agdelte.Payment in agdelte-courses (its imports at lines 43-48), which lives in a different library. So agdelte-payments has no importer inside the agdelte library that declares the dep. This is a stale-dep observation about agdelte.agda-lib (out of agdelte-payments' own scope), not a fault in the payments library itself, which is self-consistent. Flagging so the agdelte/courses agents can confirm whether `depend: agdelte-payments` should move from agdelte.agda-lib to agdelte-courses' (courses already declares it).",
        "fix": "In the agdelte/courses audit, consider dropping `agdelte-payments` from agdelte.agda-lib (it works only by registry/include-path accident if any src ever needed it; currently none does) since the real dependency edge is agdelte-courses -> agdelte-payments, which is already declared.",
        "dimension": "payments",
        "verdict": {
          "isReal": true,
          "confidence": "high",
          "severityAdjusted": "low",
          "note": "Confirmed at /home/n/.agda/agdelte/agdelte.agda-lib (lines 4-7): depend lists standard-library, agdelte-store, agdelte-payments. grep over /home/n/.agda/agdelte/src/ for 'Agdelte.Storage'/'Agdelte.Payment'/'YooKassa' returns NO actual imports — the only hit is a descriptive comment in src/Agdelte/FFI/FileSystem.agda:63 ('to the agdelte-store library...'), not an `open import`. So both agdelte-store AND agdelte-payments are declared-but-unused deps in agdelte.agda-lib (the finding focuses on agdelte-payments; agdelte-store is equally stale). The real consumer is agdelte-courses/Agdelte/Payment.agda:43 (`open import Agdelte.Payment.YooKassa using ...`), and /home/n/.agda/agdelte-courses.agda-lib already declares `agdelte-payments`, so the dependency edge courses->payments is already covered. The finding is correctly INFORMATIONAL, not a payments-lib defect: the payments library is self-consistent; this is a stale dep in agdelte.agda-lib. Severity low is right — an unused declared dep is harmless to builds (just removes an unnecessary edge); proposed fix (drop agdelte-payments, and arguably agdelte-store too, from agdelte.agda-lib) is reasonable cleanup. Location is accurate as stated."
        }
      },
      {
        "title": "agdelte.agda-lib declares agdelte-payments but the framework uses it nowhere (stale dependency)",
        "file": "/home/n/.agda/agdelte/agdelte.agda-lib (depend: agdelte-payments)",
        "severity": "medium",
        "evidence": "Repo-wide grep over all .agda in ~/.agda/agdelte for 'Agdelte.Payment' / 'YooKassa' returns ZERO matches in both src/ and server/. The only consumer of agdelte-payments is agdelte-courses (Agdelte/Payment.agda). After the courses domain left src/, the framework no longer references payments at all, yet agdelte.agda-lib still lists 'agdelte-payments' in depend. It is a stale dep that survived the decomposition.",
        "fix": "Remove 'agdelte-payments' from agdelte.agda-lib depend. (agdelte-courses keeps its own correct payments dep.)",
        "dimension": "crm",
        "verdict": {
          "isReal": true,
          "confidence": "high",
          "severityAdjusted": "low",
          "note": "Confirmed. /home/n/.agda/agdelte/agdelte.agda-lib lines 6-7 list `agdelte-store` and `agdelte-payments` in depend, with include: src. Grepped all 231 .agda files under src/ for `open import`: ZERO imports of `Agdelte.Payment.*`/`YooKassa` (payments lib) — the only `Payment` hit anywhere in the repo is a UI string literal "Payment" in examples/ControlsDemo.agda:800, and examples/ is not in the lib's `src` include anyway. The sole consumer of agdelte-payments is agdelte-courses (Agdelte/Payment.agda imports YooKassa, and courses' .agda-lib correctly lists agdelte-payments). So `agdelte-payments` in agdelte.agda-lib is a genuine stale dep; proposed fix (remove it) is safe — nothing in src resolves to it. Two caveats on framing: (1) By the identical analysis, `agdelte-store` is ALSO unused by src/ (no `open import Agdelte.Storage.*` anywhere in src; the only Storage hits are comments in src/Agdelte/FFI/FileSystem.agda lines 7/63). So the finding's implicit assumption that store stays needed is wrong — both deps are stale; a complete fix would drop both. (2) Severity: a stale `depend:` entry has no effect on typechecking or correctness (Agda ignores libs it never imports); impact is layering hygiene + forcing the framework to be unbuildable unless the unrelated payments lib is present. Real refactoring defect but no functional break, so low rather than medium."
        }
      },
      {
        "title": "Stale post-move path references to services-core/Crm/* in docs",
        "file": "/home/n/.agda/agdelte/docs/audit-2026-06-16.md:19,25,31,34 (and docs/SPEC.md §4)",
        "severity": "low",
        "evidence": "The CRM was moved from in-repo services-core/ to ~/.agda/agdelte-crm/ (services-core/ dir is GONE, confirmed). docs/audit-2026-06-16.md still cites 'services-core/Crm/Api.agda:181', ':144', ':84', ':70' as live locations; those files now live at /home/n/.agda/agdelte-crm/Crm/Api.agda. Anyone following the audit lines lands on a non-existent path.",
        "fix": "Update the audit/SPEC path references from services-core/Crm/* to the agdelte-crm library path (or a note that CRM was extracted).",
        "dimension": "crm",
        "verdict": {
          "isReal": true,
          "confidence": "high",
          "severityAdjusted": "low",
          "note": "CONFIRMED for the audit doc; SPEC §4 part is overstated. Verified: /home/n/.agda/agdelte/services-core/ does NOT exist; git shows it was removed in commit 377cb7f "Extract CRM into the standalone agdelte-crm library". The file now lives at /home/n/.agda/agdelte-crm/Crm/Api.agda (194 lines). docs/audit-2026-06-16.md cites services-core/Crm/Api.agda at exactly the claimed lines: line 19 -> ":181", line 25 -> ":144" (postAccount), line 31 -> ":84", line 34 -> ":70" (errJson). The string "services-core" appears 29 times in that audit (also Identity.agda:44, Commands.agda:132, Store.agda, etc.), all now dangling paths. Following any of these lands on a non-existent path -> the finding's failure mode is real. Note the audit file was committed (ca6808b) BEFORE the extraction (377cb7f), so it is a point-in-time snapshot whose paths rotted after the move; references are still phrased as live locations with no "extracted" marker. CORRECTION to the finding's scope: the "and docs/SPEC.md §4" claim is weak/not-a-defect. SPEC §4 (lines 82,86,91,98,102,114) uses "services-core" as the architectural LAYER NAME in the model app->packs->services-core->agdelte and the grep-guard convention — not stale file:line pointers into moved code. That layer naming is intentional and still used in CLAUDE.md; it is not path rot. So: real low-severity doc/traceability issue confined to docs/audit-2026-06-16.md (fix: add an "extracted to agdelte-crm" note or rewrite the services-core/Crm/* paths); the SPEC §4 portion should be dropped from the finding."
        }
      },
      {
        "title": "agdelte.agda-lib declares a stale dep on agdelte-payments (nothing in the agdelte repo imports Agdelte.Payment.*)",
        "file": "/home/n/.agda/agdelte/agdelte.agda-lib (depend: agdelte-payments)",
        "severity": "medium",
        "evidence": "grep across the ENTIRE agdelte repo (src/, server/, examples/, test/, app/, packs/) finds zero imports of Agdelte.Payment.* — the only payment client lives in agdelte-payments and is consumed exclusively by agdelte-courses, which left src/. The course domain was the only framework user of payments; after the move nothing in agdelte uses it. (Contrast: agdelte-store IS still load-bearing — server/CrmServer, StoreTxnTest, IndexedMapTest, WalRecoveryTest, CrmStoreTest, CrmCommandsTest all `open import Agdelte.Storage.*`, resolved through this dep, so agdelte-store must stay.)",
        "fix": "Remove `agdelte-payments` from the `depend:` of /home/n/.agda/agdelte/agdelte.agda-lib. Keep `agdelte-store` (used by the app layer in server/). Note the lib's own exported surface (include: src) uses NEITHER store nor payments — only the in-repo app layer server/ uses store; that's the sole justification for keeping agdelte-store.",
        "dimension": "integration",
        "verdict": {
          "isReal": true,
          "confidence": "high",
          "severityAdjusted": "low",
          "note": "Confirmed in actual config. /home/n/.agda/agdelte/agdelte.agda-lib line 7 declares `depend: agdelte-payments`. grep for "Agdelte.Payment" across all 284 .agda files in the repo (src/, server/, examples/, test/, app/, packs/) returns ZERO imports; the only "payment" hit is a UI label string in examples/ControlsDemo.agda:800 ('mkStep "Payment" ...'). agdelte-payments exports only Agdelte.Payment.YooKassa, which was consumed by agdelte-courses (now out of src/). Contrast claim verified: agdelte-store IS load-bearing — Agdelte.Storage.* is imported by server/CrmServer.agda, server/{IndexedMapTest,CrmStoreTest,StoreTxnTest,CoursesSmokeTest,WalRecoveryTest,CrmCommandsTest}.agda. The finding's nuance also checks out: the only src/ hit (src/Agdelte/FFI/FileSystem.agda) is a COMMENT, not an import, so the lib's exported surface (include: src) uses neither store nor payments; only the in-repo server/ app layer uses store. Proposed fix (remove agdelte-payments, keep agdelte-store) is correct. Severity lowered medium->low: it's a config-hygiene/layering-clarity defect (stale dep on the resolution path), not a build or runtime break — Agda tolerates an unused declared dep."
        }
      },
      {
        "title": "check-neutrality.sh guard 2 (CRM vertical-name guard) is now a permanent no-op after services-core/ moved to agdelte-crm",
        "file": "/home/n/.agda/agdelte/scripts/check-neutrality.sh:18-21",
        "severity": "medium",
        "evidence": "Guard 2 is gated on `[ -d services-core ]`. The CRM core (formerly in-repo services-core/, per CLAUDE.md/SPEC §4) was moved out to the separate agdelte-crm repo, so `services-core/` no longer exists in the agdelte repo (`test -d services-core` → ABSENT). The `&&` short-circuits and the psych|vet|transfer|медцентр vertical-name check never runs — `npm run check:neutrality` reports `✓ neutrality guards: OK` while checking nothing on the CRM side. The neutrality invariant the script exists to enforce is now silently unguarded.",
        "fix": "Point guard 2 at the moved location, e.g. grep over ~/.agda/agdelte-crm/Crm (or fail loudly if the dir is absent), or move check-neutrality.sh into the agdelte-crm repo. Guard 1 (domain words in src/ + hs/) is still valid and still fires.",
        "dimension": "integration",
        "verdict": {
          "isReal": true,
          "confidence": "high",
          "severityAdjusted": "low",
          "note": "Confirmed at /home/n/.agda/agdelte/scripts/check-neutrality.sh:18-21. Guard 2 is gated on `[ -d services-core ]`; `services-core/` is ABSENT from the repo (verified `test -d services-core` -> ABSENT). Git confirms the cause: commit 377cb7f "Extract CRM into the standalone agdelte-crm library" deleted services-core/{Crm/*,ServicesCore.agda,README.md} and moved it to /home/n/.agda/agdelte-crm/Crm. So the `&&` short-circuits and the psych|vet|transfer|медцентр vertical-name grep never runs. Ran `bash scripts/check-neutrality.sh` -> prints "✓ neutrality guards: OK", exit 0, while checking nothing on the CRM side. Guard 1 (src/ + hs/) is still valid: both dirs exist and the grep still executes. Proposed fix direction is sound (redirect guard 2 at ~/.agda/agdelte-crm/Crm, or fail loudly when absent, or relocate the script into agdelte-crm). Severity lowered medium->low: (1) the guarded code now lives in a separate repo the script cannot see anyway, and (2) check:neutrality is only a manual `npm run` target (package.json:92) — it is NOT wired into any CI workflow (no .github), prebuild, or precommit/husky hook, so the dead guard does not gate any automated process. Real dead-guard defect, but limited practical blast radius."
        }
      },
      {
        "title": "CLAUDE.md still documents the obsolete in-repo CRM layout (services-core/ packs/ app/ each with own .agda-lib) that no longer matches the decomposition",
        "file": "/home/n/.agda/agdelte/CLAUDE.md:7,29,34",
        "severity": "low",
        "evidence": "CLAUDE.md describes layers `app → packs → services-core → agdelte` and says 'CRM-специфика — в отдельных top-level каталогах services-core/, packs/, app/, каждый со своим .agda-lib' and the neutrality guard 'в services-core/ нет слов psych|vet…'. But services-core/ is gone (moved to ~/.agda/agdelte-crm), and app/ + packs/ now contain only README.md + .gitkeep + app/migrations/0001_identity.sql. A reader following CLAUDE.md will look for CRM code in services-core/ and the per-dir .agda-libs that don't exist. SPEC.md (6 hits) and docs/plan-crm-core.md (4 hits) carry the same stale services-core/ references.",
        "fix": "Update CLAUDE.md's layer-layout and neutrality sections to reflect the new registered-library decomposition (agdelte-crm holds Crm.*/ServicesCore; agdelte-store/agdelte-payments are separate libs). Note that the existing docs/audit-2026-06-16.md also still cites old `services-core/Crm/Api.agda` paths (historical snapshot — lower priority).",
        "dimension": "integration",
        "verdict": {
          "isReal": true,
          "confidence": "high",
          "severityAdjusted": "low",
          "note": "Confirmed all claims. /home/n/.agda/agdelte/CLAUDE.md:7 documents the layer chain `app → packs → services-core → agdelte`; line 29 says "CRM-специфика — в отдельных top-level каталогах services-core/, packs/, app/, каждый со своим .agda-lib"; line 34 is the neutrality guard "в services-core/ нет слов psych|vet|transfer|медцентр…". These no longer match reality: services-core/ does not exist in cwd (git commit 377cb7f "Extract CRM into the standalone agdelte-crm library" moved it). CRM now lives in ~/.agda/agdelte-crm as a single registered lib (agdelte-crm.agda-lib, name: agdelte-crm) holding ServicesCore.agda + Crm/. The per-dir .agda-libs CLAUDE.md describes don't exist — cwd has only the top-level agdelte.agda-lib. packs/ contains only README.md; app/ contains README.md + migrations/0001_identity.sql + .gitkeep — no Agda code. Stale services-core references also confirmed in docs/SPEC.md (6 hits) and docs/plan-crm-core.md (4 hits). Real doc-drift/orientation defect, not a build/correctness issue, so low severity stands. Proposed fix is correct."
        }
      },
      {
        "title": "Namespace fragility (not a current break): agdelte-courses defines parent module Agdelte.Payment while agdelte-payments defines its child Agdelte.Payment.YooKassa",
        "file": "/home/n/.agda/agdelte-courses/Agdelte/Payment.agda:15 (module Agdelte.Payment) vs /home/n/.agda/agdelte-payments/Agdelte/Payment/YooKassa.agda",
        "severity": "low",
        "evidence": "Two registered libs both on the path when building courses contribute modules under the SAME Agdelte.Payment.* prefix from DIFFERENT repos: courses owns `Agdelte.Payment` (a parent), payments owns `Agdelte.Payment.YooKassa` (its child). Agda permits this (a parent module need not contain its children; verified — all 8 course modules typecheck standalone, EXIT=0). But it is an unusual split: Agdelte/Payment.agda (courses) `open import Agdelte.Payment.YooKassa` (payments) — a module importing a submodule of its own qualified name from another library. If agdelte-payments ever adds an actual `Agdelte/Payment.agda` (e.g. a provider-neutral facade, foreshadowed in its .agda-lib comment 'a future provider-neutral interface can join here'), that becomes a TRUE full-name collision with the courses module and both libs fail to coexist on the path.",
        "fix": "No action needed now (typechecks today). To de-risk, either rename the courses module out of the shared parent slot (e.g. Agdelte.Courses.Payment) or reserve `Agdelte.Payment` (the bare name) for payments and never add a bare Agdelte/Payment.agda to agdelte-payments. Worth a one-line note so the future facade isn't named into a collision.",
        "dimension": "integration",
        "verdict": {
          "isReal": true,
          "confidence": "high",
          "severityAdjusted": "low",
          "note": "Confirmed all factual claims. /home/n/.agda/agdelte-courses/Agdelte/Payment.agda:15 declares `module Agdelte.Payment`; line 43 does `open import Agdelte.Payment.YooKassa` from the separate agdelte-payments lib. agdelte-payments defines `module Agdelte.Payment.YooKassa` (line 15) and has NO bare Agdelte/Payment.agda — verified by `ls`. Both libs registered in ~/.agda/libraries; courses depends on agdelte-payments (its .agda-lib). courses Payment.agda typechecks standalone EXIT=0 (only a deprecation warning from AppStore). The agdelte-payments .agda-lib comment indeed says \"a future provider-neutral interface can join here\", corroborating the latent-collision scenario. NOT a current defect: there is no duplicate full module name on the path today, so no collision exists. It is only a conditional/latent hazard if payments later adds a bare Agdelte/Payment.agda. This is also explicitly within the KNOWN-INTENTIONAL design (Agdelte.* prefix shared across libs, partitioned by submodule). Severity low is correct as a forward-looking note; the proposed fix (a one-line reservation note) is reasonable and low-cost, but no action is required now. Defensible as low rather than not-a-bug because the cross-lib parent/child split is genuinely a real future-maintenance footgun, but it is not a bug in current code."
        }
      }
    ]
  }
}
