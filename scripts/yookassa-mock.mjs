#!/usr/bin/env node
// Мок ЮKassa API для сетевого смоука клиента (аналог stripe-mock, но
// узкоспециализированный: только то, что дергает Agdelte.Payment.YooKassa).
//
// Запускается тест-раннером (npm run test:yk-mock), порт — MOCK_PORT.
// YOOKASSA_API_BASE клиента указывает на этот сервер.
//
// ЧТО ПРОВЕРЯЕТ МОК (конформанс запроса по спеке):
// * POST /v3/payments: Basic-Auth, заголовок Idempotency-Key, JSON-тело,
//   amount.value = "R.KK" (ровно две цифры после точки),
//   amount.currency ∈ {RUB, EUR, USD, KZT, BYN, UAH, UZS, TRY, INR, MDL, AZN, AMD};
//   если description начинается с "EXPECTCUR=<CODE>" — тело ОБЯЗАНО нести
//   именно эту валюту (пин на баг «клиент всегда шлёт RUB»).
// * Описания "EMPTY_URL" → ответ с ПУСТЫМ confirmation_url (класс бага
//   «тихий pending с пустым url», пойманный у Stripe на stripe-mock).
// * Идемпотентность: повтор с тем же Idempotency-Key → ТОТ ЖЕ платёж.
// * GET /v3/payments/{id} → {id, status: "succeeded"}.

import { createServer } from "node:http";

const port = Number(process.env.MOCK_PORT || 9099);
const CURRENCIES = new Set([
  "RUB", "EUR", "USD", "KZT", "BYN", "UAH", "UZS", "TRY", "INR", "MDL", "AZN", "AMD",
]);

let seq = 0;
const idem = new Map(); // Idempotency-Key → JSON ответа

function bad(res, status, description) {
  res.writeHead(status, { "Content-Type": "application/json" });
  res.end(JSON.stringify({ description, type: "invalid_request" }));
}

const server = createServer((req, res) => {
  let chunks = [];
  req.on("data", (ch) => chunks.push(ch));
  req.on("end", () => {
    const body = Buffer.concat(chunks).toString("utf8");

    // Basic-Auth: shopId:key (проверяем форму заголовка, не значения)
    const auth = req.headers["authorization"] || "";
    if (!auth.startsWith("Basic ")) return bad(res, 401, "no basic auth");

    const m = req.url.match(/^\/v3\/payments\/([^/]+)$/);
    if (req.method === "GET" && m) {
      res.writeHead(200, { "Content-Type": "application/json" });
      return res.end(JSON.stringify({ id: m[1], status: "succeeded" }));
    }

    if (req.method === "POST" && req.url === "/v3/payments") {
      const idemKey = req.headers["idempotency-key"];
      if (!idemKey) return bad(res, 400, "missing Idempotency-Key");
      if (idem.has(idemKey)) {
        res.writeHead(200, { "Content-Type": "application/json" });
        return res.end(idem.get(idemKey));
      }

      let j;
      try { j = JSON.parse(body); } catch { return bad(res, 400, "bad json"); }

      const v = j.amount && j.amount.value;
      if (typeof v !== "string" || !/^\d+\.\d\d$/.test(v))
        return bad(res, 400, `bad amount.value: ${JSON.stringify(v)}`);
      const cur = j.amount && j.amount.currency;
      if (!CURRENCIES.has(cur)) return bad(res, 400, `bad currency: ${JSON.stringify(cur)}`);

      const desc = typeof j.description === "string" ? j.description : "";
      if (desc.startsWith("EXPECTCUR=")) {
        const expect = desc.slice("EXPECTCUR=".length);
        if (cur !== expect)
          return bad(res, 400, `currency mismatch: sent ${cur}, expected ${expect}`);
      }

      const id = `mock-${++seq}-${idemKey.slice(0, 12)}`;
      const confirmationUrl = desc === "EMPTY_URL" ? "" : `https://mock.yk/pay/${id}`;
      const response = JSON.stringify({
        id,
        status: "pending",
        amount: j.amount,
        confirmation: { type: "redirect", confirmation_url: confirmationUrl },
      });
      idem.set(idemKey, response);
      res.writeHead(200, { "Content-Type": "application/json" });
      return res.end(response);
    }

    bad(res, 404, "unknown endpoint");
  });
});

server.listen(port, "127.0.0.1", () =>
  console.log(`yookassa-mock listening on http://127.0.0.1:${port}`),
);
