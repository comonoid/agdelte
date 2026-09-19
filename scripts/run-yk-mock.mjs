#!/usr/bin/env node
// Раннер сетевого смоука ЮKassa: поднимает мок (scripts/yookassa-mock.mjs),
// собирает (если нужно) и запускает бинарь yookassa-net-test с
// YOOKASSA_API_BASE, указывающим на мок. Гасит мок в любом исходе.
//
//   node scripts/run-yk-mock.cjs
//   npm run test:yk-mock

import { spawn, spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const port = Number(process.env.MOCK_PORT || 9099);

// Agda-стадия (генерация + компиляция MAlonzo), как в test:yookassa
const gen = spawnSync(
  "npm",
  ["run", "-s", "gen:yookassa-net-test"],
  { cwd: root, stdio: "inherit" },
);
if (gen.status !== 0) process.exit(gen.status ?? 1);

const mock = spawn("node", [join(root, "scripts", "yookassa-mock.mjs")], {
  env: { ...process.env, MOCK_PORT: String(port) },
  stdio: ["ignore", "pipe", "inherit"],
});
mock.stdout.on("data", () => {}); // молча: «listening» не шумим в вывод тестов

function killMock() {
  try { mock.kill(); } catch { /* уже мёртв */ }
}
process.on("exit", killMock);
process.on("SIGINT", () => { killMock(); process.exit(130); });

// ждём, пока мок начнёт принимать соединения
const deadline = Date.now() + 10_000;
async function waitReady() {
  while (Date.now() < deadline) {
    const probe = spawnSync("node", [
      "-e",
      `require("node:http").get("http://127.0.0.1:${port}/v3/payments/x", r => process.exit(0)).on("error", () => process.exit(1));`,
    ]);
    if (probe.status === 0) return;
    await new Promise((r) => setTimeout(r, 150));
  }
  console.error("mock did not start");
  process.exit(1);
}

try {
  await waitReady();
  const run = spawnSync(
    "cabal",
    ["run", "-v0", "yookassa-net-test"],
    {
      cwd: root,
      stdio: "inherit",
      env: { ...process.env, YOOKASSA_API_BASE: `http://127.0.0.1:${port}` },
    },
  );
  process.exitCode = run.status ?? 1;
} finally {
  killMock();
}
