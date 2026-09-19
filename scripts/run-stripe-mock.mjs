#!/usr/bin/env node
// Раннер сетевого смоука Stripe: поднимает stripe-mock (.tmp-stripe-mock),
// собирает (если нужно) и запускает бинарь stripe-net-test с
// STRIPE_API_BASE, указывающим на мок. Гасит мок в любом исходе.
//
//   node scripts/run-stripe-mock.mjs
//   npm run test:stripe-mock

import { spawn, spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const mockBin = join(root, "..", ".tmp-stripe-mock", "stripe-mock");
const port = Number(process.env.STRIPE_MOCK_PORT || 12111);

// Agda-стадия (генерация + компиляция MAlonzo), как в test:stripe
const gen = spawnSync(
  "npm",
  ["run", "-s", "gen:stripe-net-test"],
  { cwd: root, stdio: "inherit" },
);
if (gen.status !== 0) process.exit(gen.status ?? 1);

const mock = spawn(mockBin, ["-port", String(port)], {
  stdio: ["ignore", "pipe", "inherit"],
});
mock.stdout.on("data", () => {});

function killMock() {
  try { mock.kill(); } catch { /* уже мёртв */ }
}
process.on("exit", killMock);
process.on("SIGINT", () => { killMock(); process.exit(130); });

const deadline = Date.now() + 10_000;
async function waitReady() {
  while (Date.now() < deadline) {
    const probe = spawnSync("node", [
      "-e",
      `require("node:http").get("http://127.0.0.1:${port}/", r => process.exit(0)).on("error", () => process.exit(1));`,
    ]);
    if (probe.status === 0) return;
    await new Promise((r) => setTimeout(r, 150));
  }
  console.error("stripe-mock did not start (есть ли " + mockBin + "?)");
  process.exit(1);
}

try {
  await waitReady();
  const run = spawnSync(
    "cabal",
    ["run", "-v0", "stripe-net-test"],
    {
      cwd: root,
      stdio: "inherit",
      env: { ...process.env, STRIPE_API_BASE: `http://127.0.0.1:${port}` },
    },
  );
  process.exitCode = run.status ?? 1;
} finally {
  killMock();
}
