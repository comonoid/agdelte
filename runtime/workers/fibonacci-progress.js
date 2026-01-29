// Fibonacci Worker with progress reporting
// Receives a number N, reports progress, computes fib(N), sends result
//
// Protocol:
//   { type: 'progress', value: '25' }    — progress percentage (string)
//   { type: 'done', result: '6765' }     — final result (string)
//   { type: 'error', message: '...' }    — error (string)

// Deliberately slow recursive fib to demonstrate progress
function fibSlow(n, reportProgress) {
  if (n <= 1) return BigInt(n);

  // For large N, compute iteratively but report progress
  let a = 0n, b = 1n;
  for (let i = 2; i <= n; i++) {
    [a, b] = [b, a + b];
    // Report progress every 10% or every 1000 steps
    if (n >= 10 && i % Math.max(1, Math.floor(n / 10)) === 0) {
      const pct = Math.floor((i / n) * 100);
      reportProgress(String(pct));
    }
  }
  return b;
}

self.onmessage = (e) => {
  const n = parseInt(e.data, 10);
  if (isNaN(n) || n < 0) {
    self.postMessage({ type: 'error', message: 'Invalid input: ' + e.data });
    return;
  }

  try {
    const result = fibSlow(n, (pct) => {
      self.postMessage({ type: 'progress', value: pct });
    });
    self.postMessage({ type: 'done', result: String(result) });
  } catch (err) {
    self.postMessage({ type: 'error', message: err.message });
  }
};
