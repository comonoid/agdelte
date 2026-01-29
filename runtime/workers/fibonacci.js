// Fibonacci Worker — heavy computation offloaded from main thread
// Receives a number N, computes fib(N), sends back the result

function fib(n) {
  if (n <= 1) return n;
  let a = 0, b = 1;
  for (let i = 2; i <= n; i++) {
    [a, b] = [b, a + b];
  }
  return b;
}

self.onmessage = (e) => {
  const n = parseInt(e.data, 10);
  if (isNaN(n) || n < 0) {
    self.postMessage("Error: invalid input");
    return;
  }
  const result = fib(n);
  self.postMessage(String(result));
};
