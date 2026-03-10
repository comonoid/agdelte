#!/usr/bin/env node
const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

const PORT = parseInt(process.env.PORT, 10) || 8080;
const ROOT = __dirname;

const MAX_WS_FRAME_SIZE = 16 * 1024 * 1024; // 16 MB

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.json': 'application/json',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.svg': 'image/svg+xml',
  '.ico': 'image/x-icon',
  '.wasm': 'application/wasm',
  '.woff2': 'font/woff2',
  '.woff': 'font/woff',
  '.ttf': 'font/ttf',
  '.otf': 'font/otf',
  '.webp': 'image/webp',
  '.avif': 'image/avif',
  '.gif': 'image/gif',
  '.mp4': 'video/mp4',
  '.webm': 'video/webm',
  '.map': 'application/json',
};

const server = http.createServer((req, res) => {
  const parsed = new URL(req.url, `http://localhost:${PORT}`);
  let pathname;
  try { pathname = decodeURIComponent(parsed.pathname); }
  catch { res.writeHead(400); return res.end('Bad Request'); }

  // /api/random-delay?name=X — respond after random 500-2500ms delay
  if (pathname === '/api/random-delay') {
    const name = parsed.searchParams.get('name') || 'unknown';
    const delay = 500 + Math.floor(Math.random() * 2000);
    setTimeout(() => {
      res.writeHead(200, {
        'Content-Type': 'text/plain',
        'Cross-Origin-Opener-Policy': 'same-origin',
        'Cross-Origin-Embedder-Policy': 'require-corp'
      });
      res.end(`${name} (${delay}ms)`);
    }, delay);
    return;
  }

  const filePath = path.join(ROOT, pathname === '/' ? 'index.html' : pathname);

  // Security check: use ROOT + path.sep to prevent sibling directory traversal
  if (!filePath.startsWith(ROOT + path.sep) && filePath !== ROOT) {
    res.writeHead(403);
    return res.end('Forbidden');
  }

  // Resolve symlinks and re-check to prevent symlink escape
  fs.realpath(filePath, (rpErr, realPath) => {
    if (rpErr) {
      // If realpath fails, fall through to readFile which will report the actual error
    } else if (!realPath.startsWith(ROOT + path.sep) && realPath !== ROOT) {
      res.writeHead(403);
      return res.end('Forbidden');
    }

    fs.readFile(filePath, (err, data) => {
      if (err) {
        const notFound = err.code === 'ENOENT' || err.code === 'EISDIR';
        res.writeHead(notFound ? 404 : 500, {
          'Content-Type': 'text/plain',
          'Cross-Origin-Opener-Policy': 'same-origin',
          'Cross-Origin-Embedder-Policy': 'require-corp'
        });
        return res.end(notFound ? '404: Not Found' : `Error: ${err.code}`);
      }
      const ext = path.extname(filePath).toLowerCase();
      res.writeHead(200, {
        'Content-Type': MIME[ext] || 'application/octet-stream',
        'Cache-Control': 'no-store, no-cache, must-revalidate',
        'Pragma': 'no-cache',
        'Expires': '0',
        'Cross-Origin-Opener-Policy': 'same-origin',
        'Cross-Origin-Embedder-Policy': 'require-corp'
      });
      res.end(data);
    });
  }); // fs.realpath
});

// ----------------------------------------------------------------
// Minimal WebSocket echo server (no dependencies)
// Handles /echo path for the WebSocket demo
// ----------------------------------------------------------------

function wsAccept(key) {
  return crypto.createHash('sha1')
    .update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11')
    .digest('base64');
}

function wsEncodeFrame(data) {
  const buf = Buffer.from(data, 'utf8');
  const len = buf.length;
  let header;
  if (len < 126) {
    header = Buffer.alloc(2);
    header[0] = 0x81; // FIN + text
    header[1] = len;
  } else if (len < 65536) {
    header = Buffer.alloc(4);
    header[0] = 0x81;
    header[1] = 126;
    header.writeUInt16BE(len, 2);
  } else {
    header = Buffer.alloc(10);
    header[0] = 0x81;
    header[1] = 127;
    header.writeBigUInt64BE(BigInt(len), 2);
  }
  return Buffer.concat([header, buf]);
}

server.on('upgrade', (req, socket, head) => {
  const pathname = new URL(req.url, `http://localhost:${PORT}`).pathname;
  if (pathname !== '/echo') {
    socket.destroy();
    return;
  }

  const key = req.headers['sec-websocket-key'];
  if (!key) { socket.destroy(); return; }

  socket.setNoDelay(true);
  socket.write(
    'HTTP/1.1 101 Switching Protocols\r\n' +
    'Upgrade: websocket\r\n' +
    'Connection: Upgrade\r\n' +
    'Sec-WebSocket-Accept: ' + wsAccept(key) + '\r\n' +
    '\r\n'
  );

  console.log('  WS: client connected');

  let buf = head.length > 0 ? Buffer.from(head) : Buffer.alloc(0);

  socket.on('data', (chunk) => {
    buf = Buffer.concat([buf, chunk]);

    // Reject accumulated buffer exceeding max frame size (prevents unbounded growth)
    if (buf.length > MAX_WS_FRAME_SIZE) {
      console.log('  WS: buffer too large, closing with 1009');
      const closeFrame = Buffer.alloc(4);
      closeFrame[0] = 0x88; // FIN + close
      closeFrame[1] = 0x02; // payload length = 2
      closeFrame.writeUInt16BE(1009, 2); // 1009 = message too big
      socket.write(closeFrame);
      socket.end();
      return;
    }

    while (buf.length >= 2) {
      const opcode = buf[0] & 0x0f;
      const masked = !!(buf[1] & 0x80);
      let payloadLen = buf[1] & 0x7f;
      let offset = 2;

      if (payloadLen === 126) {
        if (buf.length < 4) return;
        payloadLen = buf.readUInt16BE(2);
        offset = 4;
      } else if (payloadLen === 127) {
        if (buf.length < 10) return;
        payloadLen = Number(buf.readBigUInt64BE(2));
        offset = 10;
      }

      // Reject frames exceeding max size to prevent unbounded allocation
      if (payloadLen > MAX_WS_FRAME_SIZE) {
        console.log('  WS: frame too large, closing with 1009');
        const closeFrame = Buffer.alloc(4);
        closeFrame[0] = 0x88;
        closeFrame[1] = 0x02;
        closeFrame.writeUInt16BE(1009, 2);
        socket.write(closeFrame);
        socket.end();
        return;
      }

      const maskSize = masked ? 4 : 0;
      const totalLen = offset + maskSize + payloadLen;
      if (buf.length < totalLen) return;

      // Copy payload to avoid mutating the shared buffer during XOR unmasking
      let payload = Buffer.from(buf.slice(offset + maskSize, totalLen));
      if (masked) {
        const mask = buf.slice(offset, offset + 4);
        for (let i = 0; i < payload.length; i++) {
          payload[i] ^= mask[i % 4];
        }
      }

      buf = buf.slice(totalLen);

      if (opcode === 0x08) {
        // Close frame — echo it back and close
        const closeFrame = Buffer.alloc(2);
        closeFrame[0] = 0x88;
        closeFrame[1] = 0x00;
        socket.write(closeFrame);
        socket.end();
        return;
      }

      if (opcode === 0x09) {
        // Ping — reply pong with same payload (RFC 6455 §5.5.3)
        const pLen = payload.length;
        let pongHeader;
        if (pLen < 126) {
          pongHeader = Buffer.alloc(2);
          pongHeader[0] = 0x8A; // FIN + pong
          pongHeader[1] = pLen;
        } else if (pLen < 65536) {
          pongHeader = Buffer.alloc(4);
          pongHeader[0] = 0x8A;
          pongHeader[1] = 126;
          pongHeader.writeUInt16BE(pLen, 2);
        } else {
          pongHeader = Buffer.alloc(10);
          pongHeader[0] = 0x8A;
          pongHeader[1] = 127;
          pongHeader.writeBigUInt64BE(BigInt(pLen), 2);
        }
        socket.write(Buffer.concat([pongHeader, payload]));
        continue;
      }

      if (opcode === 0x01) {
        // Text frame — echo back
        const text = payload.toString('utf8');
        console.log('  WS echo:', text);
        socket.write(wsEncodeFrame(text));
      }
    }
  });

  socket.on('error', (e) => { console.log('  WS error:', e.message); });
  socket.on('close', () => { console.log('  WS: client disconnected'); });
});

server.listen(PORT, () => {
  console.log(`\n  → http://localhost:${PORT}`);
  console.log(`  → ws://localhost:${PORT}/echo (WebSocket echo)\n`);
});
