'use strict';
const assert = require('node:assert/strict');
const path = require('node:path');
const root = process.argv[2];
const echo = require(path.join(root, 'invoke/adapter.js')).invoke_bytes;
const invalid = require(path.join(root, 'invalid/adapter.js')).invoke_bytes;
const oversized = require(path.join(root, 'oversized/adapter.js')).invoke_bytes;
const encode = value => new TextEncoder().encode(value);
for (const text of ['', 'a'.repeat(32), '😀'.repeat(8), '\ufeffhello\0\t\n', '<script>bad</script>']) {
  const bytes = encode(text);
  const before = bytes.slice();
  assert.deepEqual(echo(bytes), bytes);
  assert.deepEqual(bytes, before);
}
for (const input of [null, 'text', [], new Uint16Array(1), encode('a'.repeat(33)),
  Uint8Array.of(0xff), Uint8Array.of(0xc0, 0x80), Uint8Array.of(0xed, 0xa0, 0x80),
  Uint8Array.of(0xf4, 0x90, 0x80, 0x80), Uint8Array.of(0xe2, 0x82)]) {
  assert.throws(() => echo(input));
}
assert.throws(() => invalid(encode('valid request')), /invalid output UTF-8/);
assert.deepEqual(oversized(encode('x'.repeat(16))), encode('x'.repeat(32)));
assert.throws(() => oversized(encode('x'.repeat(17))), /output byte limit/);
console.log('Actual generated Wasm: exact bytes, cap boundaries, invalid UTF-8, and unchanged inputs passed');
