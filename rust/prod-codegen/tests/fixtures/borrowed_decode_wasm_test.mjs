import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

const module = new WebAssembly.Module(readFileSync(process.argv[2]));
assert.deepEqual(WebAssembly.Module.imports(module), []);
const maximumPages = Number(process.argv[3]);
assert.equal(maximumPages, 16);
const encoder = new TextEncoder();
const decoder = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true });
let cases = 0;
function check(input) {
  let expected;
  try { decoder.decode(input); expected = input; } catch { expected = Uint8Array.of(255); }
  const { exports } = new WebAssembly.Instance(module, {});
  const pointer = exports.holo_alloc(input.length);
  new Uint8Array(exports.memory.buffer, pointer, input.length).set(input);
  const packed = BigInt.asUintN(64, exports.holo_run(pointer, input.length));
  const start = Number(packed >> 32n);
  const length = Number(packed & 0xffffffffn);
  assert.ok(start + length <= exports.memory.buffer.byteLength);
  assert.ok(exports.memory.buffer.byteLength <= maximumPages * 65536);
  assert.deepEqual(new Uint8Array(exports.memory.buffer, start, length), expected);
  cases++;
}
for (const text of ['', '\0', 'ASCII', 'é', 'e\u0301', '日本語', '🦀', '\ufeff', '👩‍💻']) check(encoder.encode(text));
for (let first = 0; first < 256; first++) {
  check(Uint8Array.of(first));
  for (let second = 0; second < 256; second++) check(Uint8Array.of(first, second));
}
for (const input of [[0xed, 0xa0, 0x80], [0xe0, 0x9f, 0xbf], [0xf4, 0x90, 0x80, 0x80], [0xf0, 0x80, 0x80, 0x80], [0xe2, 0x82], [0xf0, 0x9f, 0xa6]]) check(Uint8Array.from(input));
for (const size of [4095, 4096]) check(new Uint8Array(size).fill(97));
const { exports } = new WebAssembly.Instance(module, {});
assert.throws(() => exports.holo_alloc(4097), WebAssembly.RuntimeError);
console.log(`PASS ${cases} actual import-free UTF-8 decoding cases and allocation rejection`);
