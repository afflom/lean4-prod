import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';

const module = new WebAssembly.Module(readFileSync(process.argv[2]));
assert.deepEqual(WebAssembly.Module.imports(module), []);
function invoke(input) {
  const {exports} = new WebAssembly.Instance(module, {});
  const pointer = exports.holo_alloc(input.length);
  new Uint8Array(exports.memory.buffer, pointer, input.length).set(input);
  const packed = BigInt.asUintN(64, exports.holo_run(pointer, input.length));
  const start = Number(packed >> 32n), length = Number(packed & 0xffffffffn);
  assert.equal(length, 3);
  assert.ok(start + length <= exports.memory.buffer.byteLength);
  assert.ok(exports.memory.buffer.byteLength <= 4 * 65536);
  return [...new Uint8Array(exports.memory.buffer, start, length)];
}
for (let length = 0; length <= 128; length++) {
  for (const byte of [0, 1, 127, 255]) {
    assert.deepEqual(invoke(new Uint8Array(length).fill(byte)), length === 3 ? [1, 3, 5] : [2, 4, 6]);
  }
}
assert.throws(() => invoke(new Uint8Array(129)), WebAssembly.RuntimeError);
console.log('PASS 516 actual import-free Wasm cases; shared branches, record fields and allocation bound');
