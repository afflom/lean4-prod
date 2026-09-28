import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';

const module = new WebAssembly.Module(readFileSync(process.argv[2]));
assert.deepEqual(WebAssembly.Module.imports(module), []);
const maximum = 67108864, chunkSize = 262144;
let memoryPeak = 0, cases = 0;
const run = input => {
  const instance = new WebAssembly.Instance(module, {}), exports = instance.exports;
  const at = exports.holo_alloc(input.length) >>> 0;
  new Uint8Array(exports.memory.buffer, at, input.length).set(input);
  let result;
  try { result = BigInt.asUintN(64, exports.holo_run(at, input.length)); }
  catch (cause) {
    throw new Error('generated owned-accumulator trap: input=' + input.length
      + ' memory=' + exports.memory.buffer.byteLength, {cause});
  }
  const offset = Number(result >> 32n), length = Number(result & 0xffffffffn);
  assert.ok(length <= maximum && offset + length <= exports.memory.buffer.byteLength);
  memoryPeak = Math.max(memoryPeak, exports.memory.buffer.byteLength);
  assert.ok(memoryPeak <= 1073741824);
  cases++;
  return Buffer.from(new Uint8Array(exports.memory.buffer, offset, length));
};
for (const count of [0, 1, 2, 3, 16, 256]) {
  const input = Buffer.alloc(count * chunkSize);
  for (let index = 0; index < count; index++) {
    input.fill(index, index * chunkSize, (index + 1) * chunkSize);
    input[index * chunkSize] = index ^ 0x55;
  }
  const expected = Buffer.concat(Array.from({length: count}, (_, index) =>
    input.subarray((count - index - 1) * chunkSize, (count - index) * chunkSize)));
  for (let repeat = 0; repeat < 2; repeat++) assert.deepEqual(run(input), expected);
}
for (const size of [1, 255, chunkSize - 1, chunkSize + 1, maximum - 1]) {
  for (let repeat = 0; repeat < 2; repeat++) assert.deepEqual(run(Buffer.alloc(size)), Buffer.from([255]));
}
const refused = new WebAssembly.Instance(module, {});
assert.throws(() => refused.exports.holo_alloc(maximum + 1), WebAssembly.RuntimeError);
const initialPages = refused.exports.memory.buffer.byteLength / 65536;
assert.equal(refused.exports.memory.grow(16384 - initialPages), initialPages);
assert.equal(refused.exports.memory.buffer.byteLength, 1073741824);
assert.throws(() => refused.exports.memory.grow(1), RangeError);
assert.equal(cases, 22);
console.log(JSON.stringify({cases, memoryPeak, maximum, maximumPages: 16384}));
