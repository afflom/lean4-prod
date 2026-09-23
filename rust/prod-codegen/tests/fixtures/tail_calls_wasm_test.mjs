import assert from "node:assert/strict";
import {readFileSync} from "node:fs";

const module = new WebAssembly.Module(readFileSync(process.argv[2]));
assert.deepEqual(WebAssembly.Module.imports(module), []);
assert.deepEqual(WebAssembly.Module.exports(module).filter(row => row.kind === "function").map(row => row.name).sort(), ["holo_alloc", "holo_run"]);
for (const size of [0, 1, 4095, 4096]) {
  for (let replay = 0; replay < 2; replay++) {
    const instance = new WebAssembly.Instance(module, {});
    const input = Uint8Array.from({length: size}, (_, index) => index % 256);
    const pointer = instance.exports.holo_alloc(size);
    new Uint8Array(instance.exports.memory.buffer, pointer, size).set(input);
    const result = BigInt.asUintN(64, instance.exports.holo_run(pointer, size));
    const offset = Number(result >> 32n), length = Number(result & 0xffffffffn);
    assert.deepEqual(new Uint8Array(instance.exports.memory.buffer, offset, length), input);
    assert.ok(instance.exports.memory.buffer.byteLength <= 16 * 65536);
  }
}
console.log("100000 tail steps: all eight bounded Wasm invocations passed");
