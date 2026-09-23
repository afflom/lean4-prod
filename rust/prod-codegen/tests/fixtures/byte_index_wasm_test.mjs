import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';

const module=new WebAssembly.Module(readFileSync(process.argv[2]));
const slice=process.argv[3]==='sliceEntry';
assert.ok(slice||process.argv[3]==='entry');
assert.deepEqual(WebAssembly.Module.imports(module),[]);
assert.deepEqual(WebAssembly.Module.exports(module).filter(row=>row.kind==='function').map(row=>row.name).sort(),['holo_alloc','holo_run']);
function invoke(input){
  const {exports}=new WebAssembly.Instance(module,{});
  const pointer=exports.holo_alloc(input.length);
  new Uint8Array(exports.memory.buffer,pointer,input.length).set(input);
  const packed=BigInt.asUintN(64,exports.holo_run(pointer,input.length));
  const offset=Number(packed>>32n),length=Number(packed&0xffffffffn);
  assert.ok(length===(slice&&input.length>=3?2:1));
  assert.ok(exports.memory.buffer.byteLength<=4*65536);
  return [...new Uint8Array(exports.memory.buffer,offset,length)];
}
let passed=0;
for(const size of [0,1,2,3,4,16,63,64]){
  for(let octet=0;octet<=255;octet++){
    const input=Uint8Array.from({length:size},(_,position)=>(octet+position)%256);
    const expected=slice?(size<3?[255]:[...input.subarray(1,3)]):[size<4?255:input[3]===128?1:0];
    assert.deepEqual(invoke(input),expected);
    passed++;
  }
}
assert.throws(()=>invoke(new Uint8Array(65)),WebAssembly.RuntimeError);
console.log(`PASS ${passed} actual import-free Wasm ${slice?'slice':'index'} cases and allocation rejection`);
