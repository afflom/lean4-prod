import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
const module=new WebAssembly.Module(readFileSync(process.argv[2]));
assert.deepEqual(WebAssembly.Module.imports(module),[]);
assert.deepEqual(WebAssembly.Module.exports(module).filter(row=>row.kind==='function').map(row=>row.name).sort(),['holo_alloc','holo_run']);
function invoke(input){
  const {exports}=new WebAssembly.Instance(module,{});
  const pointer=exports.holo_alloc(input.length);
  new Uint8Array(exports.memory.buffer,pointer,input.length).set(input);
  const packed=BigInt.asUintN(64,exports.holo_run(pointer,input.length));
  const offset=Number(packed>>32n),length=Number(packed&0xffffffffn);
  assert.equal(length,1);assert.ok(exports.memory.buffer.byteLength<=4*65536);
  return new Uint8Array(exports.memory.buffer,offset,length)[0];
}
const encode=text=>new TextEncoder().encode(text);
const rows=[['',0],['a',0],['é',0],['e\u0301',1],['🇺🇸',1],['👩‍💻',0],['水a',1],['\r\n',1],['\0',0],['\ufeff',0],['\u{10ffff}a',1]];
for(const codepoint of [0,1,0x7f,0x80,0x7ff,0x800,0xd7ff,0xe000,0xffff,0x10000,0x10ffff]){
  rows.push([String.fromCodePoint(codepoint),0],[String.fromCodePoint(codepoint)+'a',1]);
}
for(let codepoint=0;codepoint<=0x10ffff;codepoint+=997){
  if(codepoint>=0xd800&&codepoint<=0xdfff)continue;
  rows.push([String.fromCodePoint(codepoint)+'a',1]);
}
for(const [text,expected] of rows)assert.equal(invoke(encode(text)),expected);
for(const bytes of [[0xff],[0xc0,0xaf],[0xed,0xa0,0x80],[0xf4,0x90,0x80,0x80]])assert.equal(invoke(Uint8Array.from(bytes)),255);
assert.equal(invoke(encode('é'.repeat(128))),0);
assert.throws(()=>invoke(new Uint8Array(257)),WebAssembly.RuntimeError);
console.log(`PASS ${rows.length} scalar-count cases, invalid UTF-8 and bounded memory in actual Wasm`);
