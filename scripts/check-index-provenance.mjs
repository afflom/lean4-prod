import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {lstatSync,readFileSync,readdirSync} from 'node:fs';
import {dirname,join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';

const root=resolve(dirname(fileURLToPath(import.meta.url)),'..');
const fixture=join(root,'fixtures/lexlean-index');
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
const read=path=>{assert.ok(lstatSync(path).isFile());return readFileSync(path);};
const safe=path=>{
  assert.equal(typeof path,'string');
  assert.ok(path.split('/').every(part=>/^[A-Za-z0-9_.-]+$/.test(part)&&!['.','..'].includes(part)));
  return path;
};
const receipt=JSON.parse(read(join(fixture,'fixture-manifest.json')));
assert.equal(receipt.spec,'lean4-prod/lexlean-index-fixture/1');
assert.equal(receipt.compiler_revision,'9c1456d34b896ab77db01c5e8ebbfed584edee26');
assert.equal(receipt.compiler_crate_sha256,'94ee7d58bcbcc70dbb5b01fb4130e4f24f3fed314b3c63b2c252c431e53c2efb');
const raw=read(join(fixture,'build/manifest.json'));
assert.equal(hash(raw),receipt.build_manifest_sha256);
const manifest=JSON.parse(raw);
assert.equal(manifest.spec,'lexlean/build-manifest/1');
assert.equal(manifest.language,'1.1');
assert.equal(manifest.compiler.version,'0.3.0');
assert.equal(manifest.compiler.semantics_id,receipt.compiler_semantics_id);
for(const key of ['build_id','semantic_id','source_id'])assert.equal(manifest[key],receipt[key]);
assert.deepEqual(manifest.selection,['Bytes','Main']);
assert.deepEqual(manifest.modules,['Bytes','Main'].map(name=>({lean_module:`IndexFixture.${name}`,module:name,source_path:`src/${name}.lex.tex`})));
const inputs=manifest.inputs.filter(row=>row.kind!=='lexicon');
assert.deepEqual(inputs.map(row=>row.path).sort(),['lexlean.lock','lexlean.toml','src/Bytes.lex.tex','src/Main.lex.tex']);
for(const row of inputs){
  const bytes=read(join(fixture,safe(row.path)));
  assert.equal(bytes.length,row.byte_length);assert.equal(hash(bytes),row.sha256);
}
const lock=read(join(fixture,'lexlean.lock')).toString('utf8');
assert.equal(/^compiler_semantics = "([0-9a-f]{64})"$/m.exec(lock)?.[1],receipt.compiler_semantics_id);
const workspace=[...lock.matchAll(/\[\[workspace_file\]\]\npath = "([^"]+)"\nsha256 = "([0-9a-f]{64})"/g)];
assert.deepEqual(workspace.map(row=>row[1]).sort(),['lake-manifest.json','lakefile.toml','lean-toolchain']);
for(const row of workspace)assert.equal(hash(read(join(fixture,safe(row[1])))),row[2]);
assert.equal(manifest.outputs.length,10);
assert.equal(new Set(manifest.outputs.map(row=>row.path)).size,10);
for(const row of manifest.outputs){
  const bytes=read(join(fixture,'build',safe(row.path)));
  assert.equal(bytes.length,row.byte_length);assert.equal(hash(bytes),row.sha256);
}
const files=directory=>readdirSync(directory,{withFileTypes:true}).flatMap(row=>{
  const path=join(directory,row.name);assert.ok(row.isDirectory()||row.isFile());
  return row.isDirectory()?files(path):[path.slice(join(fixture,'build').length+1)];
}).sort();
assert.deepEqual(files(join(fixture,'build')),['manifest.json',...manifest.outputs.map(row=>row.path)].sort());
assert.deepEqual(receipt.generated.map(row=>row.path),['lean/IndexFixture/Bytes.lean','lean/IndexFixture/Main.lean']);
for(const row of receipt.generated){
  const generated=read(join(root,safe(row.path)));
  assert.equal(hash(generated),row.sha256);
  assert.deepEqual(generated,read(join(fixture,'build',safe(row.source))));
  assert.ok(!/\b(?:sorry|admit|axiom|opaque)\b/.test(generated.toString('utf8')));
}
console.log('Index fixture: exact source, compiler, workspace and complete generated output binding passed');
