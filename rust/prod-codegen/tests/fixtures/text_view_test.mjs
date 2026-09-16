// Execute the exact generated modules against controlled DOM/transport ports.
// This is deterministic DOM-contract evidence, not a layout/browser engine test.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import vm from 'node:vm';
import {createHash} from 'node:crypto';

const root = process.argv[2];
const bytes = value => new TextEncoder().encode(value);
const hash = value => createHash('sha256').update(value).digest('hex');
const read = file => fs.readFileSync(path.join(root, file));
const keys = (object, expected) => assert.deepEqual(Object.keys(object).sort(), expected.sort());
const manifest = JSON.parse(read('view-manifest.json'));
keys(manifest, ['browser_adapter', 'generated_core_sha256', 'hologram_bundle', 'max_input_bytes',
  'max_output_bytes', 'model_id', 'profile', 'projections', 'schema', 'view_model_id']);
assert.equal(manifest.profile, 'prism.text-view/1');
assert.equal(manifest.schema, 'lean4-prod/text-view-projection/1');
function verifyRecords(records, directory, expected) {
  assert.deepEqual(records.map(record => record.path), expected);
  for (const record of records) {
    keys(record, ['path', 'sha256']);
    assert.equal(record.sha256, hash(read(`${directory}/${record.path}`)));
  }
}
for (const [index, target] of ['browser', 'hologram'].entries()) {
  const projection = manifest.projections[index];
  keys(projection, ['files', 'target']);
  assert.equal(projection.target, index ? 'hologram-intent-v1' : 'browser-wasm-bindgen');
  verifyRecords(projection.files, target, ['app.css', 'app.js', 'index.html']);
  const html = read(`${target}/index.html`).toString();
  assert.ok(html.includes('Text &lt;request&gt;'));
  assert.ok(html.includes('Request &amp; response'));
  for (const required of ['<label for="request">Request</label>', 'type="submit"',
    'aria-live="polite"', 'aria-atomic="true"', 'aria-labelledby="response-label"',
    '<label id="response-label" for="result">Response</label>']) assert.ok(html.includes(required));
  assert.ok(!/\son\w+=/i.test(html));
  assert.equal((html.match(/<script/g) ?? []).length, 1);
  assert.ok(html.includes('<script type="module" src="app.js"></script>'));
  assert.ok(!/innerHTML|outerHTML|document\.write|\beval\(/.test(read(`${target}/app.js`).toString()));
}
verifyRecords(manifest.browser_adapter, 'adapter', ['Cargo.toml', 'generation-manifest.json', 'src/lib.rs']);
const adapter = JSON.parse(read('adapter/generation-manifest.json'));
keys(adapter, ['core_crate', 'core_function', 'core_version', 'files', 'generated_core_sha256',
  'max_input_bytes', 'max_output_bytes', 'model_id', 'profile', 'schema', 'view_model_id']);
assert.equal(adapter.schema, 'lean4-prod/text-browser-adapter/1');
verifyRecords(adapter.files, 'adapter', ['Cargo.toml', 'src/lib.rs']);
for (const field of ['generated_core_sha256', 'max_input_bytes', 'max_output_bytes', 'model_id', 'profile', 'view_model_id']) {
  assert.deepEqual(adapter[field], manifest[field]);
}
const bundle = read('hologram/view.holoview');
assert.equal(hash(bundle), manifest.hologram_bundle.sha256);
assert.equal(bundle.subarray(0, 8).toString(), 'HOLOVIEW');
assert.equal(bundle.readUInt16BE(8), 1);
let offset = 10;
const u32 = () => { const value = bundle.readUInt32BE(offset); offset += 4; return value; };
const string = () => { const length = u32(); const value = bundle.subarray(offset, offset + length).toString(); offset += length; return value; };
assert.equal(string(), 'index.html');
assert.equal(u32(), 3);
for (const name of ['app.css', 'app.js', 'index.html']) {
  assert.equal(string(), name);
  const length = Number(bundle.readBigUInt64BE(offset)); offset += 8;
  assert.deepEqual(bundle.subarray(offset, offset + length), read(`hologram/${name}`));
  offset += length;
}
assert.equal(offset, bundle.length);

class Element {
  handlers = new Map(); attributes = new Map(); value = ''; textContent = ''; disabled = false; focused = false;
  addEventListener(name, handler) { this.handlers.set(name, handler); }
  setAttribute(name, value) { this.attributes.set(name, value); }
  removeAttribute(name) { this.attributes.delete(name); }
  focus() { this.focused = true; }
  requestSubmit() { this.pending = this.handlers.get('submit')({preventDefault() {}}); }
}
async function setup(target, options = {}) {
  const elements = Object.fromEntries(['application-form', 'request', 'submit', 'result'].map(id => [id, new Element()]));
  const state = {calls: [], encodes: 0, mode: options.mode ?? 'echo', options, elements};
  class Encoder { encode(value) { state.encodes++; return bytes(value); } }
  const invoke = input => {
    state.calls.push(input);
    if (state.mode === 'throw') throw new Error('core failure');
    if (typeof state.mode === 'function') return state.mode(input);
    return input;
  };
  const fetch = async (url, init) => {
    assert.equal(url, '/_hologram/intent'); assert.equal(init.method, 'POST');
    const envelope = JSON.parse(init.body);
    keys(envelope, ['version', 'name', 'payload']);
    assert.equal(envelope.version, 1); assert.equal(envelope.name, 'application.invoke');
    state.calls.push(envelope.payload);
    if (state.mode === 'throw') throw new Error('transport');
    if (typeof state.mode === 'function') return state.mode(envelope.payload);
    return new Response(JSON.stringify({version: 1, outputs: [envelope.payload]}));
  };
  const context = vm.createContext({document: {getElementById: id => elements[id]},
    TextEncoder: Encoder, TextDecoder, Uint8Array, fetch, console});
  const module = new vm.SourceTextModule(read(`${target}/app.js`).toString(), {context});
  await module.link(specifier => {
    assert.equal(specifier, './text_view_core.js');
    return new vm.SyntheticModule(['default', 'invoke_bytes'], function () {
      this.setExport('default', options.init ?? (async () => {}));
      this.setExport('invoke_bytes', invoke);
    }, {context});
  });
  await module.evaluate();
  const form = elements['application-form'];
  state.submit = async value => {
    elements.request.value = value;
    let prevented = false;
    await form.handlers.get('submit')({preventDefault() { prevented = true; }});
    assert.ok(prevented);
  };
  state.key = async event => {
    let prevented = false;
    elements.request.handlers.get('keydown')({...event, preventDefault() { prevented = true; }});
    await form.pending;
    return prevented;
  };
  return state;
}

for (const target of ['browser', 'hologram']) {
  const state = await setup(target);
  const {request, result, submit, 'application-form': form} = state.elements;
  for (const value of ['', 'hello\t\n', '😀'.repeat(8), 'é'.repeat(16), 'a'.repeat(32), '\ufeffhello\0', '<img src=x onerror=bad>']) {
    await state.submit(value);
    assert.equal(result.textContent, value);
    const actual = state.calls.at(-1);
    assert.deepEqual(actual, target === 'browser' ? bytes(value) : value);
    assert.ok(!request.focused); assert.ok(!submit.disabled); assert.ok(!form.attributes.has('aria-busy'));
  }
  for (const value of ['a'.repeat(33), '😀'.repeat(9), 'é'.repeat(17), '\ud800', '\udfff', '\ud800x']) {
    const count = state.calls.length, encodes = state.encodes;
    await state.submit(value);
    assert.equal(result.textContent, 'Invalid input');
    assert.equal(request.attributes.get('aria-invalid'), 'true'); assert.ok(request.focused);
    assert.equal(state.calls.length, count); assert.equal(state.encodes, encodes);
  }
  await state.submit('recovered'); assert.ok(!request.attributes.has('aria-invalid'));
  request.value = 'keyboard';
  let count = state.calls.length;
  assert.equal(await state.key({key: 'Enter'}), false); assert.equal(state.calls.length, count);
  assert.equal(await state.key({key: 'Enter', ctrlKey: true, isComposing: true}), false);
  assert.equal(state.calls.length, count);
  assert.equal(await state.key({key: 'Enter', ctrlKey: true}), true); assert.equal(state.calls.length, ++count);
  assert.equal(await state.key({key: 'Enter', metaKey: true}), true); assert.equal(state.calls.length, ++count);
  state.mode = 'throw'; await state.submit('request');
  assert.equal(result.textContent, 'Invalid response'); assert.ok(!submit.disabled);
  state.mode = target === 'browser' ? () => bytes('x'.repeat(33)) : () => new Response(JSON.stringify({version: 1, outputs: ['x'.repeat(33)]}));
  await state.submit('request'); assert.equal(result.textContent, 'Invalid response');
}

const browser = await setup('browser');
for (const answer of [null, 'not bytes', Uint8Array.of(0xff), Uint8Array.of(0xc0, 0x80), Uint8Array.of(0xe2, 0x82)]) {
  browser.mode = () => answer; await browser.submit('input');
  assert.equal(browser.elements.result.textContent, 'Invalid response');
}
const failedInit = await setup('browser', {init: async () => { throw new Error('init failed'); }});
await failedInit.submit('input'); assert.equal(failedInit.calls.length, 0);
assert.equal(failedInit.elements.result.textContent, 'Invalid response');
let release;
const waiting = await setup('browser', {init: () => new Promise(resolve => { release = resolve; })});
const first = waiting.submit('first');
await waiting.submit('second'); assert.equal(waiting.calls.length, 0);
release(); await first; assert.equal(waiting.calls.length, 1);
assert.deepEqual(waiting.calls[0], bytes('first'));

const hologram = await setup('hologram');
for (const body of ['null', '{}', '{"version":2,"outputs":["x"]}', '{"version":1,"outputs":[]}',
  '{"version":1,"outputs":["a","b"]}', '{"version":1,"outputs":[2]}', '{"version":1,"outputs":["\\ud800"]}']) {
  hologram.mode = () => new Response(body); await hologram.submit('input');
  assert.equal(hologram.elements.result.textContent, 'Invalid response');
}
for (const response of [new Response('bad', {status: 500}), new Response(Uint8Array.of(0xff)),
  new Response(Uint8Array.of(0xe2, 0x82)), new Response(' '.repeat(449))]) {
  hologram.mode = () => response; await hologram.submit('input');
  assert.equal(hologram.elements.result.textContent, 'Invalid response');
}
let cancelled = false;
hologram.mode = () => ({ok: true, headers: new Headers({'content-length': '449'}),
  body: {cancel: async () => { cancelled = true; }, getReader() { assert.fail('oversized declared body was read'); }}});
await hologram.submit('input'); assert.ok(cancelled);
console.log('Text View DOM contracts: manifest/HOLOVIEW closure, both transports, keyboard, focus, safe text and UTF-8/error boundaries passed');
