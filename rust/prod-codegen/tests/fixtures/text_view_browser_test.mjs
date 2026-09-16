// Real Chromium over exact generated HTML/JavaScript and compiled Wasm.
// Fixture functions are compiler transport probes, not application fallbacks.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createServer} from 'node:http';
import {createRequire} from 'node:module';
import {join} from 'node:path';

const require = createRequire('/opt/lean4-prod/browser-tests/package.json');
const {chromium} = require('playwright');
const root = process.argv[2];
assert.ok(root, 'generated fixture directory is required');
const requests = [];
const media = new Map([['html', 'text/html'], ['css', 'text/css'],
  ['js', 'text/javascript'], ['wasm', 'application/wasm']]);
const server = createServer((request, response) => {
  requests.push({url: request.url, method: request.method});
  const url = new URL(request.url, 'http://127.0.0.1');
  const match = /^\/(invoke|invalid|oversized)\/(index.html|app.css|app.js|text_view_core.js|text_view_core_bg.wasm)?$/.exec(url.pathname);
  if (request.method !== 'GET' || !match) return response.writeHead(404).end();
  const name = match[2] || 'index.html';
  response.writeHead(200, {'content-type': media.get(name.split('.').at(-1)), 'cache-control': 'no-store'});
  response.end(readFileSync(join(root, match[1], 'browser', name)));
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const origin = `http://127.0.0.1:${server.address().port}`;
const browser = await chromium.launch({headless: true});
let passed = 0;
const failures = [];
async function test(name, run) {
  try { await run(); passed++; console.log(`PASS ${name}`); }
  catch (error) { failures.push(name); console.error(`FAIL ${name}: ${error.stack}`); }
}
async function setup(options = {}) {
  const context = await browser.newContext({javaScriptEnabled: options.javascript !== false});
  const page = await context.newPage();
  const traffic = [], navigations = [], errors = [];
  page.on('request', request => traffic.push({url: request.url(), method: request.method(), data: request.postData()}));
  page.on('framenavigated', frame => { if (frame === page.mainFrame()) navigations.push(frame.url()); });
  page.on('pageerror', error => errors.push(error.message));
  if (options.block) await page.route(`**/${options.block}`, route => route.abort());
  return {context, page, traffic, navigations, errors};
}
function noLeak(state, before, secret) {
  assert.equal(state.page.url(), before.url, 'native form navigation must be impossible');
  assert.deepEqual(state.navigations, before.navigations, 'no navigation after draft input');
  assert.ok(!state.traffic.some(item => decodeURIComponent(item.url).includes(secret) || item.data?.includes(secret)),
    `draft leaked in browser request: ${JSON.stringify(state.traffic)}`);
  assert.ok(!requests.some(item => decodeURIComponent(item.url).includes(secret)), 'draft reached server');
}
const input = page => page.locator('#request');
const output = page => page.locator('#result');
const button = page => page.locator('#submit');
const snapshot = state => ({url: state.page.url(), navigations: [...state.navigations], requests: state.traffic.length});
async function eventually(check) {
  const deadline = Date.now() + 5000;
  for (;;) {
    try { await check(); return; }
    catch (error) { if (Date.now() >= deadline) throw error; }
    await new Promise(resolve => setTimeout(resolve, 20));
  }
}
async function result(page, expected) {
  await eventually(async () => assert.equal(await output(page).textContent(), expected));
}
try {
  for (const options of [{javascript: false}, {block: 'app.js'}, {block: 'text_view_core.js'}]) {
    await test(`fail closed: ${JSON.stringify(options)}`, async () => {
      const state = await setup(options);
      try {
        await state.page.goto(`${origin}/invoke/`);
        await state.page.waitForLoadState('networkidle');
        const before = snapshot(state), secret = 'private-draft-49821';
        await input(state.page).fill(secret);
        // Click only if enabled: the original renderer takes the real unsafe
        // submission path here, rather than merely failing an attribute check.
        if (await button(state.page).isEnabled()) await button(state.page).click();
        await input(state.page).press('Control+Enter');
        await state.page.waitForTimeout(100);
        noLeak(state, before, secret);
        assert.equal(state.traffic.length, before.requests, 'failed bootstrap cannot send draft requests');
        assert.equal(await input(state.page).inputValue(), secret);
        await result(state.page, 'Invalid response');
        if (options.block === 'text_view_core.js') assert.deepEqual(state.errors, [], 'binding import failure must be handled');
        else assert.equal(await button(state.page).isDisabled(), true);
      } finally { await state.context.close(); }
    });
  }
  await test('CSP independently blocks native submission even if button state is changed', async () => {
    const state = await setup({block: 'app.js'});
    try {
      await state.page.goto(`${origin}/invoke/`);
      await state.page.waitForLoadState('networkidle');
      const before = snapshot(state), secret = 'private-native-bypass';
      await input(state.page).fill(secret);
      await state.page.evaluate(() => {
        // Deliberately bypass disabled state and event handlers. This mutation
        // proves HTML policy independently prevents the native form fallback.
        document.getElementById('request').name = 'request';
        HTMLFormElement.prototype.submit.call(document.getElementById('application-form'));
      });
      await state.page.waitForTimeout(100);
      noLeak(state, before, secret);
      assert.equal(state.traffic.length, before.requests);
    } finally { await state.context.close(); }
  });
  await test('input before app module initialization is retained and cannot submit natively', async () => {
    const state = await setup();
    let release;
    const delayed = new Promise(resolve => { release = resolve; });
    await state.page.route('**/app.js', async route => { await delayed; await route.continue(); });
    try {
      await state.page.goto(`${origin}/invoke/`, {waitUntil: 'commit'});
      await input(state.page).waitFor();
      const before = snapshot(state), secret = 'private-before-init';
      await input(state.page).fill(secret);
      assert.equal(await button(state.page).isDisabled(), true);
      await input(state.page).press('Control+Enter');
      noLeak(state, before, secret);
      release();
      await eventually(async () => assert.equal(await button(state.page).isEnabled(), true));
      await button(state.page).click();
      await result(state.page, secret);
      noLeak(state, before, secret);
      assert.equal(await input(state.page).inputValue(), secret);
      assert.deepEqual(state.errors, []);
    } finally { release(); await state.context.close(); }
  });
  await test('actual Wasm success, keyboard, invalid input and recovery remain local', async () => {
    const state = await setup();
    try {
      await state.page.goto(`${origin}/invoke/`);
      await state.page.waitForLoadState('networkidle');
      const before = snapshot(state);
      for (const text of ['private-success', '<script>bad</script>', '\ufeffdata', '🌱'.repeat(8)]) {
        await input(state.page).fill(text);
        await input(state.page).press('Control+Enter');
        await result(state.page, text);
        assert.equal(await output(state.page).locator('script').count(), 0);
        noLeak(state, before, text);
      }
      for (const value of ['x'.repeat(33), '\ud800']) {
        await input(state.page).evaluate((element, text) => { element.value = text; }, value);
        await button(state.page).click();
        await result(state.page, 'Invalid input');
        assert.equal(await input(state.page).getAttribute('aria-invalid'), 'true');
        assert.equal(await input(state.page).evaluate(element => element === document.activeElement), true);
      }
      await input(state.page).fill('recovered');
      await input(state.page).press('Tab');
      await state.page.keyboard.press('Enter');
      await result(state.page, 'recovered');
      assert.equal(await input(state.page).getAttribute('aria-invalid'), null);
      assert.equal(await button(state.page).isEnabled(), true);
      assert.equal(state.traffic.length, before.requests);
      assert.deepEqual(state.errors, []);
    } finally { await state.context.close(); }
  });
  await test('delayed Wasm initialization preserves validation and submitted input', async () => {
    const state = await setup();
    let release;
    const delayed = new Promise(resolve => { release = resolve; });
    await state.page.route('**/text_view_core_bg.wasm', async route => { await delayed; await route.continue(); });
    try {
      await state.page.goto(`${origin}/invoke/`, {waitUntil: 'domcontentloaded'});
      await eventually(async () => assert.equal(await button(state.page).isEnabled(), true));
      const before = snapshot(state), secret = 'private-during-wasm';
      await input(state.page).fill('x'.repeat(33));
      await button(state.page).click();
      await result(state.page, 'Invalid input');
      release();
      await state.page.waitForLoadState('networkidle');
      await result(state.page, 'Invalid input');
      await input(state.page).fill(secret);
      await button(state.page).click();
      await result(state.page, secret);
      noLeak(state, before, secret);
      assert.deepEqual(state.errors, []);
    } finally { release(); await state.context.close(); }
  });
  await test('submit while Wasm is pending stays local and preserves input', async () => {
    const state = await setup();
    let release;
    const delayed = new Promise(resolve => { release = resolve; });
    await state.page.route('**/text_view_core_bg.wasm', async route => { await delayed; await route.continue(); });
    try {
      await state.page.goto(`${origin}/invoke/`, {waitUntil: 'domcontentloaded'});
      await eventually(async () => assert.equal(await button(state.page).isEnabled(), true));
      const before = snapshot(state), secret = 'private-pending-submit';
      await input(state.page).fill(secret);
      await button(state.page).click();
      assert.equal(await button(state.page).isDisabled(), true);
      assert.equal(await state.page.locator('#application-form').getAttribute('aria-busy'), 'true');
      await input(state.page).press('Control+Enter');
      noLeak(state, before, secret);
      release();
      await result(state.page, secret);
      assert.equal(await button(state.page).isEnabled(), true);
      assert.equal(await input(state.page).inputValue(), secret);
      noLeak(state, before, secret);
      assert.deepEqual(state.errors, []);
    } finally { release(); await state.context.close(); }
  });
  for (const entry of ['invalid', 'oversized']) {
    await test(`actual Wasm ${entry} response fails visibly without draft loss`, async () => {
      const state = await setup();
      try {
        await state.page.goto(`${origin}/${entry}/`);
        await state.page.waitForLoadState('networkidle');
        const before = snapshot(state), secret = 'private-response-error';
        await input(state.page).fill(secret);
        await button(state.page).click();
        await result(state.page, 'Invalid response');
        assert.equal(await button(state.page).isEnabled(), true);
        assert.equal(await input(state.page).inputValue(), secret);
        noLeak(state, before, secret);
        assert.equal(state.traffic.length, before.requests);
        assert.deepEqual(state.errors, []);
      } finally { await state.context.close(); }
    });
  }
  await test('Wasm initialization failure is handled and input remains local', async () => {
    const state = await setup({block: 'text_view_core_bg.wasm'});
    try {
      await state.page.goto(`${origin}/invoke/`);
      await state.page.waitForLoadState('networkidle');
      const before = snapshot(state), secret = 'private-wasm-error';
      await input(state.page).fill(secret);
      await button(state.page).click();
      await result(state.page, 'Invalid response');
      assert.equal(await input(state.page).inputValue(), secret);
      assert.equal(await button(state.page).isEnabled(), true);
      noLeak(state, before, secret);
      assert.equal(state.traffic.length, before.requests);
      assert.deepEqual(state.errors, []);
    } finally { await state.context.close(); }
  });
} finally {
  await browser.close();
  await new Promise(resolve => server.close(resolve));
}
console.log(`Text View real Chromium: ${passed} passed, ${failures.length} failed`);
assert.deepEqual(failures, [], 'every browser transport security case must pass');
