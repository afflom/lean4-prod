// Compiler transport probe over the generated fixture's actual Wasm.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createServer} from 'node:http';
import {createRequire} from 'node:module';
import {join} from 'node:path';

const require = createRequire('/opt/lean4-prod/browser-tests/package.json');
assert.equal(require('playwright/package.json').version, '1.62.1');
const {chromium} = require('playwright');
const root = process.argv[2];
assert.ok(root);
const types = {html: 'text/html', css: 'text/css', js: 'text/javascript', wasm: 'application/wasm'};
const server = createServer((request, response) => {
  const name = request.url === '/' ? 'index.html' : request.url.slice(1);
  if (request.method !== 'GET' || !['index.html', 'app.css', 'app.js',
    'fixture_core.js', 'fixture_core_bg.wasm'].includes(name)) return response.writeHead(404).end();
  // No host CSP: the generated artifact must prevent native form submission.
  response.writeHead(200, {'content-type': types[name.split('.').at(-1)], 'cache-control': 'no-store'});
  response.end(readFileSync(join(root, name)));
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const origin = `http://127.0.0.1:${server.address().port}`;
const browser = await chromium.launch({headless: true});
assert.equal(browser.browserType().name(), 'chromium');
assert.equal(browser.version(), '151.0.7922.34');
let passed = 0;
const failures = [];
const inputError = 'Enter a signed 64-bit integer.';
async function check(name, work) {
  try { await work(); passed++; console.log(`PASS ${name}`); }
  catch (error) { failures.push(name); console.error(`FAIL ${name}: ${error.stack}`); }
}
async function setup(options = {}) {
  const context = await browser.newContext({javaScriptEnabled: options.javascript !== false});
  const page = await context.newPage();
  page.setDefaultTimeout(5000);
  const requests = [], errors = [];
  page.on('request', request => requests.push(request.url()));
  page.on('pageerror', error => errors.push(error.message));
  if (options.block) await page.route(`**/${options.block}`, route => route.abort());
  return {context, page, requests, errors};
}
async function result(page, expected) {
  await page.waitForFunction(value => document.querySelector('#result').textContent === value, expected);
}
async function fill(page, left = '49721', right = '7') {
  await page.locator('#left').fill(left);
  await page.locator('#right').fill(right);
}
function noNavigation(state, count) {
  assert.equal(state.page.url(), `${origin}/`);
  assert.equal(state.requests.length, count, 'numeric inputs must not enter native requests');
}
try {
  for (const options of [{javascript: false}, {block: 'app.js'},
    {block: 'fixture_core.js'}, {block: 'fixture_core_bg.wasm'}]) {
    await check(`initialization failure ${JSON.stringify(options)}`, async () => {
      const state = await setup(options);
      try {
        await state.page.goto(`${origin}/`);
        await state.page.waitForLoadState('networkidle');
        const count = state.requests.length;
        await fill(state.page);
        if (await state.page.locator('#submit').isEnabled()) await state.page.locator('#submit').click();
        noNavigation(state, count);
        await state.page.locator('#right').press('Enter');
        await state.page.waitForTimeout(100);
        noNavigation(state, count);
        await result(state.page, inputError);
        assert.equal(await state.page.locator('#left').inputValue(), '49721');
        assert.deepEqual(state.errors, []);
        if (!options.block || options.block === 'app.js') {
          assert.equal(await state.page.locator('#submit').isDisabled(), true);
        }
      } finally { await state.context.close(); }
    });
  }
  await check('artifact CSP independently blocks bypassed native form submission', async () => {
    const state = await setup({block: 'app.js'});
    try {
      await state.page.goto(`${origin}/`);
      await state.page.waitForLoadState('networkidle');
      await fill(state.page);
      const count = state.requests.length;
      const policy = await state.page.evaluate(() => new Promise((resolve, reject) => {
        const listener = event => {
          clearTimeout(timeout);
          resolve(event.violatedDirective);
        };
        const timeout = setTimeout(() => {
          document.removeEventListener('securitypolicyviolation', listener);
          reject(new Error('native submission did not produce a CSP violation'));
        }, 3000);
        document.addEventListener('securitypolicyviolation', listener, {once: true});
        document.getElementById('left').name = 'left';
        HTMLFormElement.prototype.submit.call(document.getElementById('application-form'));
      }));
      assert.equal(policy, 'form-action');
      noNavigation(state, count);
    } finally { await state.context.close(); }
  });
  for (const asset of ['app.js', 'fixture_core_bg.wasm']) {
    await check(`delayed ${asset} preserves input and never submits natively`, async () => {
      const state = await setup();
      let release;
      const waiting = new Promise(resolve => {release = resolve;});
      await state.page.route(`**/${asset}`, async route => {await waiting; await route.continue();});
      try {
        await state.page.goto(`${origin}/`, {waitUntil: 'commit'});
        await fill(state.page);
        if (asset === 'app.js') assert.equal(await state.page.locator('#submit').isDisabled(), true);
        else {
          await state.page.waitForFunction(() => !document.querySelector('#submit').disabled);
          await state.page.locator('#submit').click();
          assert.equal(await state.page.locator('#submit').isDisabled(), true);
        }
        assert.equal(state.page.url(), `${origin}/`);
        assert.ok(state.requests.every(value => !new URL(value).search));
        release();
        await state.page.waitForLoadState('networkidle');
        if (asset === 'app.js') await state.page.locator('#submit').click();
        await result(state.page, '49721');
        assert.equal(await state.page.locator('#left').inputValue(), '49721');
        assert.equal(await state.page.locator('#submit').isEnabled(), true);
        assert.deepEqual(state.errors, []);
      } finally { release(); await state.context.close(); }
    });
  }
  await check('actual fixture Wasm, integer validation and keyboard recovery stay local', async () => {
    const state = await setup();
    try {
      await state.page.goto(`${origin}/`);
      await state.page.waitForLoadState('networkidle');
      await result(state.page, '');
      const count = state.requests.length;
      await state.context.setOffline(true);
      for (const operation of ['0', '1', '2', '3']) {
        await fill(state.page, '-9223372036854775808', '9223372036854775807');
        await state.page.locator('#operation').selectOption(operation);
        await state.page.locator('#right').press('Enter');
        // The IR transport fixture intentionally returns its left argument.
        await result(state.page, '-9223372036854775808');
      }
      for (const value of ['', '+1', '-0', '9223372036854775808']) {
        await fill(state.page, value);
        await state.page.locator('#submit').click();
        await result(state.page, inputError);
      }
      await fill(state.page, '12');
      await state.page.locator('#right').press('Enter');
      await result(state.page, '12');
      noNavigation(state, count);
      assert.deepEqual(state.errors, []);
    } finally { await state.context.close(); }
  });
} finally { await browser.close(); await new Promise(resolve => server.close(resolve)); }
assert.equal(passed, 8, `browser failures: ${failures.join(', ')}`);
assert.deepEqual(failures, []);
