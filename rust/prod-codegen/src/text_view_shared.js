const form = document.getElementById('application-form');
const request = document.getElementById('request');
const submit = document.getElementById('submit');
const result = document.getElementById('result');
const encoder = new TextEncoder();
// Preserve a leading U+FEFF: it is application data, not a transport BOM.
const decoder = new TextDecoder('utf-8', {fatal: true, ignoreBOM: true});
let busy = false;
let displayed = false;

// Validate before TextEncoder allocates; never replace malformed UTF-16.
function boundedText(value, limit) {
  if (typeof value !== 'string' || value.length > limit) return false;
  let bytes = 0;
  for (let index = 0; index < value.length; index++) {
    const unit = value.charCodeAt(index);
    if (unit >= 0xd800 && unit <= 0xdbff) {
      if (++index >= value.length) return false;
      const low = value.charCodeAt(index);
      if (low < 0xdc00 || low > 0xdfff) return false;
      bytes += 4;
    } else if (unit >= 0xdc00 && unit <= 0xdfff) {
      return false;
    } else {
      bytes += unit < 0x80 ? 1 : unit < 0x800 ? 2 : 3;
    }
    if (bytes > limit) return false;
  }
  return true;
}

function show(value) { displayed = true; result.textContent = value; }
// A delayed initialization must not erase a validation error already shown.
function clearInitialStatus() { if (!displayed) result.textContent = ''; }

function attach(invoke) {
  // Install cancellation before any path can submit. HTML stays disabled if
  // this module never executes; CSP independently denies native navigation.
  form.addEventListener('submit', async event => {
    event.preventDefault();
    if (busy) return;
    const value = request.value;
    if (!boundedText(value, INPUT_LIMIT)) {
      request.setAttribute('aria-invalid', 'true');
      show(INPUT_ERROR);
      request.focus();
      return;
    }
    request.removeAttribute('aria-invalid');
    busy = true;
    submit.disabled = true;
    form.setAttribute('aria-busy', 'true');
    try {
      const answer = await invoke(value);
      if (!boundedText(answer, OUTPUT_LIMIT)) throw new Error('response text');
      show(answer);
    } catch (_) {
      show(RESPONSE_ERROR);
    } finally {
      busy = false;
      submit.disabled = false;
      form.removeAttribute('aria-busy');
    }
  });
  request.addEventListener('keydown', event => {
    if (event.key === 'Enter' && (event.ctrlKey || event.metaKey) && !event.isComposing) {
      event.preventDefault();
      if (!busy) form.requestSubmit();
    }
  });
  submit.disabled = false;
}
