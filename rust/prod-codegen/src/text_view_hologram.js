// Only the Hologram transport envelope is parsed, never application payloads.
// JSON can escape each payload byte as six ASCII bytes. Bound its envelope
// before decoding/parsing; streaming also handles absent Content-Length.
async function envelope(response) {
  if (!response.ok || !response.body) throw new Error('intent response');
  const maximum = OUTPUT_LIMIT * 6 + 256;
  const length = response.headers.get('content-length');
  if (length !== null && (!/^[0-9]+$/.test(length) || Number(length) > maximum)) {
    await response.body.cancel();
    throw new Error('intent size');
  }
  const reader = response.body.getReader();
  const decode = new TextDecoder('utf-8', {fatal: true, ignoreBOM: true});
  let total = 0;
  let text = '';
  try {
    for (;;) {
      const {done, value} = await reader.read();
      if (done) break;
      if (!(value instanceof Uint8Array) || value.byteLength > maximum - total) {
        throw new Error('intent size');
      }
      total += value.byteLength;
      text += decode.decode(value, {stream: true});
    }
    text += decode.decode();
    return JSON.parse(text);
  } catch (error) {
    await reader.cancel();
    throw error;
  } finally {
    reader.releaseLock();
  }
}
attach(async value => {
  const response = await fetch('/_hologram/intent', {
    method: 'POST',
    headers: {'content-type': 'application/json'},
    body: JSON.stringify({version: 1, name: 'application.invoke', payload: value})
  });
  const answer = await envelope(response);
  if (answer === null || answer.version !== 1 || !Array.isArray(answer.outputs) || answer.outputs.length !== 1) {
    throw new Error('intent envelope');
  }
  return answer.outputs[0];
});
clearInitialStatus();
