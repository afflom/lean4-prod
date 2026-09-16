// A static import would prevent this module (including its error and submit
// handlers) from running at all if the binding module cannot load.
const ready = Promise.resolve().then(loadBinding).then(async binding => {
  if (typeof binding.default !== 'function' || typeof binding.invoke_bytes !== 'function') {
    throw new Error('binding exports');
  }
  await binding.default();
  clearInitialStatus();
  return binding.invoke_bytes;
}).catch(() => {
  show(RESPONSE_ERROR);
  return null;
});
attach(async value => {
  const invoke = await ready;
  if (invoke === null) throw new Error('initialization');
  const answer = invoke(encoder.encode(value));
  if (!(answer instanceof Uint8Array) || answer.byteLength > OUTPUT_LIMIT) {
    throw new Error('response bytes');
  }
  return decoder.decode(answer);
});
