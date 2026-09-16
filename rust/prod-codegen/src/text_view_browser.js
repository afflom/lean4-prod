// Catch initialization failure immediately, including before the first submit.
const ready = Promise.resolve().then(() => init()).then(() => true, () => {
  show(RESPONSE_ERROR);
  return false;
});
attach(async value => {
  if (!await ready) throw new Error('initialization');
  const answer = invoke_bytes(encoder.encode(value));
  if (!(answer instanceof Uint8Array) || answer.byteLength > OUTPUT_LIMIT) {
    throw new Error('response bytes');
  }
  return decoder.decode(answer);
});
