export const dummyForm = () => {
  const form = new FormData()
  form.set('foo', 'bar')
  const hi = Buffer.from('hello, world!', 'utf8')
  form.set('baz', new Blob([hi.buffer.slice(hi.byteOffset, hi.byteOffset + hi.byteLength)], {type: 'text/plain'}), 'foo.txt')
  return form
}
