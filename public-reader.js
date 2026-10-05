// The public edition uses the same reader with saved, hash-checked reports.
const manifest = await (await fetch(new URL('./public-manifest.json', import.meta.url))).json();
export function publicUrl(path) {
  const requested = new URL(path, 'https://reader.invalid');
  requested.searchParams.sort();
  const query = requested.searchParams.toString();
  const key = requested.pathname + (query ? '?' + query : '');
  const file = manifest.routes[key];
  if (!file) throw Error('This passage is not included in the public edition: ' + requested.pathname);
  return new URL(file, import.meta.url).href;
}
