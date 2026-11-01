// Only same-origin application assets are cached. Source buffers live in browser
// storage; proof requests always go to the local, version-aware Lean backend.
const CACHE = 'solidity-lean-workbench-v3';
self.addEventListener('install', event => {
  event.waitUntil(caches.open(CACHE).then(cache => cache.addAll(['/', '/styles.css', '/app.js', '/manifest.json', '/syntax.json', '/vendor/vs/loader.js', '/vendor/vs/editor/editor.main.js', '/vendor/vs/editor/editor.main.css', '/media/proved.svg', '/media/pending.svg', '/media/error.svg', '/media/running.svg'])).then(() => self.skipWaiting()));
});
self.addEventListener('activate', event => event.waitUntil(caches.keys().then(keys => Promise.all(keys.filter(key => key.startsWith('solidity-lean-workbench-') && key !== CACHE).map(key => caches.delete(key)))).then(() => self.clients.claim())));
self.addEventListener('fetch', event => {
  const url = new URL(event.request.url);
  if (event.request.method !== 'GET' || url.origin !== self.location.origin || url.pathname.startsWith('/api/')) return;
  event.respondWith(caches.open(CACHE).then(async cache => {
    const cached = await cache.match(event.request);
    // Hashed Monaco chunks are immutable. The workbench shell and unversioned
    // entry points try the local server first, so normal development reloads
    // pick up edits without requiring users to clear their offline cache.
    if (cached && /\/[\w.]+-[\w-]+\.js$/.test(url.pathname)) return cached;
    try {
      const response = await fetch(event.request);
      if (response.ok) {await cache.put(event.request, response.clone());return response;}
      if (cached) return cached;
      return response;
    } catch (error) {if (cached) return cached; throw error;}
  }));
});
