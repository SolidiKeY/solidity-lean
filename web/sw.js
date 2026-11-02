// Only same-origin application assets are cached. Source buffers live in browser
// storage; compiler and proof requests stay in browser workers.
const CACHE = 'solidity-lean-browser-workbench-v4';
const REQUIRE_ASSET_MANIFEST = false; // Static builds require the complete list.
self.addEventListener('install', event => {
  event.waitUntil((async()=>{
    const cache=await caches.open(CACHE);
    let assets=['/', '/styles.css', '/app.js', '/browser-connection.js', '/manifest.json', '/syntax.json', '/vendor/vs/loader.js', '/vendor/vs/editor/editor.main.js', '/vendor/vs/editor/editor.main.css', '/media/proved.svg', '/media/pending.svg', '/media/error.svg', '/media/running.svg'];
    try{const response=await fetch('/asset-manifest.json',{cache:'no-store'});if(!response.ok)throw new Error('Offline asset list is unavailable');const manifest=await response.json();if(!Array.isArray(manifest.assets)||!manifest.assets.length||manifest.assets.some(asset=>typeof asset!=='string'||!asset.startsWith('/')||asset.startsWith('//')))throw new Error('Invalid offline asset list');assets=[...new Set(['/', '/asset-manifest.json',...manifest.assets])];}catch(error){if(REQUIRE_ASSET_MANIFEST)throw error;}
    for(let offset=0;offset<assets.length;offset+=16){await cache.addAll(assets.slice(offset,offset+16).map(url=>new Request(url,{cache:'no-store'})));for(const client of await self.clients.matchAll({includeUncontrolled:true}))client.postMessage({method:'offlineProgress',done:Math.min(offset+16,assets.length),total:assets.length});}
    await self.skipWaiting();
  })());
});
self.addEventListener('activate', event => event.waitUntil(caches.keys().then(keys => Promise.all(keys.filter(key => (key.startsWith('solidity-lean-workbench-')||key.startsWith('solidity-lean-browser-workbench-')) && key !== CACHE).map(key => caches.delete(key)))).then(() => self.clients.claim())));
self.addEventListener('fetch', event => {
  const url = new URL(event.request.url);
  if (event.request.method !== 'GET' || url.origin !== self.location.origin || url.pathname.startsWith('/api/')) return;
  event.respondWith(caches.open(CACHE).then(async cache => {
    const cached = await cache.match(event.request) || (event.request.mode==='navigate'&&url.pathname==='/'?await cache.match('/'):undefined);
    // Hashed Monaco chunks are immutable. The workbench shell and unversioned
    // entry points try the local server first, so normal development reloads
    // pick up edits without requiring users to clear their offline cache.
    if (cached && (/\/[\w.]+-[\w-]+\.js$/.test(url.pathname)||/^\/lean\/assets\/[a-f0-9]+\./.test(url.pathname))) return cached;
    try {
      const response = await fetch(event.request);
      if (response.ok) {await cache.put(event.request, response.clone());return response;}
      if (cached) return cached;
      return response;
    } catch (error) {if (cached) return cached; throw error;}
  }));
});
