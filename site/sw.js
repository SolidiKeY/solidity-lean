const CACHE='solidity-playground-v1';
const ASSETS=['./','index.html','app.js','style.css','examples.json','playground.mjs','runtime-client.mjs','runtime.txt'];
self.addEventListener('install',event=>event.waitUntil(caches.open(CACHE).then(cache=>cache.addAll(ASSETS)).then(()=>self.skipWaiting())));
self.addEventListener('activate',event=>event.waitUntil(self.clients.claim()));
self.addEventListener('fetch',event=>{if(event.request.method==='GET' && new URL(event.request.url).origin===location.origin)event.respondWith(caches.match(event.request).then(hit=>hit||fetch(event.request)));});
