'use strict';
const fs = require('node:fs');
const path = require('node:path');

// register(server) may call onRequest and registerCodeLensProvider.
// Registrations are committed atomically after the feature returns.
async function register(peer, service, directory = __dirname) {
  const requests = new Map(), lenses = [], disposables = [];
  const log = message => {if (!peer.closed) peer.notify('window/logMessage', {type: 1, message});};
  const cleanup = async items => {for (const item of items.reverse()) try {await item?.dispose?.();} catch (error) {log(`Server feature disposal failed: ${error.message}`);}};
  for (const file of fs.readdirSync(directory).filter(name => name.endsWith('.cjs') && name !== 'index.cjs').sort()) {
    const pending = new Map(), pendingLenses = [], owned = [];
    const server = {
      service,
      onRequest(method, handler) {
        if (!(typeof method === 'string' && method.startsWith('solidityLean/') && method.length > 'solidityLean/'.length) || typeof handler !== 'function') throw new Error('Invalid custom request');
        if (requests.has(method) || pending.has(method) || peer.requests.has(method)) throw new Error(`Request already registered: ${method}`);
        pending.set(method, handler);
      },
      registerCodeLensProvider(handler) {
        if (typeof handler !== 'function') throw new Error('Invalid code lens provider');
        pendingLenses.push({file, handler});
      }
    };
    try {
      const feature = require(path.join(directory, file));
      if (typeof feature.register !== 'function') throw new Error('missing register(server)');
      const result = await feature.register(server);
      if (result) owned.push(result);
      for (const [method, handler] of pending) {requests.set(method, handler); peer.onRequest(method, handler);}
      lenses.push(...pendingLenses); disposables.push(owned);
    } catch (error) {await cleanup(owned); log(`Server feature ${file} failed: ${error?.message || error}`);}
  }
  if (lenses.length) peer.onRequest('textDocument/codeLens', async (params, id) => {
    const results = await Promise.all(lenses.map(async ({file, handler}) => {
      try {return await handler(params, id);} catch (error) {log(`Server feature ${file} code lens failed: ${error?.message || error}`);return [];}
    }));
    return results.flatMap(result => result || []);
  });
  let disposal;
  return {requests: [...requests.keys()], codeLens: lenses.length > 0, dispose() {
    if (disposal) return disposal;
    for (const [method, handler] of requests) if (peer.requests.get(method) === handler) peer.requests.delete(method);
    if (lenses.length) peer.requests.delete('textDocument/codeLens');
    disposal=(async()=>{for (const items of disposables.reverse()) await cleanup(items);})();
    return disposal;
  }};
}
module.exports = {register};
