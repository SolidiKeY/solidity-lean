#!/usr/bin/env node
'use strict';
// The browser uses the extension's production LanguageClient, LSP and proof workers.
// There is no remote API, package fetch, shell endpoint, or separate verifier.
const http = require('node:http');
const fs = require('node:fs');
const path = require('node:path');
const {pathToFileURL} = require('node:url');
const {WebSocketServer, WebSocket} = require('ws');
const {LanguageClient} = require('../vscode/src/lsp-client.cjs');

const ROOT = path.resolve(__dirname, '..');
const MIME = {'.html':'text/html; charset=utf-8','.css':'text/css','.js':'text/javascript','.json':'application/json','.svg':'image/svg+xml','.ttf':'font/ttf','.woff2':'font/woff2','.wasm':'application/wasm'};
const METHODS = new Set(['textDocument/hover','textDocument/completion','textDocument/definition','textDocument/references','textDocument/documentSymbol','textDocument/signatureHelp','textDocument/documentHighlight','textDocument/prepareRename','textDocument/rename','textDocument/formatting','textDocument/codeAction']);
const validName = name => typeof name === 'string' && /^[A-Za-z0-9_$][A-Za-z0-9_.$-]*\.sol$/.test(name) && name.length <= 120;
function settings(value = {}) {
  const automaticVerification = value.automaticVerification ?? 'never';
  if (!['never','change','save'].includes(automaticVerification)) throw new Error('Invalid automatic verification setting');
  const workers = value.workers ?? 1;
  if (!Number.isInteger(workers) || workers < 1 || workers > 4) throw new Error('Workers must be between 1 and 4');
  return {automaticVerification, workers, counterexamples:!!value.counterexamples, auditPreconditions:!!value.auditPreconditions};
}

function createServer({port = 4173, Client = LanguageClient, backendPath = ROOT} = {}) {
  const sessions = new Set();
  let address;
  const server = http.createServer(async (req, res) => {
    const headers = {
      'X-Content-Type-Options':'nosniff', 'Referrer-Policy':'no-referrer',
      'Content-Security-Policy':"default-src 'self'; script-src 'self' 'unsafe-eval'; style-src 'self' 'unsafe-inline'; font-src 'self' data:; img-src 'self' data:; connect-src 'self'; worker-src 'self' blob:; object-src 'none'; frame-ancestors 'none'; base-uri 'none'",
      'Cache-Control':'no-cache'
    };
    const reply = (status, type, body) => { res.writeHead(status, {...headers, 'Content-Type':type}); res.end(body); };
    if (!['GET','HEAD'].includes(req.method)) return reply(405, 'text/plain', 'Read-only HTTP endpoint');
    if (!allowedHost(req.headers.host)) return reply(403, 'text/plain', 'Loopback host required');
    try {
      const pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname);
      if (pathname === '/api/bootstrap') {
        const files = Object.fromEntries(fs.readdirSync(path.join(__dirname, 'examples')).filter(validName).map(name => [name, fs.readFileSync(path.join(__dirname, 'examples', name), 'utf8')]));
        return reply(200, 'application/json', JSON.stringify({files, backend:'Solidity Lean', offline:true, protocol:1}));
      }
      const routes = {'/':'index.html','/index.html':'index.html','/app.js':'app.js','/browser-connection.js':'browser/connection.js','/styles.css':'styles.css','/sw.js':'sw.js','/manifest.json':'manifest.json'};
      let file;
      if (pathname === '/syntax.json') file = path.join(ROOT, 'vscode/syntaxes/solidity.tmLanguage.json');
      else if (routes[pathname]) file = path.join(__dirname, routes[pathname]);
      else if (pathname.startsWith('/vendor/vs/')) {
        const base = path.join(__dirname, 'node_modules/monaco-editor/min/vs');
        file = path.resolve(base, pathname.slice('/vendor/vs/'.length));
        if (!file.startsWith(base + path.sep)) return reply(403,'text/plain','Invalid path');
      } else if (/^\/media\/(proved|pending|error|running)\.svg$/.test(pathname)) file = path.join(ROOT, 'vscode', pathname);
      if (!file || !fs.statSync(file).isFile()) return reply(404, 'text/plain', 'Not found');
      res.writeHead(200, {...headers, 'Content-Type':MIME[path.extname(file)] || 'application/octet-stream'});
      if (req.method === 'HEAD') res.end(); else fs.createReadStream(file).pipe(res);
    } catch { reply(404, 'text/plain', 'Not found'); }
  });
  const allowedHost = host => !!host && ['127.0.0.1','localhost','[::1]'].some(h => host === `${h}:${address?.port ?? port}`);
  // One 8-MiB source can occupy 48 MiB after JSON control-character escaping.
  // Browser workspace updates send one file per message; total disk size is
  // independently checked below.
  const wss = new WebSocketServer({noServer:true, maxPayload:52 * 1024 * 1024});
  server.on('upgrade', (req, socket, head) => {
    const origin = req.headers.origin;
    if (req.url !== '/lsp' || !allowedHost(req.headers.host) || origin && origin !== `http://${req.headers.host}`) {
      socket.write('HTTP/1.1 403 Forbidden\r\nConnection: close\r\n\r\n'); socket.destroy(); return;
    }
    wss.handleUpgrade(req, socket, head, ws => wss.emit('connection', ws));
  });
  wss.on('connection', ws => {
    const base = path.join(backendPath, '.lake/web-ide');
    fs.mkdirSync(base, {recursive:true});
    const directory = fs.mkdtempSync(path.join(base, 'session-'));
    const docs = new Map();
    let client, config = settings(), closed = false, mutations = Promise.resolve();
    const send = value => { if (ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify(value)); };
    let disposal;
    const session = {dispose() {
      if (disposal) return disposal;
      closed = true;
      disposal = (async () => {try{await mutations; await client?.dispose(); fs.rmSync(directory, {recursive:true, force:true});}finally{sessions.delete(session);}})();
      return disposal;
    }};
    sessions.add(session);
    const event = (method, params) => {
      const doc = [...docs.values()].find(d => d.uri.toString() === params?.uri);
      send({method, params:{...params, ...(doc ? {name:doc.name} : {})}});
    };
    const getClient = () => {
      if (closed) throw new Error('Session closed');
      if (!client) {
        client = new Client({backendPath, projectRoot:directory, nodePath:process.execPath, timeoutMs:120000, ...config});
        for (const type of ['diagnostics','report','status','invalidated']) client.on(type, params => event(type, params));
        client.on('serverError', error => event('backendError', {message:error.message}));
        client.on('log', message => event('log', {message}));
      }
      return client;
    };
    const document = name => {
      if (!validName(name) || !docs.has(name)) throw new Error('Unknown Solidity document');
      return docs.get(name);
    };
    async function mutate(method, p) {
      if (closed) throw new Error('Session closed');
      if (method === 'workspace') {
        if (!p.files || Array.isArray(p.files) || typeof p.files !== 'object') throw new Error('Invalid workspace');
        const files = Object.entries(p.files);
        if (files.length > 128 || files.some(([name,text]) => !validName(name) || typeof text !== 'string' || Buffer.byteLength(text) > 8 * 1024 * 1024)) throw new Error('Invalid workspace files');
        const next = new Map(fs.readdirSync(directory).filter(validName).map(name => [name, fs.statSync(path.join(directory,name)).size]));
        for (const [name,text] of files) next.set(name, Buffer.byteLength(text));
        if (next.size > 128 || [...next.values()].reduce((sum,size) => sum + size, 0) > 32 * 1024 * 1024) throw new Error('Workspace exceeds 128 files or 32 MiB');
        for (const [name,text] of files) fs.writeFileSync(path.join(directory,name), text);
        if (client) {await client.ready; for (const [name] of files) client.peer.notify('workspace/didChangeWatchedFiles', {changes:[{uri:pathToFileURL(path.join(directory,name)).href,type:2}]});}
        return {updated:files.length};
      }
      if (method === 'open' || method === 'change') {
        if (!validName(p.name) || typeof p.text !== 'string' || Buffer.byteLength(p.text) > 8 * 1024 * 1024 || !Number.isSafeInteger(p.version) || p.version < 1) throw new Error('Invalid document snapshot');
        let doc = docs.get(p.name);
        if (!doc) {
          if (docs.size >= 4) throw new Error('Close a file before opening another (maximum four open documents)');
          doc = {name:p.name, uri:pathToFileURL(path.join(directory, p.name)), version:0, text:'', getText(){return this.text;}};
          docs.set(p.name, doc);
        }
        if (p.version <= doc.version) throw new Error('Document version must increase');
        doc.version = p.version; doc.text = p.text;
        await getClient().sync(doc);
        return {uri:doc.uri.toString(), version:doc.version};
      }
      if (method === 'close') {
        const doc = document(p.name); fs.writeFileSync(path.join(directory,doc.name),doc.text); doc.isClosed = true; client?.closeDocument(doc.uri.toString()); docs.delete(p.name); return null;
      }
      if (method === 'save') {
        const doc = document(p.name); fs.writeFileSync(path.join(directory, doc.name), doc.text);
        await getClient().sync(doc); client.peer.notify('textDocument/didSave', {textDocument:{uri:doc.uri.toString()}, text:doc.text});
        return {saved:true};
      }
      if (method === 'configure') {
        config = settings(p); if (client) { await client.ready; client.peer.notify('workspace/didChangeConfiguration', {settings:{...config,projectRoot:directory,timeoutMs:120000}}); } return config;
      }
      if (method === 'restart') {
        await client?.dispose(); if (closed) throw new Error('Session closed'); client = null; for (const doc of docs.values()) await getClient().sync(doc); return {restarted:true};
      }
      throw new Error('Unknown mutation');
    }
    const mutationMethods = new Set(['workspace','open','change','close','save','configure','restart']);
    ws.on('message', async data => {
      let id;
      try {
        const message = JSON.parse(data); id = message.id;
        if (!Number.isSafeInteger(id) || typeof message.method !== 'string') throw new Error('Invalid request');
        const {method, params:p = {}} = message;
        let result;
        if (mutationMethods.has(method)) {
          const operation = mutations.then(() => mutate(method, p)); mutations = operation.catch(() => {}); result = await operation;
        } else {
          await mutations;
          if (method === 'verify') {
            const doc = document(p.name);
            if (p.version !== doc.version) throw new Error('Document content changed');
            result = await getClient().verify(doc, {...config, listing:!!p.listing, function:p.function, contract:p.contract, timeoutMs:120000});
          } else if (method === 'cancel') { client?.cancel(p.name ? document(p.name).uri.toString() : undefined); result = null; }
          else if (method === 'stats') { const c = getClient(); await c.ready; result = await c.peer.request('solidityLean/stats', {}); }
          else if (method === 'workspace/symbol') { const c = getClient(); await c.ready; result = await c.peer.request(method, {query:String(p.query || '')}); }
          else if (METHODS.has(method)) {
            const doc = document(p.name);
            if (p.version !== doc.version) throw new Error('Document content changed');
            const {name, version, textDocument, ...params} = p;
            result = await getClient().request(method, doc, params);
          } else throw new Error('Method not allowed');
        }
        send({id, result});
      } catch (error) { send({id, error:{message:error.message, code:error.code || -32602}}); }
    });
    ws.on('close', () => session.dispose()); ws.on('error', () => session.dispose());
  });
  return {
    server,
    async listen() { await new Promise((resolve, reject) => {server.once('error', reject); server.listen(port, '127.0.0.1', resolve);}); address = server.address(); return `http://127.0.0.1:${address.port}`; },
    async close() { for (const ws of wss.clients) ws.close(); await Promise.all([...sessions].map(s => s.dispose())); await new Promise(resolve => server.close(resolve)); wss.close(); }
  };
}
if (require.main === module) {
  const app = createServer({port:Number(process.env.PORT || 4173)});
  app.listen().then(url => console.log(`Native comparison server: ${url}/?backend=native\nDevelopment tooling using local compiler and Lean processes.`)).catch(error => {console.error(error); process.exitCode = 1;});
  for (const signal of ['SIGINT','SIGTERM']) process.once(signal, async () => {await app.close(); process.exit();});
}
module.exports = {createServer, validName, settings};
