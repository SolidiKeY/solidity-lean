#!/usr/bin/env node
// Records what Lean shows for each example of the GitHub Pages site
// (`site/examples.json`, `docs/site.md`): the file is opened in the language
// server, elaborated to the end, and then its diagnostics and, at the end of
// every line, the goal the infoview would show there are written to
// `<out>/data/<project>/`. Nothing is computed here: every message and goal
// is the server's own answer, so the page is the editor's view, frozen.
//
// Usage: node scripts/site/export.mjs --project <id> [--out _site]
//          [--only <file>] [--server <cmd>]
// Run it after building the project's libraries (`lake build Solidity`, or
// in `Bridge/` the Velvet libraries): the file workers then load every import
// from the build and only re-elaborate the example itself.
//
// Exit 0 = every example recorded (with or without Lean errors, which the
// page shows), 1 = the server failed or an example timed out.
import { spawn, execFileSync } from 'node:child_process';
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { dirname, resolve, basename } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const repo = resolve(dirname(fileURLToPath(import.meta.url)), '../..');

function parseArgs(argv) {
  const args = { out: '_site', project: null, only: null, server: null };
  for (let i = 0; i < argv.length; i++) {
    const key = argv[i].replace(/^--/, '');
    if (!(key in args)) throw new Error(`unknown option ${argv[i]}`);
    args[key] = argv[++i];
  }
  if (!args.project) throw new Error('--project is required');
  return args;
}

// ---------------------------------------------------------------- the client

/** A JSON-RPC connection over a child's stdio, with LSP's framing. */
export class LspClient {
  constructor(command, args, options) {
    this.child = spawn(command, args, { ...options, stdio: ['pipe', 'pipe', 'inherit'] });
    this.nextId = 1;
    this.pending = new Map();
    this.handlers = new Map();
    this.buffer = Buffer.alloc(0);
    this.closed = new Promise((res) => this.child.on('exit', (code, signal) => {
      for (const { reject } of this.pending.values()) reject(new Error(`server exited (${code ?? signal})`));
      this.pending.clear();
      res({ code, signal });
    }));
    this.child.stdout.on('data', (chunk) => this.receive(chunk));
  }

  receive(chunk) {
    this.buffer = Buffer.concat([this.buffer, chunk]);
    for (;;) {
      const headerEnd = this.buffer.indexOf('\r\n\r\n');
      if (headerEnd < 0) return;
      const header = this.buffer.subarray(0, headerEnd).toString('ascii');
      const length = Number(/Content-Length:\s*(\d+)/i.exec(header)?.[1]);
      if (!Number.isFinite(length)) throw new Error(`bad LSP header: ${header}`);
      if (this.buffer.length < headerEnd + 4 + length) return;
      const body = this.buffer.subarray(headerEnd + 4, headerEnd + 4 + length).toString('utf8');
      this.buffer = this.buffer.subarray(headerEnd + 4 + length);
      this.dispatch(JSON.parse(body));
    }
  }

  dispatch(msg) {
    if (msg.id !== undefined && msg.method === undefined) {
      const p = this.pending.get(msg.id);
      if (!p) return;
      this.pending.delete(msg.id);
      if (msg.error) p.reject(Object.assign(new Error(msg.error.message), { code: msg.error.code }));
      else p.resolve(msg.result);
    } else if (msg.id !== undefined) {
      // A request from the server (capability registration, refreshes):
      // acknowledge it, so the server never waits on us.
      this.write({ jsonrpc: '2.0', id: msg.id, result: null });
    } else {
      this.handlers.get(msg.method)?.(msg.params);
    }
  }

  write(msg) {
    const body = Buffer.from(JSON.stringify(msg), 'utf8');
    this.child.stdin.write(`Content-Length: ${body.length}\r\n\r\n`);
    this.child.stdin.write(body);
  }

  request(method, params) {
    const id = this.nextId++;
    return new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
      this.write({ jsonrpc: '2.0', id, method, params });
    });
  }

  notify(method, params) { this.write({ jsonrpc: '2.0', method, params }); }
  on(method, handler) { this.handlers.set(method, handler); }
}

function withTimeout(promise, ms, what) {
  let timer;
  return Promise.race([
    promise,
    new Promise((_, reject) => { timer = setTimeout(() => reject(new Error(`timed out: ${what}`)), ms); }),
  ]).finally(() => clearTimeout(timer));
}

// ------------------------------------------------------------ what we record

const SEVERITY = { 1: 'error', 2: 'warning', 3: 'information', 4: 'hint' };

/** Title and summary from the module docstring's first `# ` heading. */
export function describe(source, file) {
  const doc = /\/-!([\s\S]*?)-\//.exec(source)?.[1] ?? '';
  const lines = doc.split('\n');
  const at = lines.findIndex((l) => /^#\s+\S/.test(l.trim()));
  const title = at >= 0 ? lines[at].trim().replace(/^#\s+/, '') : basename(file, '.lean');
  const para = [];
  for (const l of lines.slice(at + 1)) {
    if (l.trim() === '') { if (para.length) break; else continue; }
    if (/^\s*(#|\*|-|\d+\.|\|)/.test(l) && !para.length) break;
    para.push(l.trim());
  }
  return { title, summary: para.join(' ') };
}

/** The lines worth asking a goal for, and where: their last non-blank column. */
export function goalPositions(source) {
  const out = [];
  source.split('\n').forEach((text, line) => {
    const trimmed = text.replace(/\s+$/, '');
    if (trimmed.length) out.push({ line, character: trimmed.length });
  });
  return out;
}

async function pool(items, size, task) {
  let next = 0;
  await Promise.all(Array.from({ length: Math.min(size, items.length) }, async () => {
    while (next < items.length) await task(items[next++]);
  }));
}

/** Elaborate one file and collect its diagnostics and goals. */
export async function recordFile(client, path, { timeoutMs = 45 * 60_000 } = {}) {
  const uri = pathToFileURL(path).href;
  const source = readFileSync(path, 'utf8');
  let diagnostics = [];
  client.on('textDocument/publishDiagnostics', (p) => { if (p.uri === uri) diagnostics = p.diagnostics; });
  const started = Date.now();
  const textDocument = { uri };
  const goals = {};
  let elapsedMs;
  client.notify('textDocument/didOpen', { textDocument: { uri, languageId: 'lean4', version: 1, text: source } });
  try {
    await withTimeout(client.request('textDocument/waitForDiagnostics', { uri, version: 1 }), timeoutMs, path);
    elapsedMs = Date.now() - started;
    await pool(goalPositions(source), 16, async (position) => {
      const tactic = await client.request('$/lean/plainGoal', { textDocument, position }).catch(() => null);
      if (tactic && Array.isArray(tactic.goals)) {
        goals[position.line] = { kind: 'tactic', goals: tactic.goals };
        return;
      }
      const term = await client.request('$/lean/plainTermGoal', { textDocument, position }).catch(() => null);
      if (term && typeof term.goal === 'string') goals[position.line] = { kind: 'term', goals: [term.goal] };
    });
  } finally {
    // The last diagnostics are published before `waitForDiagnostics`
    // answers; the goal requests give any straggler time to arrive.
    client.notify('textDocument/didClose', { textDocument });
  }
  const messages = diagnostics.map((d) => {
    const range = d.fullRange ?? d.range;
    return { severity: SEVERITY[d.severity] ?? 'information', start: range.start, end: range.end, text: d.message };
  }).sort((a, b) => a.start.line - b.start.line || a.start.character - b.start.character);
  return { source, messages, goals, elapsedMs };
}

// ---------------------------------------------------------------------- main

function git(...args) {
  try { return execFileSync('git', args, { cwd: repo, encoding: 'utf8' }).trim(); } catch { return null; }
}

async function main() {
  const args = parseArgs(process.argv.slice(2));
  const config = JSON.parse(readFileSync(resolve(repo, 'site/examples.json'), 'utf8'));
  const project = config.projects.find((p) => p.id === args.project);
  if (!project) throw new Error(`no project ${args.project} in site/examples.json`);
  const root = resolve(repo, project.root);
  const outDir = resolve(repo, args.out, 'data', project.id);
  mkdirSync(outDir, { recursive: true });

  const [command, ...serverArgs] = args.server
    ? args.server.split(' ')
    : ['lake', 'serve', '--', '-Dserver.reportDelayMs=0', '--tstack=131072'];
  const client = new LspClient(command, serverArgs, { cwd: root });
  await client.request('initialize', {
    processId: process.pid,
    rootUri: pathToFileURL(root).href,
    capabilities: { textDocument: { publishDiagnostics: {} } },
  });
  client.notify('initialized', {});

  const commit = process.env.GITHUB_SHA ?? git('rev-parse', 'HEAD');
  const toolchain = readFileSync(resolve(root, 'lean-toolchain'), 'utf8').trim();
  const index = [];
  let failures = 0;
  for (const example of project.examples) {
    if (args.only && example.file !== args.only) continue;
    const path = resolve(root, example.file);
    process.stdout.write(`${project.id}: ${example.file} … `);
    const entry = { ...example, ...describe(readFileSync(path, 'utf8'), example.file), ...(example.title ? { title: example.title } : {}) };
    try {
      const recorded = await recordFile(client, path);
      const errors = recorded.messages.filter((m) => m.severity === 'error').length;
      entry.status = errors ? 'errors' : 'ok';
      entry.elapsedMs = recorded.elapsedMs;
      entry.data = `${example.file.replaceAll('/', '__')}.json`;
      writeFileSync(resolve(outDir, entry.data), JSON.stringify({ project: project.id, ...entry, ...recorded }));
      console.log(`${entry.status}, ${recorded.messages.length} messages, ${Object.keys(recorded.goals).length} goals, ${(recorded.elapsedMs / 1000).toFixed(1)} s`);
    } catch (e) {
      failures++;
      entry.status = 'failed';
      entry.error = String(e.message ?? e);
      console.log(`FAILED: ${entry.error}`);
    }
    index.push(entry);
  }
  writeFileSync(resolve(outDir, 'index.json'), JSON.stringify({
    project: project.id, commit, toolchain, recordedAt: new Date().toISOString(), examples: index,
  }, null, 1));
  await withTimeout(client.request('shutdown', null), 60_000, 'shutdown').catch(() => {});
  client.notify('exit', null);
  await withTimeout(client.closed, 10_000, 'exit').catch(() => client.child.kill());
  process.exitCode = failures ? 1 : 0;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch((e) => { console.error(e); process.exit(1); });
}
