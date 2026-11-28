/** External observations only: never write run outputs into the code checkout. */
import {createHash} from 'node:crypto';
import {appendFileSync, closeSync, fstatSync, fsyncSync, linkSync, lstatSync, mkdirSync, openSync, readFileSync,
  realpathSync, statSync, unlinkSync, writeFileSync} from 'node:fs';
import {dirname, join, relative, resolve, sep} from 'node:path';
import {fileURLToPath} from 'node:url';
import {summarize, validateRow} from './campaign.mjs';
const ROOT = realpathSync(resolve(dirname(fileURLToPath(import.meta.url)), '../..'));
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const within = (parent, child) => child === parent || child.startsWith(parent + sep);
const encode = value => JSON.stringify(value) + '\n';

/** Pin exactly the execution inputs selected by the final transport. This is
 * byte identity, not a claim that the caller listed a complete dependency set. */
export function fingerprint(paths) {
  if (!Array.isArray(paths) || !paths.length) throw Error('execution input paths required');
  const entries = paths.map(path => {
    if (typeof path !== 'string' || !path.length) throw Error('invalid execution input path');
    const canonical = realpathSync(path);
    if (!statSync(canonical).isFile()) throw Error('execution input must be a file');
    return {path:resolve(path), canonical, sha256:hash(readFileSync(canonical))};
  }).sort((a,b) => a.path.localeCompare(b.path));
  if (new Set(entries.map(e => e.canonical)).size !== entries.length) throw Error('duplicate execution input');
  return entries;
}

function durableFile(path, text) {
  const fd = openSync(path, 'wx', 0o600);
  try { writeFileSync(fd, text); fsyncSync(fd); } finally { closeSync(fd); }
}

/** Create a fresh run directory under an EXISTING external parent. Each append
 * is validated and fsynced before returning. Only finish writes report.json;
 * absent report.json means incomplete. The hard-link publication is the commit
 * point: an unlink/fsync error afterward may leave a valid published report,
 * but throws and poisons the writer because durability was not confirmed.
 * A failure poisons the writer rather
 * than allowing a later finish to turn partial evidence into a complete run. */
export function openRun(directory, {requested, inputPaths, metadata = {}}) {
  const runMetadata = JSON.parse(JSON.stringify(metadata));
  if (!Number.isSafeInteger(requested) || requested < 1 || requested > 10000)
    throw Error('requested must be 1..10000');
  if (typeof directory !== 'string' || !directory.length) throw Error('output directory required');
  const path = resolve(directory), parent = realpathSync(dirname(path));
  const output = join(parent, relative(dirname(path), path));
  if (within(ROOT, path) || within(ROOT, output)) throw Error('observations must be outside checkout');
  const before = fingerprint(inputPaths);
  mkdirSync(output, {mode:0o700}); // Existing directories, including symlinks, fail.
  durableFile(join(output,'inputs.json'), encode({schema:1,requested,metadata:runMetadata,inputs:before}));
  const fd = openSync(join(output,'observations.jsonl'), 'wx', 0o600);
  const directoryFd = openSync(output, 'r');
  try {
    fsyncSync(directoryFd);
    const parentFd = openSync(parent, 'r');
    try { fsyncSync(parentFd); } finally { closeSync(parentFd); }
  } catch (error) { closeSync(fd); closeSync(directoryFd); throw error; }
  const identity = fstatSync(directoryFd);
  const checkDirectory = () => {
    const current = lstatSync(output);
    if (!current.isDirectory() || current.dev !== identity.dev || current.ino !== identity.ino ||
        realpathSync(output) !== output) throw Error('output directory changed');
  };
  let rows = [], state = 'open', closed = false, findingsIdentity;
  const findings = [];
  const checkFindings = () => {
    if (!findingsIdentity) return;
    const dir = join(output,'findings'), current = lstatSync(dir);
    if (!current.isDirectory() || current.dev !== findingsIdentity.dev || current.ino !== findingsIdentity.ino || realpathSync(dir) !== dir)
      throw Error('findings directory changed');
    for (const item of findings)
      if (hash(readFileSync(join(output,item.path))) !== item.sha256) throw Error('saved finding changed');
  };
  const recorded = createHash('sha256');
  const close = () => { if (!closed) { closed = true; try { closeSync(fd); } finally { closeSync(directoryFd); } } };
  const poison = error => { state = 'failed'; close(); throw error; };
  return {
    directory:output,
    append(entry) {
      if (state !== 'open') throw Error('run writer is not open');
      try {
        checkDirectory();
        // Snapshot mutable callers before recording or retaining anything.
        const copy = JSON.parse(JSON.stringify(entry));
        validateRow(copy.record, copy.row);
        if (rows.length >= requested) throw Error('too many observations');
        summarize([...rows,copy.row], rows.length + 1);
        const serialized = encode(copy);
        appendFileSync(fd, serialized); fsyncSync(fd); recorded.update(serialized);
        rows.push(copy.row);
      } catch (error) { poison(error); }
    },
    writeFinding(value) {
      if (state !== 'open') throw Error('run writer is not open');
      try {
        checkDirectory(); checkFindings();
        const text = JSON.stringify(value,null,2) + '\n', sha256 = hash(text);
        const path = 'findings/' + sha256 + '.json';
        if (findings.some(item=>item.path===path)) return path;
        if (!findingsIdentity) {
          mkdirSync(join(output,'findings'),{mode:0o700});
          findingsIdentity = lstatSync(join(output,'findings'));
        }
        durableFile(join(output,path),text);
        const fd = openSync(join(output,'findings'),'r');
        try { fsyncSync(fd); } finally { closeSync(fd); }
        fsyncSync(directoryFd);
        findings.push({path,sha256});
        return path;
      } catch (error) { poison(error); }
    },
    finish() {
      if (state !== 'open') throw Error('run writer is not open');
      try {
        checkDirectory();
        checkFindings();
        const summary = summarize(rows, requested);
        const after = fingerprint(inputPaths);
        if (JSON.stringify(before) !== JSON.stringify(after)) throw Error('execution inputs changed');
        fsyncSync(fd);
        const observationsSha256 = hash(readFileSync(join(output,'observations.jsonl')));
        if (observationsSha256 !== recorded.digest('hex')) throw Error('saved observations changed');
        const report = {schema:1,summary,metadata:runMetadata,inputs:before, observationsSha256,findings:[...findings],
          boundary:'External observations only; no kernel proof. Mismatches still require triage.'};
        checkDirectory();
        durableFile(join(output,'report.pending.json'), encode(report));
        linkSync(join(output,'report.pending.json'), join(output,'report.json'));
        unlinkSync(join(output,'report.pending.json'));
        fsyncSync(directoryFd); close();
        state = 'finished';
        return report;
      } catch (error) { poison(error); }
    },
    abort() { if (state === 'open') { state = 'aborted'; close(); } }
  };
}
