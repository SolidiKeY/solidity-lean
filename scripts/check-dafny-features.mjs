import { readFileSync, statSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const commit = 'de36f2ec1f9c530080eff7929ae28229f45da069';
export const familyIds = Object.freeze([
  'preconditions', 'postconditions', 'old-state', 'quantifiers', 'function-frames',
  'loop-invariants', 'loop-frames', 'termination-metrics', 'modular-calls',
  'recursive-contracts', 'ghost-variables', 'lemmas-predicates', 'proof-blocks',
  'opacity-reveal', 'assert-assume', 'spec-collections', 'comprehensions',
  'numeric-types', 'floating-real-ordinal', 'refinement-types', 'algebraic-datatypes',
  'arrays-aliasing-allocation', 'functions-lambdas-generics', 'classes-traits-inheritance',
  'modules-refinement', 'iterators-coinduction', 'control-flow', 'nondeterminism-havoc',
  'automation-budgets', 'triggers-induction', 'counterexamples', 'audit-vacuity-dead-code',
  'unit-tests-generation', 'cli-project-artifacts', 'ide-language-services', 'plugins-backends',
]);
const chapters = ['Programs', 'Modules', 'Types', 'Specifications', 'Statements',
  'Expressions', 'Refinement', 'Attributes', 'Topics', 'UserGuide', 'VSCodeIDE', 'Plugins'];
const inspectedPaths = [
  ...chapters.map(name => `docs/DafnyRef/${name}.md`),
  'Source/DafnyCore/Verifier/Statements/BoogieGenerator.TrLoop.cs',
  'Source/DafnyCore/Verifier/Statements/BoogieGenerator.TrCall.cs',
  'Source/DafnyCore/Verifier/BoogieGenerator.Decreases.cs',
  'Source/DafnyLanguageServer.Test/Diagnostics/VerificationDiagnostics.cs',
  'Source/DafnyLanguageServer.Test/Various/CancelVerificationTest.cs',
  'Source/DafnyLanguageServer.Test/Synchronization/EditDocumentTest.cs',
  'Source/DafnyLanguageServer/DafnyRequestNames.cs',
  'Source/DafnyLanguageServer/Handlers/Custom/CounterExampleParams.cs',
  'Source/DafnyLanguageServer/Handlers/Custom/DafnyCounterExampleHandler.cs',
  'Source/DafnyLanguageServer/Handlers/Custom/CounterExampleItem.cs',
  'Source/DafnyLanguageServer.Test/Various/CounterExampleTest.cs',
];
const relativePath = p => typeof p === 'string' && p.length > 0 &&
  !p.includes('\\') && !p.startsWith('/') && p.split('/').every(s => s && s !== '.' && s !== '..');
const nonempty = s => typeof s === 'string' && s.trim().length > 0;

/** Offline metadata/evidence checks; does not establish semantic parity or refetch Git blobs. */
export function validateManifest(manifest, options = {}) {
  const errors = [];
  const localRoot = options.root ?? root;
  const check = (condition, message) => { if (!condition) errors.push(message); };
  if (!manifest || typeof manifest !== 'object') return ['manifest must be an object'];
  check(manifest.schemaVersion === 1, 'unsupported schemaVersion');
  check(nonempty(manifest.scope), 'missing scope statement');
  check(/^[0-9a-f]{8,40}$/.test(manifest.localBaseline ?? ''), 'invalid local baseline');
  check(manifest.upstream?.repository === 'dafny-lang/dafny', 'unexpected repository');
  check(manifest.upstream?.commit === commit, 'unexpected upstream commit; review before repinning');
  const inspectedOn = manifest.upstream?.inspectedOn;
  const parsedDate = typeof inspectedOn === 'string' ? Date.parse(inspectedOn) : NaN;
  check(/^\d{4}-\d{2}-\d{2}$/.test(inspectedOn ?? '') && Number.isFinite(parsedDate) &&
    new Date(parsedDate).toISOString().slice(0, 10) === inspectedOn, 'invalid inspection date');
  const sources = manifest.upstream?.sources;
  if (!Array.isArray(sources)) errors.push('sources must be an array');
  const seenSources = new Set();
  for (const source of Array.isArray(sources) ? sources : []) {
    check(source && inspectedPaths.includes(source.path), `unknown inspected source: ${source?.path}`);
    check(!seenSources.has(source?.path), `duplicate inspected source: ${source?.path}`);
    seenSources.add(source?.path);
    check(/^[0-9a-f]{40}$/.test(source?.blob ?? ''), `invalid Git blob: ${source?.path}`);
    check(nonempty(source?.inspection), `missing inspection scope: ${source?.path}`);
  }
  for (const path of inspectedPaths) check(seenSources.has(path), `missing inspected source: ${path}`);
  if (!Array.isArray(manifest.features)) return [...errors, 'features must be an array'];
  const seen = new Set();
  const cited = new Set();
  for (const feature of manifest.features) {
    const id = feature?.id;
    check(familyIds.includes(id), `unknown feature family: ${id}`);
    check(!seen.has(id), `duplicate feature family: ${id}`);
    seen.add(id);
    check(nonempty(feature?.category), `missing category: ${id}`);
    check(['runtime', 'specification', 'verification', 'host', 'tooling', 'notApplicable'].includes(feature?.relevance), `invalid relevance: ${id}`);
    check(['present', 'partial', 'missing', 'notApplicable'].includes(feature?.status), `invalid status: ${id}`);
    check(nonempty(feature?.assessment) && nonempty(feature?.next), `missing assessment or next action: ${id}`);
    check(Array.isArray(feature?.upstream) && feature.upstream.length > 0, `missing upstream evidence: ${id}`);
    for (const ref of Array.isArray(feature?.upstream) ? feature.upstream : []) {
      check(inspectedPaths.includes(ref?.path) && seenSources.has(ref?.path), `uninspected upstream evidence: ${id}: ${ref?.path}`);
      check(Number.isSafeInteger(ref?.line) && ref.line > 0, `invalid upstream line: ${id}`);
      cited.add(ref?.path);
    }
    check(Array.isArray(feature?.localEvidence) && feature.localEvidence.length > 0, `missing local evidence: ${id}`);
    for (const path of Array.isArray(feature?.localEvidence) ? feature.localEvidence : []) {
      if (!relativePath(path)) { errors.push(`unsafe local evidence path: ${id}: ${path}`); continue; }
      try { check(statSync(resolve(localRoot, path)).isFile(), `local evidence is not a file: ${path}`); }
      catch { errors.push(`missing local evidence file: ${path}`); }
    }
  }
  for (const id of familyIds) check(seen.has(id), `missing feature family: ${id}`);
  for (const chapter of chapters) {
    const path = `docs/DafnyRef/${chapter}.md`;
    check(cited.has(path), `uncited reference chapter: ${chapter}`);
  }
  for (const path of inspectedPaths) check(cited.has(path), `uncited inspected source: ${path}`);
  return errors;
}

if (process.argv[1] && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  try {
    const manifest = JSON.parse(readFileSync(resolve(root, 'docs/dafny-features.json'), 'utf8'));
    const errors = validateManifest(manifest);
    if (errors.length) { process.stderr.write(errors.join('\n') + '\n'); process.exitCode = 1; }
    else process.stdout.write(`Dafny inventory: ${manifest.features.length} families, ${manifest.upstream.sources.length} inspected paths; offline checks passed.\n`);
  } catch (error) { process.stderr.write(`${error.message}\n`); process.exitCode = 1; }
}
