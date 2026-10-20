import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, writeFileSync, rmSync, existsSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { execFileSync } from "node:child_process";
import { runSolidityTests, runTool, solidityFiles, testsPassed } from "./test-solidity.mjs";

test("timed-out tool jobs terminate their descendant processes", {skip:process.platform === 'win32'}, async () => {
  const dir = mkdtempSync(join(tmpdir(), 'solidity-timeout-'));
  const pidFile = join(dir, 'child.pid'), marker = join(dir, 'late-output');
  let child;
  try {
    const job = join(dir, 'job.mjs');
    const code = `process.on('SIGTERM',()=>{});require('node:fs').writeFileSync(${JSON.stringify(pidFile)},String(process.pid));setTimeout(()=>require('node:fs').writeFileSync(${JSON.stringify(marker)},'alive'),1200);setInterval(()=>{},1000)`;
    writeFileSync(job, `import {spawn} from 'node:child_process';
spawn(process.execPath,['-e',${JSON.stringify(code)}],{stdio:'ignore'});
process.on('SIGTERM',()=>{});
setInterval(()=>{},1000);`);
    assert.throws(() => runTool(process.execPath, [job], 500), e => {
      assert.match(e.message, /ETIMEDOUT/);
      assert.equal(e.tool.errorCode, 'ETIMEDOUT');
      assert.equal(e.tool.timedOut, true);
      assert.equal(e.tool.signal, 'SIGKILL');
      assert.equal(e.tool.exitCode, null);
      return true;
    });
    assert.ok(existsSync(pidFile), 'the child must have started before the timeout');
    child = Number(readFileSync(pidFile, 'utf8'));
    await new Promise(resolve => setTimeout(resolve, 1100));
    assert.equal(existsSync(marker), false, 'a descendant survived the failed tool job');
  } finally {
    if (child) { try { process.kill(child, 'SIGKILL'); } catch (e) { if (e.code !== 'ESRCH') throw e; } }
    rmSync(dir, {recursive:true, force:true});
  }
});

test("failed tool jobs retain exit and signal metadata even with output", () => {
  assert.throws(() => runTool(process.execPath,
    ['-e', 'console.warn("diagnostic"); process.exit(7)'], 2000), e => {
    assert.match(e.message, /exited 7/);
    assert.match(e.message, /diagnostic/);
    assert.equal(e.tool.exitCode, 7);
    assert.equal(e.tool.signal, null);
    assert.equal(e.tool.timedOut, false);
    return true;
  });
  if (process.platform !== 'win32') {
    assert.throws(() => runTool(process.execPath,
      ['-e', 'console.warn("diagnostic"); process.kill(process.pid, "SIGTERM")'], 2000), e => {
      assert.match(e.message, /terminated by SIGTERM/);
      assert.match(e.message, /diagnostic/);
      assert.equal(e.tool.exitCode, null);
      assert.equal(e.tool.signal, 'SIGTERM');
      assert.equal(e.tool.timedOut, false);
      return true;
    });
  }
});

test("discovery deduplicates overlapping inputs", () => {
  const files = solidityFiles(["tests/solc", "tests/solc/Runner.sol"]);
  assert.equal(files.filter(f => f.endsWith("/Runner.sol")).length, 1);
  assert.deepEqual(files, [...files].sort());
});

test("empty and untested suites cannot pass", () => {
  assert.equal(testsPassed({ results: [], errors: [] }), false);
  assert.equal(testsPassed({ results: [{ status: "skipped" }], errors: [] }), false);
  assert.throws(() => runSolidityTests([], { build: false }), /no Solidity/);
});

test("Solidity source through solc and kernel-checked proof search", () => {
  const checkpoints = [];
  const report = runSolidityTests(["tests/solc/Runner.sol"], { build: false, batchSize:3,
    onProgress: part => checkpoints.push(part.results.length) });
  assert.deepEqual(report.errors, []);
  assert.ok(checkpoints.length > 3);
  assert.equal(checkpoints.at(-1),report.results.length);
  assert.ok(checkpoints.every((n,i) => i === 0 || n >= checkpoints[i-1]));
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  assert.equal(status.passes, "proved");
  assert.equal(status.passesToo, "proved");
  assert.equal(status.staysOpen, "pending");
  assert.equal(status.ignored, "skipped");
  assert.equal(status.helper, "internal");
  assert.equal(status.assemblyGap, "unsupported");
  assert.equal(status.specified, "proved");
  assert.equal(status.badSpec, "pending");
  assert.equal(status.boxRevert, "proved");
  assert.equal(status.diamondRevert, "pending");
  assert.equal(status.breaksInvariant, "pending");
  assert.equal(status.constructor, "pending");
  assert.equal(status.preservesInvariant, "proved");
  assert.equal(status.payableSpec, "pending");
  assert.equal(status.misplacedInvariant, "unsupported");
  assert.equal(testsPassed(report), false);
});

test("fixed-array copy shapes preserve tails, snapshots and evaluation order", () => {
  const report = runSolidityTests(["tests/solc/ArrayShapes.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  assert.deepEqual(report.results.map(r => [r.function, r.status]), [
    ['fixedTail', 'proved'], ['dynamicLength', 'proved'], ['fieldTarget', 'proved'],
    ['sourceAndTargetEffects', 'proved'], ['pushedShape', 'proved'],
    ['falseTail', 'pending'], ['falseAlias', 'pending'], ['badSourceReverts', 'proved']
  ]);
  assert.equal(testsPassed(report), false);
});

test("implicit initializer omissions cannot silently pass", () => {
  const report = runSolidityTests(["tests/solc/InitGap.sol"], { build: false });
  assert.ok(report.errors.some(e => e.reason.includes("initializers are left out")));
  assert.equal(testsPassed(report), false);
});

test("file-level structs and library references retain declaration identity", () => {
  const report = runSolidityTests(["tests/solc/FileLevelStructs.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const rows = report.results.map(r => [r.contract, r.function, r.status]);
  assert.deepEqual(rows, [
    ['DifferentFileStruct', 'unsupportedShape', 'proved'],
    ['DifferentOwnStruct', 'unsupportedShape', 'proved'],
    ['FileLevelStructs', 'swaps', 'proved'],
    ['FileLevelStructs', 'falsePost', 'pending'],
    ['FilePairLib', 'swap', 'internal'],
    ['OwnStructWins', 'ownPair', 'proved']
  ]);
  assert.equal(testsPassed(report), false);
});

test("a nested struct of other widths is the contract's own; a hidden one stays out of reach", () => {
  const report = runSolidityTests(["tests/solc/FileLevelStructGaps.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  assert.deepEqual(report.results.filter(r => r.contract !== 'HiddenStructLib')
    .map(r => [r.contract, r.function, r.status]), [
    ['HiddenStructCaller', 'narrowLibraryMember', 'unsupported'],
    ['InvalidNestedStruct', 'narrowMember', 'pending']
  ]);
  assert.equal(testsPassed(report), false);
});

test("a contract's own structs: nested, a mapping member, an array of them, literals", () => {
  const report = runSolidityTests(["tests/solc/OwnStructs.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  assert.deepEqual(report.results.map(r => [r.function, r.status]), [
    ['nested', 'proved'], ['mappingMember', 'proved'], ['arrayOfStructs', 'proved'],
    ['literal', 'proved'], ['namedLiteral', 'proved'], ['narrowOverflow', 'proved'],
    ['falsePost', 'pending']
  ]);
  assert.equal(testsPassed(report), false);
});

test("a NatSpec expression cannot introduce another contract member", () => {
  const dir = mkdtempSync(join(tmpdir(), "solidity-clause-"));
  try {
    const source = join(dir, "BadClause.sol");
    writeFileSync(source, `pragma solidity ^0.8.0;
contract BadClause {
    /// @custom:key ensures false; requires false
    function bad() public pure {}
}`);
    const report = runSolidityTests([source], { build: false });
    assert.equal(report.errors.length, 1);
    assert.equal(testsPassed(report), false);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});

test("selection, listing and missing selections", () => {
  const options = { build: false, contract: "Runner", function: "passes" };
  const report = runSolidityTests(["tests/solc/Runner.sol"], options);
  assert.deepEqual(report.errors, []);
  assert.equal(report.results.length, 1);
  assert.equal(testsPassed(report), true);
  const listed = runSolidityTests(["tests/solc/Runner.sol"], { ...options, list: true });
  assert.equal(listed.results[0].status, "ready");
  assert.equal(testsPassed(listed, true), true);
  const missing = runSolidityTests(["tests/solc/Runner.sol"], { ...options, function: "absent" });
  assert.equal(missing.errors.length, 1);
  assert.equal(testsPassed(missing), false);
});

test("value push captures complex receivers once", () => {
  const report = runSolidityTests(["tests/solc/PushReceiver.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  assert.equal(report.results.length,5);
  assert.deepEqual(report.results.map(r => r.signature),
    ['nested()','falsePost()','effectfulReceiver()','oldTargetIndex()','falseTargetIndex()']);
  const status = Object.fromEntries(report.results.map(r => [r.function,r.status]));
  // An empty push of a reference element saves only the length and exposes the
  // old slot as it is (solkey d85018517f's `storagePushLengthSave`, e2319c57):
  // a claim about the pushed row fails from a well-formed entry state
  // (`nested_dirty`, `Examples/Tactics/PushReceiver.lean`), as solkey's
  // SYMBOLIC_TAIL_OPENS stay open. The runs from the initial state are pinned there.
  for (const fn of ['nested','falsePost','oldTargetIndex','falseTargetIndex'])
    assert.equal(status[fn],'pending',fn);
  // its search runs out of heartbeats on the open leaves
  assert.notEqual(status.effectfulReceiver,'proved');
});

test("push source captures preserve values, independent copies and mutable source names", () => {
  // Batches of three: as one Lean call the contract took 260 s (2026-10-20),
  // against the 300 s default subprocess timeout.
  const report = runSolidityTests(["tests/solc/PushSources.sol"], {build:false, batchSize:3});
  assert.deepEqual(report.errors, []);
  // Each source row is read from `rows.push()`'s exposed old slot (length-only
  // empty push, see "value push captures complex receivers once"): open, but for
  // the field written in place and the source index that reverts.
  assert.deepEqual(report.results.map(r => [r.function,r.status]), [
    ['primitive','pending'], ['primitiveField','proved'], ['primitiveFalse','pending'],
    ['referenceCopy','pending'], ['referenceFalse','pending'], ['selfCopy','pending'],
    ['effectfulSource','pending'], ['complexReceiver','pending'], ['badSourceIndex','proved'],
    ['freshSourceNames','pending']
  ]);
});

test("memory push copies atomically and resolves a changing receiver once", () => {
  const report = runSolidityTests(["tests/solc/MemoryPush.sol"], {build:false, batchSize:3});
  assert.deepEqual(report.errors, []);
  // `receiverUsesLength` indexes by `cube[0].length` after `cube.push()`, an
  // exposed old row (length-only empty push, see "value push captures complex
  // receivers once"): its claim is open, and its search runs out of heartbeats.
  const status = report.results.map(r => [r.function,r.status]);
  assert.notEqual(status[4][1], 'proved');
  status[4][1] = 'open';
  assert.deepEqual(status, [
    ['arrayCopy','proved'], ['arrayFalse','pending'], ['structCopy','proved'],
    ['recycledSlot','proved'], ['receiverUsesLength','open'], ['receiverFalse','pending'],
    ['complexMemorySource','proved'], ['complexMemoryFalse','pending'],
    ['badMemorySource','proved']
  ]);
});

test("storage-return bindings retain alias identity, effects and caller memory", () => {
  const report = runSolidityTests(["tests/solc/StorageReturns.sol"], {build:false, batchSize:3});
  assert.deepEqual(report.errors, []);
  // `returnsIndexed` reads the rows of `rows.push()`: open since the
  // length-only empty push (see "value push captures complex receivers once").
  assert.deepEqual(report.results.map(r => [r.function,r.status]), [
    ['valuesRef','internal'], ['otherRef','internal'], ['rowRef','internal'],
    ['allocatedRef','internal'], ['rejectedRef','internal'],
    ['bindsRoot','proved'], ['rebinds','proved'], ['returnsIndexed','pending'],
    ['heapGrowth','proved'], ['calleeReverts','proved'], ['falseCopy','pending'],
    ['receiverPush','proved'], ['receiverPushValue','proved'], ['receiverPop','proved'],
    ['receiverReadsAfterGetter','proved'], ['receiverReadsBeforeGetterFalse','pending'],
    ['receiverEffectfulOperand','proved']
  ]);
});

test("solc unchecked blocks wrap locally and restore checked arithmetic", () => {
  const report = runSolidityTests(["tests/solc/UncheckedImport.sol"],{build:false});
  assert.deepEqual(report.errors,[]);
  const status=Object.fromEntries(report.results.map(r => [r.function,r.status]));
  assert.equal(status.wraps,'proved');
  assert.equal(status.falsePost,'pending');
  assert.equal(status.scopeEnds,'proved');
});

test("mapping push and its returned alias preserve recycled entries", () => {
  const report = runSolidityTests(["tests/solc/MappingPush.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  assert.deepEqual(report.results.map(r => [r.function, r.status]), [
    ['boundPushDiamond', 'proved'],
    ['barePushKeepsEntries', 'proved'], ['boundPushKeepsEntries', 'proved']
  ]);
});

test("overloads use solc declaration identities and retain source signatures", () => {
  const report = runSolidityTests(["tests/solc/Overloads.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  assert.deepEqual(report.results.filter(r => r.function === 'pick').map(r => r.signature),
    ['pick(uint)', 'pick(bool)']);
  const status = Object.fromEntries(report.results.map(r => [r.signature, r.status]));
  assert.equal(status['choosesByDeclaration()'], 'proved');
  assert.equal(status['falsePost()'], 'pending');
  assert.equal(status['check(uint)'], 'proved');
  assert.equal(status['check(bool)'], 'proved');
  assert.equal(status['selectsDistinctSourceTypes()'], 'proved');
  const typed = report.results.filter(r => r.function === 'typedPick');
  assert.equal(typed.length, 3);
  assert.equal(new Set(typed.map(r => r.signature)).size, 3);
  const named = report.results.filter(r => r.function === 'namedType').map(r => r.signature);
  assert.equal(new Set(named).size, 2);
  assert.ok(named.some(s => s.includes('uint256Flavor')));
  const selected = runSolidityTests(["tests/solc/Overloads.sol"],
    {build:false, function:'check(bool)'});
  assert.deepEqual(selected.errors, []);
  assert.deepEqual(selected.results.map(r => r.signature), ['check(bool)']);
  assert.equal(testsPassed(selected), true);
});

test("constant and enum declarations are imported without storage slots", () => {
  const report = runSolidityTests(["tests/solc/ConstantsEnums.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  assert.equal(status.constantsInline, 'proved');
  assert.equal(status.enumsHaveOrdinals, 'proved');
  assert.equal(status.reservedLocal, 'proved');
  assert.equal(status.boundsAndValueTypes, 'proved');
  assert.equal(status.boundsFalsePost, 'pending');
  assert.equal(status.otherValueTypes, 'proved');
  assert.equal(status.falsePost, 'pending');
  assert.equal(status.immutableGap, 'proved');
});

test("enum NatSpec names respect declaration scope and preserve false obligations", () => {
  const report = runSolidityTests(["tests/solc/EnumSpecs.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  assert.deepEqual(report.results.map(r => [r.contract, r.function, r.status]), [
    ['EnumInvariant', 'set', 'proved'], ['EnumInvariant', 'falsePost', 'pending'],
    ['EnumLibrary', 'last', 'proved'],
    ['EnumSpecs', 'set', 'proved'], ['EnumSpecs', 'reset', 'proved'],
    ['EnumSpecs', 'qualifiedFile', 'proved'], ['EnumSpecs', 'otherScope', 'proved'],
    ['EnumSpecs', 'falsePost', 'pending'], ['EnumSpecs', 'quantifiedShadow', 'proved'],
    ['EnumSpecs', 'parameterShadow', 'proved'], ['EnumSpecs', 'loopAnnotation', 'proved'],
    ['EnumSpecs', 'libraryScope', 'proved']
  ]);
});

test("imported library helper annotations retain their defining enum scope", () => {
  const dir = mkdtempSync(join(tmpdir(), "solidity-enum-library-"));
  try {
    const ast = join(dir, "source.ast.json");
    execFileSync(process.execPath, ['scripts/solc-ast.mjs', '--source',
      'tests/solc/EnumSpecs.sol', '--out', ast, '--no-wrapper']);
    const check = join(dir, "Check.lean");
    writeFileSync(check, `import Solidity.Frontend.SolcJson
open Lean Solidity.Frontend
#eval do
  let text ← IO.FS.readFile ${JSON.stringify(ast)}
  let j ← IO.ofExcept (Json.parse text)
  let ast ← IO.ofExcept (j.getObjVal? "ast")
  let c ← IO.ofExcept (readContract ast "EnumSpecs" [] true)
  unless c.funMembers.any (fun (_, m) => m.startsWith "ensures \\\\result == 0; ") do
    throw (IO.userError "library helper annotation resolved outside its defining scope")
`);
    execFileSync('lake', ['--quiet', '--no-build', 'lean', check, '--', '--tstack=131072']);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});

test("a shadowed enum head cannot silently become a numeral", () => {
  const dir = mkdtempSync(join(tmpdir(), "solidity-enum-shadow-"));
  try {
    const source = join(dir, "EnumShadow.sol");
    writeFileSync(source, `pragma solidity ^0.8.26;
contract EnumShadow {
    enum Status { First, Last }
    /// @custom:key ensures Status.Last == 1
    function parameter(uint Status) public pure {}
    /// @custom:key ensures \\forall uint Status; Status.Last == 1
    function quantified() public pure {}
    /// @custom:key ensures \\forall uint «Status»; Status.Last == 1
    function escapedQuantified() public pure {}
    /// @custom:key ensures \\forall uint /- note -/ Status; Status.Last == 1
    function commentedQuantified() public pure {}
}`);
    const report = runSolidityTests([source], {build:false});
    assert.equal(report.results.length, 4);
    assert.ok(report.results.every(r => r.status === 'error'));
    assert.equal(testsPassed(report), false);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});

test("source types preserve overflow and declaration scope", () => {
  const report = runSolidityTests(["tests/solc/SourceTypes.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  assert.equal(status.signedAliasIsNotAlwaysPositive, 'pending');
  assert.equal(status.negativeAlias, 'proved');
  assert.equal(status.narrowOverflowCannotReturn, 'pending');
  assert.equal(status.narrowOverflowPanics, 'proved');
  assert.equal(status.signedOverflowCannotReturn, 'pending');
  assert.equal(status.signedOverflowPanics, 'proved');
  assert.equal(status.ternaryOverflowCannotReturn, 'pending');
  for (const name of ['ternaryOverflowPanics', 'ternaryUncheckedWraps',
    'ternaryExplicitWidening']) assert.equal(status[name], 'proved');
  // a branch's effects run in the branch taken (`hoist`'s conditional capture);
  // a conditional of literals has solc's mobile type (`mobileTy`)
  for (const name of ['ternaryEffectsOnce', 'nestedTypedConditionals', 'signedLiteralConditional',
    'nestedLiteralConditional', 'shortCircuitLiteralConditional']) assert.equal(status[name], 'proved', name);
  assert.equal(status.signedTernaryOverflowCannotReturn, 'pending');
});

test("source types: narrow elements, keys, values, struct members, locals and parameters", () => {
  const report = runSolidityTests(["tests/solc/NarrowNested.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  for (const name of ['valueOverflowPanics', 'valueInRange', 'elementTypeChecked', 'uncheckedWraps',
    'narrowKey', 'pushOverflowPanics', 'memberOverflowPanics', 'memberInRange', 'valueMemberPanics',
    'memberArrayPanics', 'memoryMemberPanics', 'aliasPanics', 'memoryPanics', 'copyPanics',
    'memoryParamPanics', 'memoryWraps', 'modifierParam', 'pushArithInRange', 'pushArithPanics',
    'ternaryAliasPanics', 'ternaryAliasInRange', 'ternaryArgumentPanics']) assert.equal(status[name], 'proved', name);
  // its elements' range is a premise (`Problem.callPre`) the closer does not instantiate
  assert.equal(status.abiElementInRange, 'pending');
});

test("modifiers use the existing inliner for calls and root obligations", () => {
  const report = runSolidityTests(["tests/solc/Modifiers.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  for (const name of ['constructor', 'arguments', 'resumesAfterReturn',
    'firstListedOutermost', 'directApplication', 'argumentEvaluation',
    'localsPerApplication', 'multiplePlaceholders', 'internalCallFromModifier',
    'unnamedParameter', 'unnamedArgumentStillRuns', 'narrowArrayModifier',
    'narrowArrayModifierPanics', 'storageArrayModifierPanics']) {
    assert.equal(status[name], 'proved', name);
  }
  assert.equal(status.falsePost, 'pending');
  // a narrow modifier parameter is a local of its type: `x += 1` at `255` panics
  assert.equal(status.narrowModifierGap, 'pending');
});

test("free and library calls resolve by declaration with attached receivers", () => {
  const report = runSolidityTests(["tests/solc/LibraryCalls.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  for (const name of ['ownCalls', 'declarationsStayDistinct', 'attachedAndNamed', 'receiverOnce', 'tupleCalls']) {
    assert.equal(status[name], 'proved', name);
  }
  assert.equal(status.falsePost, 'pending');
  // a recursive call (`Stmt.callRec`) whose result is read past it: by its
  // callee's `/// @custom:key ensures` contract (`rec_auto`)
  assert.equal(status.recursionGap, 'proved');
});

test("recursion: calls by their contracts, proved by induction over the frames", () => {
  // tests/solc/Recursion.sol: each recursive call by its callee's
  // `/// @custom:key` contract (`true`/`true` without one), the contract by
  // induction over the frames (`rec_auto`, docs/kernel-port.md "Recursion")
  const report = runSolidityTests(["tests/solc/Recursion.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  for (const name of ['countdown', 'sumTo', 'sumToSix', 'even', 'odd', 'evenFour',
    'fib', 'fibOne', 'divmod', 'divmodSeven']) {
    assert.equal(status[name], 'proved', name);
  }
  // the triangular sum's step is nonlinear, past the closer
  assert.equal(status.sum, 'pending');
  assert.equal(status.sumThree, 'pending');
  assert.equal(status.falsePost, 'pending');
  // under the callback reading (O7) no rule steps over a recursive call
  assert.equal(status.callThenCount, 'pending');
});

test("root primitive push bindings and empty user calls parse unambiguously", () => {
  const report = runSolidityTests(["tests/solc/PushBindings.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  assert.equal(status.rootBinding, 'proved');
  assert.equal(status.falsePost, 'pending');
  // A pushed reference slot is exposed as it is (length-only empty push, see
  // "value push captures complex receivers once"): its contents are open.
  for (const name of ['fixedReturn', 'dynamicReturn', 'structReturn']) {
    assert.equal(status[name], 'pending', name);
  }
  assert.equal(status.falseReferencePost, 'pending');
});

test("fresh arrays expose their written size and initialized elements", () => {
  const report = runSolidityTests(["tests/solc/NewArrays.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  for (const name of ['storageRoot', 'sizeOnce', 'memorySizeOnce', 'receiverAfterSize', 'symbolicSize']) {
    assert.equal(status[name], 'proved', name);
  }
  // Reference-element copy reads remain a required migration gap.
  assert.equal(status.nestedDefaults, 'pending');
  assert.equal(status.falsePost, 'pending');
  assert.equal(status.emptyRead, 'pending');
});

test("the full frozen TestSuite compiles its testing function table within default limits", () => {
  const report = runSolidityTests([
    "tests/migration/solkey/keyext.solidity.examples/TestSuite.sol",
  ], {build:false, list:true, renaming:{Triple:'FixedTriple'}});
  assert.deepEqual(report.errors, []);
  const rows = report.results.filter(r => r.contract === 'TestSuite');
  // TestSuite at solkey 473da8944c (`TestSuite/Report.lean`): 617 functions,
  // 563 obligations (546 derived, 17 pending) and 54 others.
  assert.equal(rows.length, 617);
  const count = s => rows.filter(r => r.status === s).length;
  assert.deepEqual([count('ready'), count('internal'), count('skipped'), count('excluded')],
    [563, 51, 2, 1]);
  const status = Object.fromEntries(rows.map(r => [r.function, r.status]));
  assert.equal(status.storagePushMemoryCopySource, 'ready');
  assert.equal(status.storagePushCompoundSigned, 'ready');
  assert.equal(status.whileCountsUp, 'ready');
  assert.equal(status.storagePushPopCallReceiver, 'ready');
  assert.equal(status.addmodMulmod, 'ready');
  assert.equal(status.indexParameter, 'ready');
  assert.equal(status.storageStructParameter, 'ready');
  assert.equal(status.storageMappingParameter, 'ready');
});

test("reference parameters preserve locations, copies and initialized source inputs", () => {
  const report = runSolidityTests(["tests/solc/ReferenceParameters.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  for (const fn of ["storageAndMemory", "nestedStorageReturn", "allocationArgument", "initializedInput"]) {
    assert.equal(status[fn], "proved", fn);
  }
  // Executable kernel regressions cover the copy's evaluation order. Symbolic
  // closure of that larger update remains open.
  assert.equal(status.copiesBeforeEffects, "pending");
});

test("quantified consequents parse and omitted specification bodies stay local", () => {
  const report = runSolidityTests(["tests/solc/SpecImport.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const rows = Object.fromEntries(report.results.filter(r => r.contract === "SpecImport")
    .map(r => [r.function, r]));
  assert.equal(rows.universalConsequent.status, "proved");
  assert.equal(rows.existentialConsequent.status, "proved");
  assert.equal(rows.falseUniversal.status, "pending");
  assert.equal(rows.renamedSpec.status, "proved");
  assert.equal(rows.omittedCaller.status, "pending");
  assert.equal(rows.omittedBody.status, "unsupported");
  assert.equal(rows.omittedModifier.status, "unsupported");
  assert.equal(rows.stillChecked.status, "pending");
  const ctor = Object.fromEntries(report.results.filter(r => r.contract === "SpecCtorGap")
    .map(r => [r.function, r]));
  assert.equal(ctor.constructor.status, "proved");
  assert.equal(ctor.stillChecked.status, "pending");
  const types = Object.fromEntries(report.results.filter(r => r.contract === "OmittedTypes")
    .map(r => [r.function, r]));
  assert.equal(types.unrelated.status, "proved");
  assert.equal(types.stillChecked.status, "pending");
  assert.equal(types.readsString.status, "unsupported");
  // a narrow element, key or value is modelled (`expandStateTyW`): `narrow[0]`
  // may be past the end, and `narrow.length == 0` need not hold
  for (const fn of ["readsNarrowKey", "readsNarrowValue"]) assert.equal(types[fn].status, "proved", fn);
  for (const fn of ["readsNarrow", "specReadsNarrow"]) assert.equal(types[fn].status, "pending", fn);
});

test("specification parameter renaming preserves scopes, distinct names and frames", () => {
  const report = runSolidityTests(["tests/solc/SpecBindings.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const rows = Object.fromEntries(report.results.filter(r => r.contract === "SpecBindings")
    .map(r => [r.function, r]));
  for (const fn of ["keywords", "oldParameter", "stateShadow", "distinctParameters", "namedReturn",
    "returnScope", "existentialShadow", "quantifiedSibling", "avoidCapture", "memberLabel",
    "splitMemberLabel", "assignableIndex", "bodyLocal", "escaped", "comments", "parameterLoop",
    "localLoop", "loopScopeExit", "blockScopeExit", "returnLoop", "modifierLoop", "externalValue",
    "tryScopeExit"]) {
    assert.equal(rows[fn].status, "proved", fn);
  }
  for (const fn of ["falseStateShadow", "falseDistinctParameters", "falseOldReturnScope",
    "falseQuantifiedShadow", "falseQuantifiedSibling", "falseCapture", "falseDeepCapture", "falseFrame", "stillChecked"]) {
    assert.equal(rows[fn].status, "pending", fn);
  }
  assert.equal(rows.malformedRenamed.status, "unsupported");
  assert.match(rows.malformedRenamed.reason, /expected end of input/);
  assert.equal(rows.unknownLoopName.status, "unsupported");
  assert.match(rows.unknownLoopName.reason, /unknown name from_/);
  assert.equal(report.results.find(r => r.contract === "SpecBindingConstructor").status, "proved");
  assert.equal(report.results.find(r => r.contract === "SpecBindingInherited").status, "proved");
});

test("unsupported ledger frames stay local and retain their caller gaps", () => {
  const report = runSolidityTests(["tests/solc/NetAssignable.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const rows = Object.fromEntries(report.results.map(r => [r.function, r]));
  for (const fn of ["ledgerGap", "mixedGap"]) {
    assert.equal(rows[fn].status, "unsupported", fn);
    assert.match(rows[fn].reason, /ledger locations in assignable/);
  }
  assert.equal(rows.callerGap.status, "unsupported");
  assert.equal(rows.unrelated.status, "proved");
  assert.equal(rows.falseUnrelated.status, "pending");
  assert.equal(rows.bareStateName.status, "proved");
  assert.equal(rows.builtinLedger.status, "proved");
  assert.equal(rows.falseBuiltinLedger.status, "pending");
  assert.equal(rows.constantLedgerGap.status, "unsupported");
  assert.match(rows.constantLedgerGap.reason, /ledger locations in assignable/);
  assert.equal(rows.builtinEscapes.status, "proved");
});

test("constant specifications preserve units, lexical visibility and unsigned types", () => {
  const run = contract => runSolidityTests(["tests/solc/SpecConstants.sol"], {build:false, contract});
  const base = run("SpecConstants");
  assert.deepEqual(base.errors, []);
  const rows = Object.fromEntries(base.results.map(r => [r.function, r]));
  assert.equal(rows.exactUnits.status, "proved");
  assert.equal(rows.falseConstant.status, "pending");
  for (const fn of ["boundedLoop", "quantifiedShadow"]) {
    assert.equal(rows[fn].status, "unsupported", fn);
  }
  assert.match(rows.boundedLoop.reason, /loop's invariant needs a statement/);
  assert.equal(rows.parameterShadow.status, "pending");
  const other = run("OtherConstants");
  assert.deepEqual(other.errors, []);
  assert.equal(other.results[0].status, "proved");
  const defining = run("PrivateConstants");
  assert.deepEqual(defining.errors, []);
  assert.equal(defining.results[0].status, "proved");
  const inherited = run("InheritedConstants");
  assert.deepEqual(inherited.errors, []);
  const inheritedRows = Object.fromEntries(inherited.results.map(r => [r.function, r]));
  assert.equal(inheritedRows.inheritedVisible.status, "proved");
  assert.equal(inheritedRows.callDefiningScope.status, "proved");
  assert.equal(inheritedRows.privateIsHidden.status, "unsupported");
  const typed = run("ConstantTypes");
  assert.equal(typed.results[0].status, "error");
  assert.equal(testsPassed(typed), false);
  assert.match(typed.errors.map(e => e.reason).join("\n"), /operands of \+ of types uint and int/);
  const isolated = run("ConstantIsolation");
  assert.ok(isolated.results.every(r => r.status === "error"));
  assert.equal(testsPassed(isolated), false);
  const isolationErrors = isolated.errors.map(e => e.reason).join("\n");
  assert.match(isolationErrors, /unknown name LIMIT/);
  assert.match(isolationErrors, /unknown name LIB_ONLY/);
});

test("specifications retain the contract address and its ledger snapshot", () => {
  const report = runSolidityTests(["tests/solc/SpecSelf.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const rows = Object.fromEntries(report.results.map(r => [r.function, r]));
  for (const fn of ["identity", "snapshot", "unchangedLedger", "parameter", "returned"]) {
    assert.equal(rows[fn].status, "proved", fn);
  }
  for (const fn of ["falseAddress", "falseLedger"]) {
    assert.equal(rows[fn].status, "pending", fn);
  }
});

test("inheritance preserves virtual, static, named and modifier dispatch", () => {
  const report = runSolidityTests(["tests/solc/Inheritance.sol"], {build:false, contract:"Inherited"});
  assert.deepEqual(report.errors, []);
  const rows = Object.fromEntries(report.results.map(r => [r.function, r]));
  for (const fn of ["dispatch", "staticCall", "staticStillDispatches", "namedCall", "privateCall",
    "modified", "staticModifier", "inheritedStruct", "inheritedEnumSpec", "inheritedEnumModifier", "externalValue",
    "superCall", "superNamed"]) {
    assert.equal(rows[fn].status, "proved", fn);
  }
  assert.equal(rows.falseDispatch.status, "pending");
  assert.equal(rows.falseInheritedEnumSpec.status, "pending");
  // a self-call `try` runs its callee (O8): `r == 2` is proved
  assert.equal(rows.externalStaysExternal.status, "proved");
  assert.equal(rows.falseSuper.status, "pending");
  assert.equal(rows.viaBase, undefined); // inherited helpers have no new independent row
  const init = runSolidityTests(["tests/solc/Inheritance.sol"], {build:false, contract:"InitDiamond"});
  assert.deepEqual(init.errors, []);
  // The closer reads the deployment's empty storage (`SFun.mt`), so the
  // constructor's assertions close automatically too.
  assert.equal(init.results.find(r => r.function === "constructor").status, "proved");
});

test("inheritance resolves super in the most-derived C3 order", () => {
  const report = runSolidityTests(["tests/solc/Inheritance.sol"], {build:false, contract:"SuperDiamond"});
  assert.deepEqual(report.errors, []);
  const rows = Object.fromEntries(report.results.map(r => [r.function, r]));
  assert.equal(rows.diamondSuper.status, "proved");
  assert.equal(rows.staticRight.status, "proved");
  assert.equal(rows.falseDiamondSuper.status, "pending");
});

test("constructor and function quotients close as solkey's sdiv_axiom reads them", () => {
  const report = runSolidityTests(["tests/solc/CtorDivision.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [`${r.contract}.${r.function}`, r.status]));
  for (const row of ["CtorDivision.constructor", "CtorDivision.half", "CtorDivisionLiteral.constructor",
    "CtorModulo.constructor"]) assert.equal(status[row], "proved", row);
  assert.equal(status["CtorDivisionFalse.constructor"], "pending");
});

test("inheritance runs base constructors in solc's legacy order", () => {
  for (const [contract, status] of [["CtorLeaf", "proved"], ["CtorFalse", "pending"],
    ["CtorImplicit", "proved"], ["CtorUnnamedChild", "proved"]]) {
    const report = runSolidityTests(["tests/solc/Inheritance.sol"], {build:false, contract});
    assert.deepEqual(report.errors, [], contract);
    assert.equal(report.results.find(r => r.function === "constructor")?.status, status, contract);
  }
});

test("inheritance conjoins inherited contract invariants", () => {
  const report = runSolidityTests(["tests/solc/Inheritance.sol"], {build:false, contract:"GuardedChild"});
  assert.deepEqual(report.errors, []);
  const rows = Object.fromEntries(report.results.map(r => [r.function, r]));
  assert.equal(rows.bump.status, "proved");
  assert.equal(rows.breaksBase.status, "pending");
  assert.equal(rows.breaksOwn.status, "pending");
});

test("unmodelled inheritance boundaries are rejected instead of omitted", () => {
  const report = runSolidityTests(["tests/solc/InheritanceGaps.sol"], {build:false, contract:"NameGap"});
  assert.ok(report.errors.some(e => /a specification reads: distinct storage roots/.test(e.reason)));
  assert.equal(testsPassed(report), false);
});

test("inheritance renames a base's private variable of a later one's name", () => {
  const report = runSolidityTests(["tests/solc/InheritanceGaps.sol"], {build:false, contract:"NameShadow"});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  assert.equal(status.f, "proved");
  assert.equal(status.falseShared, "pending");
});

test("inheritance wraps each constructor's body in its own modifiers, after its bases", () => {
  const report = runSolidityTests(["tests/solc/InheritanceCtors.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [`${r.contract}.${r.function}`, r.status]));
  for (const c of ["ModLeaf", "CtorModLeaf", "CtorReturnLeaf", "SuperMod1", "SuperModCtor", "SuperModArg"])
    assert.equal(status[`${c}.constructor`], "proved", c);
  for (const c of ["CtorModFalse", "CtorReturnFalse"]) assert.equal(status[`${c}.constructor`], "pending", c);
  // `super` in a modifier's body, the modifier applied in the contract and below it
  for (const f of ["SuperModBody.f", "SuperModInherited.h"]) assert.equal(status[f], "proved", f);
});

test("native modular builtins retain wide results, failure priority and source effects", () => {
  const report = runSolidityTests(["tests/solc/Modular.sol"], {build:false, batchSize:3});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  for (const fn of ["wide", "zeroBeforeBad", "ordered", "capturedRead", "usesDeclaredFunction"]) {
    assert.equal(status[fn], "proved", fn);
  }
  assert.equal(status.positiveBad, "pending");
});

test("specification negation widens unsigned operands only beside the ledger", () => {
  const report = runSolidityTests(["tests/solc/SpecNegation.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const rows = Object.fromEntries(report.results.map(r => [r.function, r]));
  for (const fn of ["ledgerEquation", "unsignedNegation", "reversedNegation", "negativeLiteral",
    "oldUnsignedNegation", "typedConstantNegation", "negativeLedger", "maximumUnsignedNegation"]) {
    assert.equal(rows[fn].status, "proved", fn);
  }
  assert.equal(rows.falseNegation.status, "pending");
  assert.equal(rows.checkedInnerArithmetic.status, "pending");
});

test("solkey's solc/open ports close except where the model says why not", () => {
  // tests/solc/open: solkey bab7200276's `keyext.solidity.examples/solc/open`,
  // less `SolcLoopsOpen.sol` (its loops are past the search budget). Each row
  // left open is open for a reason the model states, not a gap of the import:
  const open = {
    // the callee is the contract itself only at the harness address
    // (0x…DeaDBeef), which no obligation fixes (`--self-address`, below)
    tryCatchExactReturn: "pending", trySuccessRunsCallee: "pending",
    tryMultipleCatchClausesSuccess: "pending", tryNestedGetter: "pending",
    // a value call to the parameter runs `receive` only where it is the
    // contract, which no obligation fixes (`--self-address`, below)
    callRunsReceive: "pending",
    // false on the EVM: at the harness address the callee writes `ix = 42`,
    // which the run executes (`docs/options.md`, O8); the value call's
    // callee may write the state under the callback reading (O7)
    trySuccessKeepsStorageUnsound: "pending", callKeepsStorageUnsound: "pending",
    // false on the EVM: `t ? 63 : 255` is a `uint8`, so `63 + 255` panics
    // (`0x11`); the model reverts there (`SolcOpen.ternaryLiteralOverflow`)
    ternaryLiteralOverflow: "pending",
  };
  // `functionsRecursiveUnbounded` proves: its recursive call by the contract
  // true/true over the 1024 frames of the unrolling (`rec_auto`, kernel-port.md
  // "Recursion"); `callWithoutCodeReverts` proves: address 0 has no code (O8);
  // `msgValueArith`: `msg.value < 2^128`, a chain fact (`Problem.callPre`).
  const files = ["SolcArithmeticOpen", "SolcConstructorsOpen", "SolcFunctionCallsOpen",
    "SolcHigherLevelOpen", "SolcPaymentsOpen", "SolcSmtControlFlowOpen", "SolcTypesOpen"]
    .map(f => `tests/solc/open/${f}.sol`);
  const report = runSolidityTests(files, {build:false});
  assert.deepEqual(report.errors, []);
  const rows = report.results.filter(r => !["internal", "skipped"].includes(r.status));
  assert.equal(rows.length, 51);
  const expected = new Map(Object.entries(open));
  for (const r of rows) assert.equal(r.status, expected.get(r.function) ?? "proved", r.function);
});

test("solc/open self-calls prove at the harness address (--self-address)", () => {
  // the same file, every obligation assuming `address(this) == 0x…DeaDBeef`
  // (`Problem.selfPre`): a `try` of the pinned parameter runs the callee
  const report = runSolidityTests(["tests/solc/open/SolcPaymentsOpen.sol"],
    {build:false, selfAddress: "0x00000000000000000000000000000000DeaDBeef"});
  assert.deepEqual(report.errors, []);
  const rows = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  // a `catch` goal assumes the callee fails (O8); a value call to the
  // contract runs `receive`; `msg.value < 2^128` (a chain fact)
  for (const fn of ["trySuccessRunsCallee", "tryMultipleCatchClausesSuccess", "tryNestedGetter",
    "callWithoutCodeReverts", "tryArgumentSideEffect", "tryCatchExactReturn", "callRunsReceive",
    "msgValueArith"]) {
    assert.equal(rows[fn], "proved", fn);
  }
  // the unsound claims are false on the EVM: the callee writes the state
  for (const fn of ["trySuccessKeepsStorageUnsound", "callKeepsStorageUnsound"]) {
    assert.equal(rows[fn], "pending", fn);
  }
});

test("self-calls of the contract run their callee (tests/solc/SelfCalls.sol)", () => {
  const report = runSolidityTests(["tests/solc/SelfCalls.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const rows = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  for (const fn of ["tryReturnInSuccess", "trySuccessRunsCallee", "tryMultipleCatchClausesSuccess",
    "tryNestedGetter", "callWithoutCodeReverts", "tryCatchExactReturn", "callRunsReceive"]) {
    assert.equal(rows[fn], "proved", fn);
  }
});

test("an obligation whose callee may write the state is read with callbacks", () => {
  // docs/options.md O7: `ValidT .noCallback` where a `try` of a callee not
  // declared view/pure or a low-level call is reached, `⊢` elsewhere
  const report = runSolidityTests(["tests/solc/CallbackReading.sol"], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(r => [r.function, r.status]));
  assert.equal(status.localKept, "proved");
  assert.equal(status.staticKept, "proved");
  assert.equal(status.storageLost, "pending");
  assert.equal(status.valueCallLost, "pending");
});
