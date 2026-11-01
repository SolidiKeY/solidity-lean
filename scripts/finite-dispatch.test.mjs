import {test} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync, writeFileSync, readFileSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';
import {runSolidityTests} from './test-solidity.mjs';

// Uses the pinned compiler and the actual declaration reader/admission scan.
// No build is started: rebuild the modified frontend before running this file.
function scopeCheck(source, body, mutate = '') {
  const dir = mkdtempSync(join(tmpdir(), 'solidity-finite-dispatch-'));
  try {
    const input = join(dir, 'FiniteDispatch.sol');
    const fixture = join(dir, 'FiniteDispatch.ast.json');
    const check = join(dir, 'Check.lean');
    writeFileSync(input, '// SPDX-License-Identifier: MIT\npragma solidity ^0.8.0;\n' + source);
    execFileSync(process.execPath, ['scripts/solc-ast.mjs', '--source', input,
      '--out', fixture, '--no-wrapper'], {stdio:'pipe'});
    writeFileSync(check, `import Solidity.Frontend.SolcJson
open Lean Solidity.Frontend
private def put (j : Json) (key : String) (value : Json) : Json :=
  Json.mkObj ((key, value) :: ((j.getObj?.toOption.map (·.toList)).getD []).filter (·.1 != key))
partial def modifyTree (f : Json → Json) : Json → Json
  | .obj fields => f (Json.mkObj (fields.toList.map fun (k, v) => (k, modifyTree f v)))
  | .arr values => .arr (values.map (modifyTree f))
  | other => f other
#eval do
  let fixture ← IO.ofExcept (Json.parse (← IO.FS.readFile ${JSON.stringify(fixture)}))
  let original ← IO.ofExcept (fixture.getObjVal? "ast")
  let provenance ← IO.ofExcept (Source.read fixture original)
  let ast := original
  ${mutate}
  let contract : SolcContract ← IO.ofExcept (readContract ast "C" [] true
    (scanSource := Admission.scan ast provenance))
  let row (name : String) : Option SolcFun := contract.funs.find? (·.name == name)
  ${body}
`);
    runLean(check);
  } finally { rmSync(dir, {recursive:true, force:true}); }
}

// Run the real import command for specification and native-model checks.
// This deliberately uses Import's private production callbacks through solc_import.
function productionCheck(source, body, viaIR = false) {
  const dir = mkdtempSync(join(tmpdir(), 'solidity-production-dispatch-'));
  try {
    const input = join(dir, 'FiniteDispatch.sol');
    const fixture = join(dir, 'FiniteDispatch.ast.json');
    const check = join(dir, 'Check.lean');
    writeFileSync(input, '// SPDX-License-Identifier: MIT\npragma solidity ^0.8.0;\n' + source);
    execFileSync(process.execPath, ['scripts/solc-ast.mjs', '--source', input,
      '--out', fixture, '--no-wrapper', ...(viaIR ? ['--via-ir'] : [])], {stdio:'pipe'});
    let hash = 0xcbf29ce484222325n;
    for (const byte of readFileSync(fixture))
      hash = BigInt.asUintN(64, (hash ^ BigInt(byte)) * 0x100000001b3n);
    writeFileSync(check, `import Solidity.Tools.Upstream
open Solidity Solidity.Frontend
solc_import "FiniteDispatch.ast.json" hash 0x${hash.toString(16)} as Imported.C testing
${body}
`);
    runLean(check);
  } finally { rmSync(dir, {recursive:true, force:true}); }
}

// Lean's own errors, not the warnings of replayed modules, in a failure.
function runLean(check) {
  try {
    execFileSync('lake', ['--quiet', '--no-build', 'lean', check, '--', '--tstack=131072'],
      {stdio:'pipe', encoding:'utf8', timeout:180000});
  } catch (e) {
    if (process.env.FINITE_DISPATCH_LOG)
      writeFileSync(process.env.FINITE_DISPATCH_LOG, String(e.stdout ?? '') + String(e.stderr ?? ''));
    const lines = (String(e.stdout ?? '') + String(e.stderr ?? '')).split('\n')
      .filter(l => /error|mismatch|broken|userError/.test(l));
    e.message = lines.join('\n').slice(0, 4000) || e.message;
    throw e;
  }
}

function diagnostic(name, code) {
  return `unless (row ${JSON.stringify(name)}).any (fun (r : SolcFun) =>
      (r.sourceScope.diagnostic?.map (fun (d : Source.Diagnostic) => d.name)) == some \`${code}) do
    throw (IO.userError "wrong or absent dispatch diagnostic for ${name}")`;
}

test('finite dispatch preserves the original FunctionTypes positive and negative verdicts', () => {
  const report = runSolidityTests(['tests/solc/FunctionTypes.sol'], {build:false});
  assert.deepEqual(report.errors, []);
  const status = Object.fromEntries(report.results.map(row => [row.function, row.status]));
  for (const name of ['applyAndCompose','localValue','storedByFlag','returnedValue',
    'unassignedPanics','memberValue','deletedPanics','equality','memberCall','elementCall',
    'callResultCall','ext','externalSelector','recursionThroughValue','externalValue'])
    assert.equal(status[name], 'proved', name);
  assert.equal(status.unassignedDiamond, 'pending');
  assert.equal(status.falsePost, 'pending');
});

test('finite dispatch admits a typed scalar caller and retains inherited declaration identities', () => {
  scopeCheck(`contract Base {
    function target(uint x) internal pure virtual returns(uint) { return x; }
  }
  contract C is Base {
    function target(uint x) internal pure override returns(uint) { return x + 1; }
    function entry() public pure {
      function(uint) internal pure returns(uint) h = target;
      assert(h(2) == 3);
    }
  }`, `unless (row "entry").any (fun (r : SolcFun) => r.body.isOk &&
      r.sourceScope.diagnostic?.isNone && !r.calls.isEmpty) do
    throw (IO.userError "finite inherited internal dispatch was not admitted")`);
});

test('dynamic target bodies and transitive calls cannot evade admission', () => {
  scopeCheck(`contract C {
    function clean(uint x) internal pure returns(uint) { return x; }
    function forbidden() internal view returns(uint) { return block.number; }
    function poison(uint x) internal view returns(uint) { return x + forbidden(); }
    function entry(bool b) public view {
      function(uint) internal view returns(uint) h = b ? clean : poison;
      h(1);
    }
  }`, diagnostic('entry', 'solidity.blockField.number'));
});

test('unused native-compatible targets are conservatively scanned', () => {
  scopeCheck(`contract C {
    function clean(uint x) internal pure returns(uint) { return x; }
    function poison(uint x) internal view returns(uint) { return x + block.number; }
    function entry() public pure {
      function(uint) internal pure returns(uint) h = clean;
      h(1);
    }
  }`, diagnostic('entry', 'solidity.blockField.number'));
});

test('function-value calls inside modifiers include target modifiers', () => {
  scopeCheck(`contract C {
    modifier excluded() { require(block.number != 0); _; }
    function target(uint x) internal view excluded returns(uint) { return x; }
    modifier dynamic() {
      function(uint) internal view returns(uint) h = target;
      h(1); _;
    }
    function entry() public dynamic {}
  }`, diagnostic('entry', 'solidity.blockField.number'));
});

test('production specification admission follows dynamic target specifications', () => {
  productionCheck(`contract C {
    /// @custom:key requires block.number == 0
    function poison(uint x) internal pure returns(uint) { return x; }
    function entry() public pure {
      function(uint) internal pure returns(uint) h = poison;
      h(1);
    }
  }`, `#guard (Imported.C.report.find? (·.name == "entry")).any fun row =>
  row.admissionChecked && row.status == .excluded &&
    (row.sourceDiagnostic.map (·.name)) == some \`solidity.blockField.number`);
});

test('an address/uint collision in the native key is rejected without dropping its target', () => {
  scopeCheck(`contract C {
    function addressTarget(address x) internal pure returns(uint) { return uint160(x); }
    function uintTarget(uint x) internal pure returns(uint) { return x; }
    function entry() public pure {
      function(uint) internal pure returns(uint) h = uintTarget;
      h(1);
    }
  }`, diagnostic('entry', 'solidity.functionDispatch'));
});

test('unknown function-value type metadata fails closed', () => {
  scopeCheck(`contract C {
    function target(uint x) internal pure returns(uint) { return x; }
    function entry() public pure {
      function(uint) internal pure returns(uint) h = target;
      h(1);
    }
  }`, diagnostic('entry', 'solidity.functionDispatch'), `let ast := modifyTree (fun node =>
    if J.kind node == "Identifier" && J.str? node "name" == some "h" then
      put node "typeDescriptions" (Json.mkObj []) else node) ast`);
});

test('missing candidate signature metadata cannot silently remove a possible target', () => {
  scopeCheck(`contract C {
    function target(uint x) internal pure returns(uint) { return x; }
    function entry() public pure {
      function(uint) internal pure returns(uint) h = target;
      h(1);
    }
  }`, diagnostic('entry', 'solidity.functionDispatch'), `let ast := modifyTree (fun node =>
    if J.kind node == "VariableDeclaration" && J.str? node "name" == some "x" then
      put node "typeName" (Json.mkObj []) else node) ast`);
});

test('memory reference arguments are admitted by native dispatch since lane CF2', () => {
  // Before lane CF2 this was the explicit refusal; calldata and other
  // reference shapes remain refused ('other reference signatures remain refused').
  scopeCheck(`contract C {
    function target(uint[] memory xs) internal pure returns(uint) { return xs.length; }
    function entry(uint[] memory xs) public pure {
      function(uint[] memory) internal pure returns(uint) h = target;
      h(xs);
    }
  }`, `unless (row "entry").any (fun (r : SolcFun) => r.body.isOk &&
      r.sourceScope.diagnostic?.isNone) do
    throw (IO.userError "a memory-array argument was not admitted")`);
});

test('private candidates cannot become self external targets through native type erasure', () => {
  scopeCheck(`contract C {
    function hidden(uint x) private pure returns(uint) { return x; }
    function target(uint x) external pure returns(uint) { return x; }
    function entry() public view {
      function(uint) external pure returns(uint) h = this.target;
      h(1);
    }
  }`, diagnostic('entry', 'solidity.functionDispatch'));
});

test('external inherited selector renaming is an explicit boundary', () => {
  scopeCheck(`contract Base {
    function target(uint x) external pure returns(uint) { return x; }
  }
  contract C is Base {
    function entry() public view {
      function(uint) external pure returns(uint) h = this.target;
      h(1);
    }
  }`, diagnostic('entry', 'solidity.functionDispatch'));
});

test('initializer dispatch is deployment scope and does not leak into ordinary entry points', () => {
  scopeCheck(`contract C {
    function target(uint x) internal view returns(uint) { return x + block.number; }
    function(uint) internal view returns(uint) h = target;
    uint result = h(1);
    constructor() {}
    function entry() public pure { assert(true); }
  }`, `unless contract.ctor.any (fun (r : SolcFun) =>
      (r.sourceScope.diagnostic?.map (fun (d : Source.Diagnostic) => d.name)) == some \`solidity.blockField.number) do
    throw (IO.userError "initializer dispatch target was omitted from deployment scope")
  unless (row "entry").any (fun (r : SolcFun) => r.body.isOk && r.sourceScope.diagnostic?.isNone) do
    throw (IO.userError "initializer target leaked into an ordinary function")`);
});

test('base constructor dynamic targets enter the composite constructor closure', () => {
  scopeCheck(`contract Base {
    function target(uint x) internal view returns(uint) { return x + block.number; }
    constructor() {
      function(uint) internal view returns(uint) h = target;
      h(1);
    }
  }
  contract C is Base { constructor() {} }
  `, `unless contract.ctor.any (fun (r : SolcFun) =>
      (r.sourceScope.diagnostic?.map (fun (d : Source.Diagnostic) => d.name)) == some \`solidity.blockField.number) do
    throw (IO.userError "base constructor dynamic target was omitted")`);
});

test('zero-argument void dispatch cannot silently omit receive and fallback candidates', () => {
  for (const special of ['receive() external payable {}', 'fallback() external payable {}'])
    scopeCheck(`contract C {
      ${special}
      function target() internal pure {}
      function entry() public pure {
        function() internal pure h = target;
        h();
      }
    }`, diagnostic('entry', 'solidity.functionDispatch'));
});

test('synthesized constructor body helpers are native non-dispatchable entries', () => {
  productionCheck(`contract Base {
    modifier wrapped() { _; }
    constructor() wrapped {}
  }
  contract C is Base {
    function target() internal pure {}
    function entry() public pure {
      function() internal pure h = target;
      h();
    }
    constructor() {}
  }`, `#guard Imported.C.funs.any fun (name, _) => name.startsWith "solcCtorBody"
#guard Imported.C.funs.all fun (name, _) =>
  !(name.startsWith "solcCtorBody") || !(fnSource Imported.C name)
#guard (Imported.C.report.find? (·.name == "entry")).any fun row =>
  row.admissionChecked && row.status == .elaborated && row.sourceDiagnostic.isNone`);
});


test('discarded function projections preserve source names and evaluate array operands once', () => {
  productionCheck(`contract C {
    uint calls;
    function f() public returns(uint, uint) {
      uint discarded1 = 17;
      [C(address(0x1234)).f.address, address(uint160(++calls))][0];
      return (discarded1, calls);
    }
  }`, `#eval (do
  let cases : List (List String × String) :=
    [(["17", "1"], "working"), (["17", "0"], "broken"), (["4660", "1"], "broken")]
  for (expected, status) in cases do
    let vector := Lean.Json.mkObj [
      ("signature", Lean.toJson ("f()" : String)),
      ("args", Lean.toJson ([] : List String)),
      ("failure", Lean.toJson false), ("expected", Lean.toJson expected)]
    let data := Lean.Json.mkObj [("vectors", Lean.toJson [vector])]
    let report := Solidity.Tools.Upstream.replay Imported.C Imported.C.report data
    unless (report.getObjValAs? String "status").toOption == some status do
      throw (IO.userError report.pretty) : IO Unit)`);
});

test('effectful receiver address projection remains an explicit frontend exclusion', () => {
  productionCheck(`contract C {
    uint calls;
    function receiver() internal returns(address) { calls++; return address(0x1234); }
    function f() public returns(uint, uint) {
      uint discarded1 = 17;
      C(receiver()).f.address;
      return (discarded1, calls);
    }
  }`, `#guard (Imported.C.report.find? (·.name == "f")).any fun row => row.status == .unsupported
#eval (do
  let vector := Lean.Json.mkObj [
    ("signature", Lean.toJson ("f()" : String)),
    ("args", Lean.toJson ([] : List String)),
    ("failure", Lean.toJson false),
    ("expected", Lean.toJson (["17", "1"] : List String))]
  let report := Solidity.Tools.Upstream.replay Imported.C Imported.C.report
    (Lean.Json.mkObj [("vectors", Lean.toJson [vector])])
  unless (report.getObjValAs? String "status").toOption == some "broken" do
    throw (IO.userError report.pretty) : IO Unit)`);
});

test('internal memory-byte returns preserve location, aliasing and stateful pointer selection', () => {
  productionCheck(`contract C {
    bytes source = hex"616263";
    uint calls;
    function() internal returns(bytes memory) f;
    function other() internal view returns(bytes memory) { return source; }
    function first() internal returns(bytes memory) { calls++; f = other; return source; }
    constructor() { f = first; }
    function run() public returns(uint,uint) {
      bytes memory b = f(); b[0] = bytes1(0x64);
      return (uint8(b[0]), uint8(source[0]));
    }
    function count() public view returns(uint) { return calls; }
  }`, `#guard Imported.C.report.all fun r => r.status == .elaborated
#eval (do
  let cases : List (String × List String) :=
    [("run()", ["100", "97"]), ("count()", ["1"]),
     ("run()", ["100", "97"]), ("count()", ["1"])]
  let vectors := cases.map fun (signature, expected) => Lean.Json.mkObj [
    ("signature", Lean.toJson signature), ("args", Lean.toJson ([] : List String)),
    ("failure", Lean.toJson false), ("expected", Lean.toJson expected)]
  let data := Lean.Json.mkObj [("vectors", Lean.toJson vectors)]
  let report := Solidity.Tools.Upstream.replay Imported.C Imported.C.report data
  unless (report.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError report.pretty) : IO Unit)`);
});

test('abstract virtual reference identity resolves to its concrete body without losing declarations', () => {
  const source = `abstract contract S {
    function target() internal virtual returns(bytes memory);
  }
  abstract contract X is S {
    function target() internal pure override returns(bytes memory) { return hex"61"; }
  }
  contract C is X {
    function() internal returns(bytes memory) f;
    constructor() { f = super.target; }
    function run() public returns(uint) { bytes memory b = f(); return uint8(b[0]); }
  }`;
  scopeCheck(source, `let identities := contract.sourceDecls.filterMap fun (entry : String × Solidity.SourceFunction) =>
    let d := entry.2
    if d.name == "target" then d.declaration else none
  unless identities.eraseDups.length >= 2 do
    throw (IO.userError "abstract and concrete source identities were lost")`);
  productionCheck(source, `#guard Imported.C.report.all fun r => r.status == .elaborated
#guard Imported.C.funs.any fun (_, d) => d.sourceDecl.any fun identity =>
  identity.name == "target" && identity.declaration.isSome
#eval (do
  let vector := Lean.Json.mkObj [
    ("signature", Lean.toJson ("run()" : String)), ("args", Lean.toJson ([] : List String)),
    ("failure", Lean.toJson false), ("expected", Lean.toJson (["97"] : List String))]
  let data := Lean.Json.mkObj [("vectors", Lean.toJson [vector])]
  let report := Solidity.Tools.Upstream.replay Imported.C Imported.C.report data
  unless (report.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError report.pretty) : IO Unit)`);
});

test('memory-return admission refuses unsupported argument and external ABI paths', () => {
  // A scalar argument beside the memory-byte return is admitted since lane
  // CF2 (finite-dispatch.md, "Reference arguments"); a byte argument and an
  // external memory return stay refused.
  scopeCheck(`contract C {
    function target(uint x) internal pure returns(bytes memory) { return new bytes(x); }
    function entry() public pure {
      function(uint) internal pure returns(bytes memory) h = target; h(1);
    }
  }`, `unless (row "entry").any (fun (r : SolcFun) => r.body.isOk &&
      r.sourceScope.diagnostic?.isNone) do
    throw (IO.userError "a scalar argument beside a memory-byte return was not admitted")`);
  scopeCheck(`contract C {
    function target(bytes memory x) internal pure returns(bytes memory) { return x; }
    function entry() public pure {
      function(bytes memory) internal pure returns(bytes memory) h = target; h(hex"61");
    }
  }`, diagnostic('entry', 'solidity.functionDispatch'));
  scopeCheck(`contract C {
    function target() public pure returns(bytes memory) { return hex"61"; }
    function entry() public view {
      function() external view returns(bytes memory) h = this.target; h();
    }
  }`, diagnostic('entry', 'solidity.functionDispatch'));
});

test('a concrete base candidate with missing body metadata is not erased as abstract', () => {
  scopeCheck(`contract Base {
    function target() internal pure virtual returns(bytes memory) { return hex"61"; }
  }
  contract C is Base {
    function target() internal pure override returns(bytes memory) { return hex"62"; }
    function entry() public pure {
      function() internal pure returns(bytes memory) h = target;
      bytes memory b = h(); assert(b[0] == bytes1(0x62));
    }
  }`, `unless (row "entry").any (fun (r : SolcFun) => r.body.toOption.isNone) do
    throw (IO.userError "a malformed concrete candidate was silently erased")`,
  `let ast := modifyTree (fun node =>
    if J.kind node == "FunctionDefinition" && J.str? node "name" == some "target" &&
        ((J.arr node "baseFunctions").toOption.getD []).isEmpty then
      put (put node "implemented" (.bool true)) "body" .null else node) ast`);
});

// Internal function values with a memory- or storage-array parameter. The observations are
// the pinned compiler's (scripts/check-function-value-references.mjs, legacy
// and viaIR, optimizer off and on); the legacy schedule is the default.
const referenceSource = readFileSync('tests/solc/FunctionValueReferences.sol', 'utf8')
  .replace(/^\/\/ SPDX[^\n]*\npragma[^\n]*\n/, '').replace(/FunctionValueReferences/g, 'C');
const panic51 = [0x4e, 0x48, 0x7b, 0x71, ...Array(31).fill(0), 0x51];
const panic01 = [0x4e, 0x48, 0x7b, 0x71, ...Array(31).fill(0), 0x01];
function referenceVectors(viaIR) {
  // viaIR copies a storage argument after every argument (901); the model
  // copies at the argument's position for direct and dispatched calls alike
  // (finite-dispatch.md, "Recorded deviations"), so only legacy replays it.
  const order = viaIR ? [] : [['argumentOrder()', [], ['101', '9']],
    ['argumentOrderDirect()', [], ['101', '9']]];
  const callee = viaIR ? ['402'] : ['4002'];
  const calleeScalar = viaIR ? ['11'] : ['12'];
  const cases = [
    ['aliasing()', [], ['11', '11', '1']],
    ['storageCopy()', [], ['11', '1', '2']],
    ...order,
    ['calleeOrder()', [], callee],
    ['calleeOrderScalar()', [], calleeScalar],
    ['branches(bool)', ['true'], ['13']],
    ['branches(bool)', ['false'], ['7']],
    ['unassigned()', [], panic51],
    // legacy halts without data here (finite-dispatch.md, "Recorded deviations")
    ['unassignedStored()', [], panic51],
    ['deleted()', [], panic51],
    ['storageAlias()', [], ['6', '6']],
    ['storageOrder()', [], ['901', '9']],
    ['arrayReturn(bool)', ['true'], ['106', '106', '1']],
    ['arrayReturn(bool)', ['false'], ['5', '110', '1']],
    ['bytesReturn()', [], ['3', '65']],
    ['tupleReturn()', [], ['3', '2']],
    ['structMemory()', [], ['2', '2', '43']],
    ['structStorage()', [], ['8', '8']],
    ['nominalQ()', [], ['9']],
    ['falseObservation()', [], panic01],
  ];
  return cases.map(([signature, args, expected]) => {
    const failure = typeof expected[0] === 'number';
    return `Lean.Json.mkObj [("signature", Lean.toJson (${JSON.stringify(signature)} : String)),
      ("args", Lean.toJson (${JSON.stringify(args)} : List String)),
      ("failure", Lean.toJson ${failure}),
      ("expected", Lean.toJson (${JSON.stringify(failure ? [] : expected)} : List String))` +
      (failure ? `, ("revertBytes", Lean.toJson (${JSON.stringify(expected)} : List Nat))]` : ']');
  }).join(',\n    ');
}
function referenceReplay(viaIR) {
  return `#guard Imported.C.report.all fun r => r.status == .elaborated
#eval (do
  let data := Lean.Json.mkObj [("vectors", Lean.toJson [
    ${referenceVectors(viaIR)}])]
  let report := Solidity.Tools.Upstream.replay Imported.C Imported.C.report data
  unless (report.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError report.pretty) : IO Unit)`;
}

test('memory-array arguments alias, copy and dispatch as the compiler does (legacy)', () => {
  productionCheck(referenceSource, referenceReplay(false));
});

test('memory-array arguments under the viaIR schedule read the callee first', () => {
  productionCheck(referenceSource, referenceReplay(true), true);
});

// A refusal for this reason: the dispatch diagnostic, or the declaration
// reader's refusal of the function type itself; not an unrelated gap.
function refused(name) {
  return `unless (row ${JSON.stringify(name)}).any (fun (r : SolcFun) =>
      (r.sourceScope.diagnostic?.map (fun (d : Source.Diagnostic) => d.name)) == some \`solidity.functionDispatch ||
      (match r.body with
        | .error g => (String.splitOn (Gap.msg g) "function type").length > 1 ||
            (String.splitOn (Gap.msg g) "functionDispatch").length > 1
        | .ok _ => false)) do
    throw (IO.userError "the reference signature of ${name} was not refused by dispatch")`;
}

test('a recursive struct signature is refused by the elaborator', () => {
  // The reader admits the nominal key; the elaborator's fnRefStruct? refuses
  // the recursive struct, so the function stops elaborating (fails closed).
  productionCheck(`contract C {
    struct R { uint x; R[] kids; }
    function target(R memory r) internal pure returns(uint) { return r.x; }
    function entry() public pure returns(uint) {
      R memory r;
      function(R memory) internal pure returns(uint) h = target; return h(r);
    }
  }`, `#guard (Imported.C.report.find? (·.name == "entry")).any fun row =>
  row.status != .elaborated`);
});

test('calldata passed to a memory parameter of a function value is refused', () => {
  // solc copies the calldata array into memory; the dispatch passes memory
  // by reference, so the model would share it.
  productionCheck(`contract C {
    function bump(uint[] memory xs) internal pure returns(uint) { xs[0] = 7; return xs[0]; }
    function e(uint[] calldata xs) external pure returns(uint) {
      function(uint[] memory) internal pure returns(uint) h = bump;
      h(xs); return xs[0];
    }
  }`, `#guard (Imported.C.report.find? (·.name == "e")).any fun r =>
  r.status != .elaborated && (r.reason.splitOn "calldata passed").length > 1`);
});

test('struct candidates are nominal: a same-shaped struct function is not scanned', () => {
  // With a structural key, poison (same shape as P, reading block.number)
  // would be a native-compatible candidate and its body would be refused.
  scopeCheck(`contract C {
    struct P { uint a; }
    struct Q { uint a; }
    function target(P memory p) internal pure returns(uint) { return p.a; }
    function poison(Q memory q) internal view returns(uint) { return q.a + block.number; }
    function entry() public pure {
      P memory p;
      function(P memory) internal pure returns(uint) h = target; h(p);
    }
  }`, `unless (row "entry").any (fun (r : SolcFun) => r.body.isOk &&
      r.sourceScope.diagnostic?.isNone) do
    throw (IO.userError "a same-shaped struct's function was treated as a candidate")`);
});

test('reference-array dispatch admits exact candidates and keeps their locations', () => {
  scopeCheck(`contract C {
    function target(uint[] memory xs) internal pure returns(uint) { return xs[0]; }
    function stored(uint[] storage xs) internal view returns(uint) { return xs[0]; }
    uint[] values;
    function entry() public view {
      uint[] memory xs = new uint[](1);
      function(uint[] memory) internal pure returns(uint) h = target;
      assert(h(xs) == 0);
      function(uint[] storage) internal view returns(uint) g = stored;
      g(values);
    }
  }`, `unless (row "entry").any (fun (r : SolcFun) => r.body.isOk &&
      r.sourceScope.diagnostic?.isNone) do
    throw (IO.userError "memory-array dispatch was not admitted")`);
});

test('memory-array dispatch refuses an address/uint element collision', () => {
  scopeCheck(`contract C {
    function addrs(address[] memory xs) internal pure returns(uint) { return xs.length; }
    function uints(uint[] memory xs) internal pure returns(uint) { return xs.length; }
    function entry() public pure {
      uint[] memory xs = new uint[](1);
      function(uint[] memory) internal pure returns(uint) h = uints;
      h(xs);
    }
  }`, diagnostic('entry', 'solidity.functionDispatch'));
});

test('other reference signatures remain refused', () => {
  const cases = [
    // an external struct parameter
    `struct S { uint a; }
    function target(S memory s) public pure returns(uint) { return s.a; }
    function entry() public view {
      S memory s;
      function(S memory) external view returns(uint) h = this.target; h(s);
    }`,
    // a struct return
    `struct S { uint a; }
    function target() internal pure returns(S memory s) { s.a = 1; }
    function entry() public pure {
      function() internal pure returns(S memory) h = target; h();
    }`,
    // a nominal element
    `struct S { uint a; }
    function target(S[] memory xs) internal pure returns(uint) { return xs.length; }
    function entry() public pure {
      S[] memory xs = new S[](1);
      function(S[] memory) internal pure returns(uint) h = target; h(xs);
    }`,
    // a narrow element (a capture carries no width rows)
    `function target(uint8[] memory xs) internal pure returns(uint) { return xs[0]; }
    function entry() public pure {
      uint8[] memory xs = new uint8[](1);
      function(uint8[] memory) internal pure returns(uint) h = target; h(xs);
    }`,
    // a byte element
    `function target(bytes1[] memory xs) internal pure returns(uint) { return xs.length; }
    function entry() public pure {
      bytes1[] memory xs = new bytes1[](1);
      function(bytes1[] memory) internal pure returns(uint) h = target; h(xs);
    }`,
    // a nested array
    `function target(uint[][] memory xs) internal pure returns(uint) { return xs.length; }
    function entry() public pure {
      uint[][] memory xs = new uint[][](1);
      function(uint[][] memory) internal pure returns(uint) h = target; h(xs);
    }`,
    // a calldata reference
    `function target(uint[] calldata xs) internal pure returns(uint) { return xs.length; }
    function entry(uint[] calldata xs) external pure {
      function(uint[] calldata) internal pure returns(uint) h = target; h(xs);
    }`,
    // a storage mapping
    `mapping(uint => uint) m;
    function target(mapping(uint => uint) storage xs) internal view returns(uint) { return xs[0]; }
    function entry() public view {
      function(mapping(uint => uint) storage) internal view returns(uint) h = target; h(m);
    }`,
    // a storage-array return
    `uint[] values;
    function target() internal view returns(uint[] storage) { return values; }
    function entry() public view {
      function() internal view returns(uint[] storage) h = target; h();
    }`,
    // several memory returns
    `function target() internal pure returns(bytes memory, bytes memory) { return (hex"61", hex"62"); }
    function entry() public pure {
      function() internal pure returns(bytes memory, bytes memory) h = target; h();
    }`,
    // a memory return beside a scalar return
    `function target() internal pure returns(bytes memory, uint) { return (hex"61", 1); }
    function entry() public pure {
      function() internal pure returns(bytes memory, uint) h = target; h();
    }`,
    // an external memory-array parameter
    `function target(uint[] memory xs) public pure returns(uint) { return xs.length; }
    function entry() public view {
      uint[] memory xs = new uint[](1);
      function(uint[] memory) external view returns(uint) h = this.target; h(xs);
    }`,
    // an external memory-array return
    `function target() public pure returns(uint[] memory xs) { xs = new uint[](1); }
    function entry() public view {
      function() external view returns(uint[] memory) h = this.target; h();
    }`,
  ];
  const failed = [];
  cases.forEach((body, i) => {
    try { scopeCheck(`contract C {\n${body}\n}`, refused('entry')); }
    catch (e) { failed.push(`case ${i}: ${(String(e.stdout ?? "") + String(e.stderr ?? "") + String(e.message ?? "")).split("\n").filter(l => /error|userError|not refused/.test(l)).join(" | ").slice(0, 600)}`); }
  });
  assert.deepEqual(failed, []);
});
