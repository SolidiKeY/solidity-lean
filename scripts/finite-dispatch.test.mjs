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
    execFileSync('lake', ['--quiet', '--no-build', 'lean', check, '--', '--tstack=131072'],
      {stdio:'pipe', encoding:'utf8', timeout:180000});
  } finally { rmSync(dir, {recursive:true, force:true}); }
}

// Run the real import command for specification and native-model checks.
// This deliberately uses Import's private production callbacks through solc_import.
function productionCheck(source, body) {
  const dir = mkdtempSync(join(tmpdir(), 'solidity-production-dispatch-'));
  try {
    const input = join(dir, 'FiniteDispatch.sol');
    const fixture = join(dir, 'FiniteDispatch.ast.json');
    const check = join(dir, 'Check.lean');
    writeFileSync(input, '// SPDX-License-Identifier: MIT\npragma solidity ^0.8.0;\n' + source);
    execFileSync(process.execPath, ['scripts/solc-ast.mjs', '--source', input,
      '--out', fixture, '--no-wrapper'], {stdio:'pipe'});
    let hash = 0xcbf29ce484222325n;
    for (const byte of readFileSync(fixture))
      hash = BigInt.asUintN(64, (hash ^ BigInt(byte)) * 0x100000001b3n);
    writeFileSync(check, `import Solidity.Tools.Upstream
open Solidity Solidity.Frontend
solc_import "FiniteDispatch.ast.json" hash 0x${hash.toString(16)} as Imported.C testing
${body}
`);
    execFileSync('lake', ['--quiet', '--no-build', 'lean', check, '--', '--tstack=131072'],
      {stdio:'pipe', encoding:'utf8', timeout:180000});
  } finally { rmSync(dir, {recursive:true, force:true}); }
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

test('reference arguments remain explicitly refused by native dispatch', () => {
  scopeCheck(`contract C {
    function target(uint[] memory xs) internal pure returns(uint) { return xs.length; }
    function entry(uint[] memory xs) public pure {
      function(uint[] memory) internal pure returns(uint) h = target;
      h(xs);
    }
  }`, diagnostic('entry', 'solidity.functionDispatch'));
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
  scopeCheck(`contract C {
    function target(uint x) internal pure returns(bytes memory) { return new bytes(x); }
    function entry() public pure {
      function(uint) internal pure returns(bytes memory) h = target; h(1);
    }
  }`, diagnostic('entry', 'solidity.functionDispatch'));
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
