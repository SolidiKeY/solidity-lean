import {test} from 'node:test';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {mkdtempSync,readFileSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';
import {runSolidityTests,testsPassed} from './test-solidity.mjs';

const source = 'tests/solc/Shadowing.sol';

function leanCheck(text, directory) {
  const file = join(directory,'Check.lean');
  writeFileSync(file,text);
  try {
    return execFileSync('lake',['--quiet','--no-build','lean',file,'--','--tstack=131072'],{
      timeout:120000,encoding:'utf8',maxBuffer:8*1024*1024,
    });
  } catch (error) {
    throw new Error(`Shadowing kernel check failed:\n${error.stdout?.toString() || error.message}`);
  }
}

test('source shadowing preserves reads, writes, source contracts and lexical scope', () => {
  const report = runSolidityTests([source],{build:false,contract:'Shadowing'});
  assert.deepEqual(report.errors,[]);
  const rows = new Map(report.results.map(row => [row.function,row]));
  for (const name of ['constructor','innerReadWrite','beforeDeclaration','selfInitialization',
    'defaultInitialization','parameterSpec','stateParameterSpec','namedReturn','stateField','siblings','forScope',
    'loopScope','tupleDeclaration','modified','catchScope','legacyAliases','namedCall']) {
    assert.equal(rows.get(name)?.status,'proved',`${name}: ${rows.get(name)?.reason}`);
  }
  assert.equal(rows.get('originalFormalNames')?.status,'internal');
  for (const name of ['witness','falseAssertion'])
    assert.equal(rows.get(name)?.status,'pending',`${name}: ${rows.get(name)?.reason}`);
  assert.equal(testsPassed(report),false);
});

test('renamed shadowing parameters retain exact certified source witness positions', () => {
  const report = runSolidityTests([source],{
    build:false,contract:'Shadowing',function:'witness(uint,uint)',counterexamples:true,
  });
  assert.deepEqual(report.errors,[]);
  assert.equal(report.results.length,1);
  const row = report.results[0];
  assert.equal(row.status,'refuted',row.reason);
  assert.equal(row.counterexample.certified,true);
  const arguments_ = row.counterexample.arguments;
  assert.deepEqual(arguments_.map(argument => argument.sourceName),['v','v_']);
  assert.deepEqual(arguments_.map(argument => argument.paramIndex),[0,1]);
  assert.equal(arguments_[0].value,'2');
  assert.match(arguments_[0].modelName,/^solcLocal[0-9]+_*$/);
  assert.equal(arguments_[1].modelName,'v_');
  assert.notEqual(arguments_[0].modelName,arguments_[1].modelName);
  assert.ok(row.counterexample.axioms.every(name => ['propext','Classical.choice','Quot.sound'].includes(name)));
});

test('declaration-ID names avoid user locals, called functions, specification binders and legacy aliases', () => {
  const directory = mkdtempSync(join(tmpdir(),'solidity-shadowing-names-'));
  try {
    const declaration = (id,name) => ({nodeType:'VariableDeclaration',id,name,stateVariable:false});
    const fn = (parameters,body) => ({nodeType:'FunctionDefinition',id:1,name:'f',
      parameters:{nodeType:'ParameterList',parameters},body:{nodeType:'Block',statements:body}});
    const collisionFree = fn([declaration(20,'from'),declaration(21,'from_')],[]);
    const stateCollisionFree = fn([declaration(20,'x'),declaration(21,'x_')],[]);
    const legacyDuplicates = fn([declaration(20,'x'),declaration(21,'x_'),
      declaration(30,'from'),declaration(31,'from_')],[declaration(22,'x'),declaration(32,'from')]);
    const collisions = fn([declaration(11,'v')],[declaration(12,'v'),declaration(13,'solcLocal11'),
      {nodeType:'Identifier',name:'solcLocal12',referencedDeclaration:99},
      {nodeType:'WhileStatement',loopSpec:['invariant \\forall uint solcLocal11_; true']}]);
    const unnamed = fn([declaration(77,'')],[declaration(78,'solcArg77')]);
    const literal = value => `(Lean.Json.parse ${JSON.stringify(JSON.stringify(value))}).toOption.getD .null`;
    leanCheck(`import Solidity.Frontend.SolcJson.Contract
open Solidity.Frontend
def collisionFree : Lean.Json := ${literal(collisionFree)}
def stateCollisionFree : Lean.Json := ${literal(stateCollisionFree)}
def legacyDuplicates : Lean.Json := ${literal(legacyDuplicates)}
def collisions : Lean.Json := ${literal(collisions)}
def unnamed : Lean.Json := ${literal(unnamed)}
#guard renames [] collisionFree == [(20, "from__")]
#guard renames ["x"] stateCollisionFree == [(20, "x__")]
${[20,22,30,32].map(id => `#guard Solidity.Semantics.lookupBy (${id} : Int) (renames ["x"] legacyDuplicates) == some "solcLocal${id}"`).join('\n')}
#guard (renames ["x"] legacyDuplicates).length == 4
#guard (renames [] collisions).length == 2
#guard Solidity.Semantics.lookupBy (11 : Int) (renames [] collisions) == some "solcLocal11__"
#guard Solidity.Semantics.lookupBy (12 : Int) (renames [] collisions) == some "solcLocal12_"
#guard renames [] unnamed == [(77, "solcArg77_")]
`,directory);
  } finally { rmSync(directory,{recursive:true,force:true}); }
});

test('a real source variable matching an allocated declaration-ID name cannot be captured', () => {
  const directory = mkdtempSync(join(tmpdir(),'solidity-shadowing-capture-'));
  try {
    const file = join(directory,'Collision.sol');
    const fixture = join(directory,'Collision.ast.json');
    const text = `pragma solidity ^0.8.34;
contract Collision {
  function check() public pure {
    uint v = 1;
    uint userMarker = 9;
    { uint v = 2; assert(v == 2); }
    assert(v == 1 && userMarker == 9);
  }
}`;
    writeFileSync(file,text);
    execFileSync(process.execPath,['scripts/solc-ast.mjs','--source',file,'--out',fixture,'--no-wrapper'],{timeout:30000});
    const ast = JSON.parse(readFileSync(fixture,'utf8')).ast;
    const f = ast.nodes.find(node => node.nodeType === 'ContractDefinition').nodes.find(node => node.name === 'check');
    const id = f.body.statements[0].declarations[0].id;
    writeFileSync(file,text.replaceAll('userMarker',`solcLocal${id}`));
    const report = runSolidityTests([file],{build:false,contract:'Collision'});
    assert.deepEqual(report.errors,[]);
    assert.equal(report.results[0]?.status,'proved',report.results[0]?.reason);
  } finally { rmSync(directory,{recursive:true,force:true}); }
});

test('tuple annotations retain the innermost program binding after source-ID renaming', () => {
  const directory = mkdtempSync(join(tmpdir(),'solidity-shadowing-tuples-'));
  try {
    const fixture = join(directory,'Shadowing.ast.json');
    execFileSync(process.execPath,['scripts/solc-ast.mjs','--source',resolve(source),
      '--out',fixture,'--no-wrapper'],{timeout:30000});
    let hash = 0xcbf29ce484222325n;
    for (const byte of readFileSync(fixture)) hash = BigInt.asUintN(64,(hash ^ BigInt(byte))*0x100000001b3n);
    leanCheck(`import Solidity.Frontend.Testing
open Solidity
solc_import "Shadowing.ast.json" hash 0x${hash.toString(16)} as Imported.Shadowing testing
mutual
def metricPositionsP {C : Contract} : {Γ Δ : Ctx} → Prog C Γ Δ → List (List (Option Nat))
  | _, _, .nil => []
  | _, _, .cons head tail => metricPositionsS head ++ metricPositionsP tail
def metricPositionsS {C : Contract} : {Γ Δ : Ctx} → Stmt C Γ Δ → List (List (Option Nat))
  | _, _, .loop annotation _ body =>
    (match annotation with
      | .invLex _ metrics _ _ => [metrics.toList.map fun metric => match metric with
        | .simple (.local position) => some position.toNat
        | _ => none]
      | _ => []) ++ metricPositionsP body
  | _, _, .block body => metricPositionsP body
  | _, _, .ite _ left right => metricPositionsP left ++ metricPositionsP right
  | _, _, _ => []
end
example : metricPositionsP Imported.Shadowing.loopScope = [[some 0, none]] := by decide +kernel
`,directory);
  } finally { rmSync(directory,{recursive:true,force:true}); }
});

test('previously unsupported tuple-loop shadowing and C99 source cases are admitted and proved', () => {
  const loop = runSolidityTests(['tests/solc/LexMetrics.sol'],{
    build:false,contract:'LexMetrics',function:'shadowed',
  });
  assert.deepEqual(loop.errors,[]);
  assert.equal(loop.results[0]?.status,'proved',loop.results[0]?.reason);
  const expected = ['c99ScopingAssignOuter','c99ScopingReadOuter','c99ScopingSelfInit','c99ScopingShadowDefault'];
  const directory = mkdtempSync(join(tmpdir(),'solidity-shadowing-c99-'));
  try {
    const fixture = join(directory,'C99.ast.json');
    execFileSync(process.execPath,['scripts/solc-ast.mjs','--source',
      resolve('tests/migration/solkey/keyext.solidity.examples/solc/SolcConstructors.sol'),
      '--out',fixture,'--no-wrapper'],{timeout:30000});
    let hash = 0xcbf29ce484222325n;
    for (const byte of readFileSync(fixture)) hash = BigInt.asUintN(64,(hash ^ BigInt(byte))*0x100000001b3n);
    leanCheck(`import Solidity.Frontend.Testing
solc_import "C99.ast.json" hash 0x${hash.toString(16)} as Imported.SolcConstructors testing
solc_scoped_problems Imported.SolcConstructors decl
${expected.map(name => `#solkey_test Imported.SolcConstructors only "${name}" to ${JSON.stringify(join(directory,`${name}.json`))}`).join('\n')}
`,directory);
    for (const name of expected) {
      const [row] = JSON.parse(readFileSync(join(directory,`${name}.json`),'utf8'));
      assert.equal(row.function,name);
      assert.equal(row.status,'proved',`${name}: ${row.reason}`);
    }
  } finally { rmSync(directory,{recursive:true,force:true}); }
});
