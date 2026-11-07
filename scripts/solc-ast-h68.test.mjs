import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdtempSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join,dirname} from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {execFileSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {compileFixture} from './solc-ast.mjs';
import {retainCompilerMetadata} from '../tests/directruntime-20261104/shared-translator/retained-metadata.mjs';

// The immutable pre-H68 producer is executed, not mocked. Both compilers use
// identical arguments/settings/source bytes. No checked expectations are rewritten.
const root=join(dirname(fileURLToPath(import.meta.url)),'..');
const base='5f7bb1441566aaad64a34436904afc61de762fd2';
const baseline=execFileSync('git',['show',base+':scripts/solc-ast.mjs'],{cwd:root});
const source=`pragma solidity ^0.8.34;
contract H68 {
  uint256 public root;
  function narrow(uint8 x) external pure returns (uint8) { return x; }
  function called(uint256 x) public pure returns (uint256) { return x; }
  function run(uint256 n) external returns (uint256) {
    require(n > 0); uint256 i = 0;
    /// @custom:key invariant i <= n
    /// @custom:key decreases n - i
    while (i < n) { i++; }
    try this.called(n) returns (uint256 z) { root = z; } catch { root = 0; }
    return i;
  }
}`;
const sha=b=>createHash('sha256').update(b).digest('hex');
function nodes(value){
 const out=[];
 const go=x=>{if(!x||typeof x!=='object')return;if(x.nodeType)out.push(x);for(const v of Object.values(x)){if(Array.isArray(v))v.forEach(go);else go(v);}};
 go(value);return out;
}
const withoutMetadata=x=>JSON.parse(JSON.stringify(x,(k,v)=>k==='typeIdentifier'||k==='tryCall'?undefined:v));

test('H68 modern producer retains exact raw metadata without changing normalization, loops or provenance',async()=>{
 const temp=mkdtempSync(join(tmpdir(),'cr-h68-'));
 const oldPath=join(root,'scripts',`.solc-ast-h68-baseline-${process.pid}.mjs`);
 let baselineCreated=false;
 try{
  writeFileSync(oldPath,baseline,{flag:'wx'});baselineCreated=true;
  const old=(await import(pathToFileURL(oldPath).href)).compileFixture;
  const input=join(temp,'H68.sol');writeFileSync(input,source);
  const common=['--solkey','/workspace/.setup/solkey','--compiler-file','/workspace/.setup/soljson/soljson-v0.8.34+commit.80d5c536.js','--compiler-sha256','c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8','--source',input,'--no-wrapper'];
  for(const pipeline of [[],['--via-ir']]){
   const run=(fn,name)=>fn({args:[...common,...pipeline,'--out',join(temp,name+'.json')],quiet:true});
   const before=run(old,'before'),after=run(compileFixture,'after');
   assert.deepEqual(after.rawAst,before.rawAst);
   assert.deepEqual(withoutMetadata(after.fixture),withoutMetadata(before.fixture));
   assert.deepEqual(after.fixture,retainCompilerMetadata(before).fixture);
   let types=0,tries=0,trueFlags=0,falseFlags=0;
   for(const n of nodes(after.fixture.ast)){
    const matches=nodes(after.rawAst).filter(x=>x.nodeType===n.nodeType&&x.src===n.src&&(n.id===undefined||x.id===n.id));
    assert.ok(matches.length,'normalized node retains raw compiler identity');
    const raw=matches[0];
    if(typeof raw.typeDescriptions?.typeIdentifier==='string'&&n.typeDescriptions){assert.equal(n.typeDescriptions.typeIdentifier,raw.typeDescriptions.typeIdentifier);types++;}
    if(typeof raw.tryCall==='boolean'){assert.equal(n.tryCall,raw.tryCall);tries++;if(raw.tryCall)trueFlags++;else falseFlags++;}
   }
   assert.ok(types>0);assert.ok(tries>0);assert.ok(trueFlags>0);assert.ok(falseFlags>0);
   const loops=nodes(after.fixture.ast).filter(n=>n.nodeType==='WhileStatement');
   assert.equal(loops.length,1);assert.deepEqual(loops[0].loopSpec,['invariant i <= n','decreases n - i']);
   const builtin=nodes(after.fixture.ast).find(n=>n.nodeType==='Identifier'&&n.name==='require');
   assert.ok(builtin.referencedDeclaration<0,'builtin ID stays signed');
   assert.equal(after.compiler.sha256,'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8');
  }
  const legacyArgs=[...common,'--legacy-fixture'];
  const a=old({args:[...legacyArgs,'--out',join(temp,'legacy-before.json')],quiet:true});
  const b=compileFixture({args:[...legacyArgs,'--out',join(temp,'legacy-after.json')],quiet:true});
  assert.deepEqual(b.fixture,a.fixture,'explicit frozen legacy serialization is unchanged');
  assert.equal(sha(readFileSync(join(temp,'legacy-before.json'))),sha(readFileSync(join(temp,'legacy-after.json'))));
 } finally {if(baselineCreated)rmSync(oldPath,{force:true});rmSync(temp,{recursive:true,force:true});}
});
