import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync,existsSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {spawnSync} from 'node:child_process';
const root=resolve('tests/source-immutables');
const evidence='/workspace/vy5-composition/h12-independent-20261102';
const raw=readFileSync('/workspace/vy5-composition/evidence/h12-immut-baseline-mcp-final.log','utf8');
const dir=join(evidence,'guard-tests');mkdirSync(dir,{recursive:true});
const expectedRaw=readFileSync(join(root,'expected.json'),'utf8');
const expected=JSON.parse(expectedRaw);
const baseline=join(root,'ImmutableBaseline.lean.txt');
function reject(name,content,head=expected.baselineSourceHead,manifest=expected,reason,baselineInput=baseline) {
 const log=join(dir,name+'.log'),spec=join(dir,name+'.expected.json'),out=join(dir,name+'.report.json');
 writeFileSync(log,content);writeFileSync(spec,manifest===expected ? expectedRaw : JSON.stringify(manifest));
 const r=spawnSync(process.execPath,[join(root,'check-source.mjs'),log,spec,baselineInput,head,out],{encoding:'utf8'});
 assert.notEqual(r.status,0);assert.match(r.stderr,reason);assert.equal(existsSync(out),false,'invalid evidence wrote a result');
}
function changeRecords(f) {
 return raw.split('\n').map(line=>{
  if(!line.startsWith('tests/source-immutables/ImmutableBaseline.lean ')) return line;
  const i=line.indexOf('{'),record=JSON.parse(line.slice(i));
  f(record.structuredContent.result);
  return line.slice(0,i)+JSON.stringify(record);
 }).join('\n');
}
test('desired constructor acceptance stays failed, not an approved exclusion',()=>{
 const r=JSON.parse(readFileSync(join(evidence,'source-acceptance.json')));
 assert.equal(r.rows.length,8);assert.equal(r.allMatch,false);
 assert.deepEqual(r.rows.filter(x=>!x.match).map(x=>[x.pipeline,x.fixture,x.actualAccepted,x.desiredAccepted]),
  [['legacy','Constructor.sol',false,true],['viaIR','Constructor.sol',false,true]]);
});
test('missing Source pipeline is refused',()=>reject('missing',changeRecords(r=>{
 r.items=r.items.filter(x=>!x.message.includes('H12_SOURCE_ACCEPTANCE pipeline=viaIR'));
}),expected.baselineSourceHead,expected,/missing\/reordered/));
test('reordered Source pipelines are refused',()=>reject('reordered',changeRecords(r=>{
 const ix=r.items.map((x,i)=>x.message.includes('H12_SOURCE_ACCEPTANCE')?i:-1).filter(i=>i>=0);
 [r.items[ix[0]],r.items[ix[1]]]=[r.items[ix[1]],r.items[ix[0]]];
}),expected.baselineSourceHead,expected,/missing\/reordered/));
test('incomplete elaboration is refused',()=>reject('partial',changeRecords(r=>{r.partial=true;}),
 expected.baselineSourceHead,expected,/incomplete/));
test('stale Source head is refused',()=>reject('head',raw,'0'.repeat(40),expected,/stale source head/));
test('stale baseline bytes are refused',()=>{
 const changed=join(dir,'stale-baseline.lean.txt');writeFileSync(changed,readFileSync(baseline,'utf8')+'\n-- stale');
 reject('baseline',raw,expected.baselineSourceHead,expected,/stale baseline source/,changed);
});
test('changed desired verdict cannot green a Source rejection',()=>{
 const changed=structuredClone(expected);changed.fixtures[0].sourceDesiredAccepted=false;
 reject('changed-verdict',raw,expected.baselineSourceHead,changed,/expected manifest hash mismatch/);
});
function rejectCompilerCatalog(name,fixtures) {
 const path=join(dir,name);mkdirSync(path,{recursive:true});
 writeFileSync(join(path,'expected.json'),JSON.stringify({...expected,fixtures}));
 const r=spawnSync(process.execPath,[join(root,'probe.mjs'),'/missing/compiler','/missing/helper',path,join(path,'output')],{encoding:'utf8'});
 assert.notEqual(r.status,0);assert.match(r.stderr,/expected manifest hash mismatch/);
 assert.equal(existsSync(join(path,'output')),false);
}
test('empty compiler fixture catalog is refused',()=>rejectCompilerCatalog('empty-catalog',[]));
test('duplicate compiler fixture catalog is refused',()=>rejectCompilerCatalog('duplicate-catalog',[...expected.fixtures,expected.fixtures[0]]));
test('missing record is refused',()=>reject('no-record','',expected.baselineSourceHead,expected,/missing or duplicate/));
test('helper digest is checked before executing imported code',()=>{
 const helper=join(dir,'must-not-execute.mjs'),marker=join(dir,'executed');
 writeFileSync(helper,`import{writeFileSync}from'node:fs';writeFileSync(${JSON.stringify(marker)},'bad');`);
 const r=spawnSync(process.execPath,[join(root,'probe.mjs'),'/missing/compiler',helper,root,join(dir,'bad-compiler')],{encoding:'utf8'});
 assert.notEqual(r.status,0);assert.match(r.stderr,/compiler helper hash mismatch/);assert.equal(existsSync(marker),false);
});
