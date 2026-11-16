// Regression: a physical trace can remain stale after a current cached build.
// Bind source positions to the exact current OLean tuple, refusing ambiguity.
import {test} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync,existsSync} from 'node:fs';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {freshArtifactGraph,currentIleanPaths} from './trust-artifacts.mjs';
test('fresh importing setup selects the root without reading physical traces',()=>{
 const root=mkdtempSync(join(tmpdir(),'trust-artifact-graph-'));let query;
 try{
  const graph=freshArtifactGraph('Solidity.Theorems',{root,run:(_cmd,args)=>{query=args[2];assert.match(readFileSync(query,'utf8'),/import Solidity.Theorems/);return JSON.stringify({importArts:{'Solidity.Theorems':['new.olean']}});}});
  assert.equal(graph.imports['Solidity.Theorems'][0],join(root,'new.olean'));assert.equal(existsSync(query),false);
  assert.throws(()=>freshArtifactGraph('Solidity; bad',{root}),/invalid artifact root/);
 }finally{rmSync(root,{recursive:true,force:true});}
});
test('current object tuple selects paired index and ambiguous pairs fail closed',()=>{
 const root=mkdtempSync(join(tmpdir(),'trust-artifact-index-'));
 try{
  mkdirSync(join(root,'artifacts'));mkdirSync(join(root,'inputs'));
  writeFileSync(join(root,'artifacts/current.ilean'),'current index');
  const inputs=join(root,'inputs/solidity-lean.jsonl');
  const rows=[['same-input',{o:['old'],i:'stale'}],['same-input',{o:['new'],i:'current'}]];
  writeFileSync(inputs,rows.map(r=>JSON.stringify(r)).join('\n')+'\n');
  const graph={'Solidity.Control':[join(root,'artifacts/new.olean')]};
  assert.equal(currentIleanPaths(graph,['Solidity.Control'],{cacheDir:root}).get('Solidity.Control'),join(root,'artifacts/current.ilean'));
  rows.push(['other-input',{o:['new'],i:'different'}]);writeFileSync(inputs,rows.map(r=>JSON.stringify(r)).join('\n')+'\n');
  assert.throws(()=>currentIleanPaths(graph,['Solidity.Control'],{cacheDir:root}),/ambiguous/);
  assert.throws(()=>currentIleanPaths({},['Solidity.Control'],{cacheDir:root}),/module unavailable/);
  writeFileSync(inputs,JSON.stringify(['tuple',{o:['public','private'],i:'current'}])+'\n');
  const complete={'Solidity.Control':[join(root,'artifacts/private.olean.private'),join(root,'artifacts/public.olean')]};
  assert.equal(currentIleanPaths(complete,['Solidity.Control'],{cacheDir:root}).get('Solidity.Control'),join(root,'artifacts/current.ilean'));
  assert.throws(()=>currentIleanPaths({'Solidity.Control':[join(root,'artifacts/public.olean')]},['Solidity.Control'],{cacheDir:root}),/ambiguous or missing/);
 }finally{rmSync(root,{recursive:true,force:true});}
});
