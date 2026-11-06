// Inventory transport integrity is part of the gate's fail-closed boundary.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os'),{spawnSync}=require('node:child_process');
const {loadInventory,saveInventory}=require('../parity/inventory.cjs');
const repo=path.resolve(__dirname,'../..');
function fixture(){
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),'parity-inventory-'));
 const descriptor=path.join(dir,'docs/dafny-editor-features.json');fs.mkdirSync(path.dirname(descriptor),{recursive:true});fs.copyFileSync(path.join(repo,'docs/dafny-editor-features.json'),descriptor);
 const entry=JSON.parse(fs.readFileSync(descriptor)).inventory,file=path.join(dir,entry.path);
 return{dir,descriptor,file,entry,restore(){fs.mkdirSync(path.dirname(file),{recursive:true});fs.copyFileSync(path.join(repo,entry.path),file);},close(){fs.rmSync(dir,{recursive:true,force:true});}};
}
test('inventory loader rejects absent or corrupt bulk instead of accepting the digest as rows',()=>{
 const f=fixture();try{
  assert.throws(()=>loadInventory(f.descriptor,f.dir),/Full parity inventory unavailable:.*Restore the checksum-bound bundle/);
  f.restore();assert.equal(loadInventory(f.descriptor,f.dir).features.length,93);
  const bytes=fs.readFileSync(f.file);fs.writeFileSync(f.file,Buffer.concat([bytes,Buffer.from(' ')]));assert.throws(()=>loadInventory(f.descriptor,f.dir),/checksum\/size mismatch/);
  fs.writeFileSync(f.file,bytes);const d=JSON.parse(fs.readFileSync(f.descriptor));d.inventory.rows--;fs.writeFileSync(f.descriptor,JSON.stringify(d));assert.throws(()=>loadInventory(f.descriptor,f.dir),/count mismatch/);
 }finally{f.close();}
});
test('digest paths cannot escape the ignored inventory location',()=>{
 const f=fixture();try{const d=JSON.parse(fs.readFileSync(f.descriptor));for(const value of ['/tmp/arbitrary.json','../outside.json','tests/editor-parity/inventory/../../outside.json']){d.inventory.path=value;fs.writeFileSync(f.descriptor,JSON.stringify(d));assert.throws(()=>loadInventory(f.descriptor,f.dir),/Invalid tracked parity inventory digest/);}}finally{f.close();}
});
test('inventory refresh updates the digest but cannot remove or duplicate an existing obligation',()=>{
 const f=fixture();try{f.restore();const initial=loadInventory(f.descriptor,f.dir);const before=fs.readFileSync(f.file);
  const removed=structuredClone(initial);removed.mechanical.rows.pop();assert.throws(()=>saveInventory(removed,f.descriptor,f.dir),/shrinkage/);assert.deepEqual(fs.readFileSync(f.file),before);
  const duplicate=structuredClone(initial);duplicate.features.push(duplicate.features[0]);assert.throws(()=>saveInventory(duplicate,f.descriptor,f.dir),/duplicate/);
  initial.features[0].assessment.reason+=' Test-only metadata update';saveInventory(initial,f.descriptor,f.dir);assert.deepEqual(loadInventory(f.descriptor,f.dir),initial);
 }finally{f.close();}
});
test('fresh-checkout audit fails explicitly until the verified bundle is restored',()=>{
 const f=fixture();try{
  fs.mkdirSync(path.join(f.dir,'vscode/parity'),{recursive:true});for(const name of ['audit.cjs','inventory.cjs'])fs.copyFileSync(path.join(repo,'vscode/parity',name),path.join(f.dir,'vscode/parity',name));
  fs.copyFileSync(path.join(repo,'docs/dafny-editor-audit.json'),path.join(f.dir,'docs/dafny-editor-audit.json'));
  const audit=()=>spawnSync(process.execPath,[path.join(f.dir,'vscode/parity/audit.cjs'),'--check'],{encoding:'utf8'});
  const absent=audit();assert.equal(absent.status,1);assert.match(absent.stderr,/Full parity inventory unavailable:.*Restore the checksum-bound bundle/);
  assert.equal(spawnSync('git',['init','-q',f.dir]).status,0);fs.copyFileSync(path.join(repo,'.gitignore'),path.join(f.dir,'.gitignore'));
  const restore=spawnSync('python3',[path.join(repo,'scripts/coord-tools/dafny-parity-bulk.py'),'--repo',f.dir,'--manifest',path.join(repo,'docs/dafny-editor-inventory-manifest.json'),'--restore'],{encoding:'utf8'});assert.equal(restore.status,0,restore.stderr);
  const present=audit();assert.equal(present.status,0,present.stderr);assert.match(present.stdout,/Audited/);
  fs.appendFileSync(f.file,' ');const corrupt=audit();assert.equal(corrupt.status,1);assert.match(corrupt.stderr,/checksum\/size mismatch/);
 }finally{f.close();}
});

test('ordinary paired runtime reports retain the original completeness predicate (injected reports)',()=>{
 const dir=fs.mkdtempSync(path.join(repo,'.lake/inventory-evidence-'));
 try{const inventory=loadInventory(),feature=inventory.features[0];feature.assessment={...feature.assessment,status:'complete',scenarioIds:['fixture-native'],testEvidence:[]};
  for(const target of ['local','dafny']){const file=path.join(dir,target+'.json');fs.writeFileSync(file,JSON.stringify({runId:'injected-'+target,target,status:'passed',checks:['fixture-native'],scenarios:[{id:'fixture-native',status:'passed'}]}));feature.assessment.testEvidence.push({target,status:'passed',assertion:'fixture-native',artifact:path.relative(repo,file)});}
  const {validate}=require('../parity/discover.cjs');assert.deepEqual(validate(inventory),[]);
  const file=path.join(dir,'local.json'),report=JSON.parse(fs.readFileSync(file));report.scenarios[0].status='missing';fs.writeFileSync(file,JSON.stringify(report));assert.ok(validate(inventory).some(e=>e.includes('unsupported completeness claim')));
 }finally{fs.rmSync(dir,{recursive:true,force:true});}
});
