// Inventory transport integrity is part of the gate's fail-closed boundary.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os'),{spawnSync}=require('node:child_process');
const {loadInventory,saveInventory,checkOffline}=require('../parity/inventory.cjs');
const {createHash}=require('node:crypto'),{inventoryFixture}=require('./parity-fixture.cjs');
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
const repo=path.resolve(__dirname,'../..');
// Hermetic injected checksum-bound bundle; no VM payload is needed for transport tests.
function fixture(){
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),'parity-inventory-')),descriptor=path.join(dir,'docs/dafny-editor-features.json');fs.mkdirSync(path.dirname(descriptor),{recursive:true});
 const inventory=inventoryFixture(),pins=JSON.parse(fs.readFileSync(path.join(repo,'docs/dafny-editor-audit.json'))).upstream;
 inventory.upstream={extension:{commit:pins.extension},server:{commit:pins.server}};
 const payload=Buffer.from(JSON.stringify(inventory,null,2)+'\n'),entry={path:'tests/editor-parity/inventory/injected.json',bytes:payload.length,sha256:sha(payload),features:inventory.features.length,mechanicalRows:inventory.mechanical.rows.length,rows:inventory.features.length+inventory.mechanical.rows.length};
 const file=path.join(dir,entry.path),manifestPath=path.join(dir,'docs/dafny-editor-inventory-manifest.json'),archive=path.join(dir,'bulk.tar.gz'),index=path.join(dir,'files.json');
 fs.mkdirSync(path.dirname(file),{recursive:true});fs.writeFileSync(file,payload);
 const packed=spawnSync('tar',['-czf',archive,'-C',dir,entry.path],{encoding:'utf8'});assert.equal(packed.status,0,packed.stderr);fs.unlinkSync(file);
 fs.writeFileSync(index,JSON.stringify([{path:entry.path,bytes:payload.length,sha256:sha(payload)}]));
 const artifact=p=>({path:p,bytes:fs.statSync(p).size,sha256:sha(fs.readFileSync(p))});
 const data={schemaVersion:1,kind:'external-dafny-parity-inventory',inventory:entry,restoreManifest:'docs/dafny-editor-inventory-manifest.json',restoreCommand:'injected test fixture restore'};
 fs.writeFileSync(descriptor,JSON.stringify(data));fs.writeFileSync(manifestPath,JSON.stringify({schemaVersion:1,fileCount:1,rawInventory:artifactBytes(payload),uncompressedBytes:payload.length,rowCount:entry.rows,frozenRowCount:1,frozenSha256:'0'.repeat(64),archive:artifact(archive),index:artifact(index)}));
 function artifactBytes(bytes){return {bytes:bytes.length,sha256:sha(bytes)};}
 return{dir,descriptor,file,entry,manifestPath,restore(){fs.mkdirSync(path.dirname(file),{recursive:true});fs.writeFileSync(file,payload);},close(){fs.rmSync(dir,{recursive:true,force:true});}};
}
test('inventory loader rejects absent or corrupt bulk instead of accepting the digest as rows',()=>{
 const f=fixture();try{
  assert.throws(()=>loadInventory(f.descriptor,f.dir),/Full parity inventory unavailable:.*Restore the checksum-bound bundle/);
  f.restore();assert.equal(loadInventory(f.descriptor,f.dir).features.length,f.entry.features);
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
test('fresh-checkout audit labels digest-only while strict loader still requires the verified bundle',()=>{
 const f=fixture();try{
  fs.mkdirSync(path.join(f.dir,'vscode/parity'),{recursive:true});for(const name of ['audit.cjs','inventory.cjs','input-presence.cjs'])fs.copyFileSync(path.join(repo,'vscode/parity',name),path.join(f.dir,'vscode/parity',name));
  fs.copyFileSync(path.join(repo,'docs/dafny-editor-audit.json'),path.join(f.dir,'docs/dafny-editor-audit.json'));
  const audit=()=>spawnSync(process.execPath,[path.join(f.dir,'vscode/parity/audit.cjs'),'--check'],{encoding:'utf8'});
  const absent=audit();assert.equal(absent.status,0,absent.stderr);assert.match(absent.stdout,/Digest-only:.*NOT run/);assert.throws(()=>loadInventory(f.descriptor,f.dir),/Full parity inventory unavailable/);
  assert.equal(spawnSync('git',['init','-q',f.dir]).status,0);fs.copyFileSync(path.join(repo,'.gitignore'),path.join(f.dir,'.gitignore'));
  const restore=spawnSync('python3',[path.join(repo,'scripts/coord-tools/dafny-parity-bulk.py'),'--repo',f.dir,'--manifest',f.manifestPath,'--restore'],{encoding:'utf8'});assert.equal(restore.status,0,restore.stderr);
  const present=audit();assert.equal(present.status,0,present.stderr);assert.match(present.stdout,/Audited/);
  fs.appendFileSync(f.file,' ');const corrupt=audit();assert.equal(corrupt.status,1);assert.match(corrupt.stderr,/checksum\/size mismatch/);
 }finally{f.close();}
});

test('ordinary paired runtime reports retain the original completeness predicate (injected reports)',()=>{
 fs.mkdirSync(path.join(repo,'.lake'),{recursive:true});const dir=fs.mkdtempSync(path.join(repo,'.lake/inventory-evidence-'));
 try{fs.mkdirSync(path.join(repo,'.lake'),{recursive:true});const inventory=inventoryFixture(),feature=inventory.features[0];feature.assessment={...feature.assessment,status:'complete',scenarioIds:['fixture-native'],testEvidence:[]};
  for(const target of ['local','dafny']){const file=path.join(dir,target+'.json');fs.writeFileSync(file,JSON.stringify({runId:'injected-'+target,target,status:'passed',checks:['fixture-native'],scenarios:[{id:'fixture-native',status:'passed'}]}));feature.assessment.testEvidence.push({target,status:'passed',assertion:'fixture-native',artifact:path.relative(repo,file)});}
  const {validate}=require('../parity/discover.cjs');assert.deepEqual(validate(inventory),[]);
  const file=path.join(dir,'local.json'),report=JSON.parse(fs.readFileSync(file));report.scenarios[0].status='missing';fs.writeFileSync(file,JSON.stringify(report));assert.ok(validate(inventory).some(e=>e.includes('unsupported completeness claim')));
 }finally{fs.rmSync(dir,{recursive:true,force:true});}
});

test('offline digest mode rejects inconsistent manifests and never hides present corrupt or escaping payloads',()=>{
 const f=fixture();try{
  assert.equal(checkOffline(f.descriptor,f.dir).mode,'digest-only');
  const original=fs.readFileSync(f.manifestPath),manifest=JSON.parse(original);manifest.rawInventory.sha256='f'.repeat(64);fs.writeFileSync(f.manifestPath,JSON.stringify(manifest));assert.throws(()=>checkOffline(f.descriptor,f.dir),/manifest mismatch/);fs.writeFileSync(f.manifestPath,original);
  f.restore();assert.equal(checkOffline(f.descriptor,f.dir).mode,'full');fs.appendFileSync(f.file,' ');assert.throws(()=>checkOffline(f.descriptor,f.dir),/checksum\/size mismatch/);fs.unlinkSync(f.file);
  fs.symlinkSync(path.join(os.tmpdir(),'absent-parity-'+process.pid),f.file);assert.throws(()=>checkOffline(f.descriptor,f.dir),/Unsafe symbolic input path/);assert.throws(()=>loadInventory(f.descriptor,f.dir),/Full parity inventory unavailable/);
 }finally{f.close();}
});

test('offline digest mode rejects a missing payload behind broken or escaping ancestor links',()=>{
 for(const target of ['missing-target','outside']){const f=fixture();try{
  const ancestor=path.dirname(f.file);fs.rmdirSync(ancestor);const destination=path.join(f.dir,target);if(target==='outside')fs.mkdirSync(destination);fs.symlinkSync(destination,ancestor,'dir');assert.throws(()=>checkOffline(f.descriptor,f.dir),/symbolic|Unsafe|escaping/i);
 }finally{f.close();}}
});
