#!/usr/bin/env node
'use strict';
// Independently enumerate ALL reference test files and registration sites.
// Reconciliation reads the feature inventory only after enumeration finishes.
const fs=require('node:fs');
const {join,resolve}=require('node:path');
const {spawnSync}=require('node:child_process');
const {createHash}=require('node:crypto');
const repo=resolve(__dirname,'../..'),output=join(repo,'docs/dafny-editor-audit.json');
const digest=x=>createHash('sha256').update(x).digest('hex');
function enumerate(directory,component){
  const git=spawnSync('git',['-C',directory,'ls-files','-z'],{encoding:'utf8'});
  if(git.status!==0)throw new Error('Cannot enumerate reference checkout');
  const paths=git.stdout.split('\0').filter(p=>component==='server'?p.startsWith('Source/DafnyLanguageServer.Test/')&&p.endsWith('.cs'):p.startsWith('src/test/')&&p.endsWith('.ts')).sort();
  return paths.map(path=>{
    const bytes=fs.readFileSync(join(directory,path)),text=bytes.toString('utf8');
    const regex=component==='server'?/\[(Fact|Theory)\b/g:/\b(test|it|suite|describe)\s*\(/g;
    const cases=[...text.matchAll(regex)].map(m=>{
      const line=text.slice(0,m.index).split('\n').length,following=text.slice(m.index,m.index+1600);
      const name=component==='server'?following.match(/\b(?:public|internal)\s+(?:async\s+)?(?:Task(?:<[^>]+>)?|void)\s+(\w+)\s*\(/)?.[1]:following.match(/^[^(]+\(\s*(['"`])([^\n]*?)\1/)?.[2];
      return {id:`${component}:${path}:${line}`,line,registration:m[1],name:name||null,status:'unexamined',runtimeEvidence:[]};
    });
    return {component,path,sha256:digest(bytes),cases};
  });
}
function scan(extension,server,inventoryPath=join(repo,'docs/dafny-editor-features.json')){
  const testFiles=[...enumerate(extension,'extension'),...enumerate(server,'server')];
  const inventory=require('./inventory.cjs').loadInventory(inventoryPath);
  for(const file of testFiles){
    file.featureIds=inventory.features.filter(f=>f.upstream.some(s=>s.path===file.path&&s.repository===`dafny-lang/${file.component==='server'?'dafny':'ide-vscode'}`)).map(f=>f.id);
    for(const c of file.cases)c.reason=file.featureIds.length?'Related feature family discovered; this individual upstream test has not been ported and run against both targets.':'Unmapped reference test; inspect and add a targeted scenario before claiming coverage.';
  }
  const commit=dir=>spawnSync('git',['-C',dir,'rev-parse','HEAD'],{encoding:'utf8'}).stdout.trim();
  return {schemaVersion:1,fullParityEstablished:false,upstream:{extension:commit(extension),server:commit(server)},
    method:'Enumerate tracked upstream test files and Fact/Theory/TypeScript registration sites independently, then reconcile paths with the feature inventory. Registration sites are discovery candidates, not passes; dynamic cases are not expanded.',
    counts:{testFiles:testFiles.length,registrationSites:testFiles.reduce((n,f)=>n+f.cases.length,0),unmappedFiles:testFiles.filter(f=>!f.featureIds.length).length},
    fileSetSha256:digest(JSON.stringify(testFiles.map(f=>[f.component,f.path,f.sha256]))),testFiles};
}
function validateIndex(audit){
  const errors=[];
  if(audit.schemaVersion!==1||audit.fullParityEstablished!==false)errors.push('invalid audit schema/parity claim');
  if(!audit.testFiles?.length)return [...errors,'empty audit'];
  const files=audit.testFiles;
  if(audit.counts?.testFiles!==files.length||audit.counts.registrationSites!==files.reduce((n,f)=>n+f.cases.length,0))errors.push('test index count drift');
  if(audit.fileSetSha256!==digest(JSON.stringify(files.map(f=>[f.component,f.path,f.sha256]))))errors.push('test file set drift');
  const ids=new Set();for(const f of files){
    if(!/^[0-9a-f]{64}$/.test(f.sha256))errors.push('invalid source digest');
    for(const c of f.cases){
      if(ids.has(c.id))errors.push('duplicate registration');ids.add(c.id);
      if(c.status!=='unexamined'||c.runtimeEvidence.length)errors.push('source registration cannot certify a runtime pass');
    }
  }
  for(const component of ['extension','server'])if(!/^[a-f0-9]{40}$/.test(audit.upstream?.[component]||''))errors.push('invalid audit source pin '+component);
  return errors;
}
function validate(audit){
  const errors=validateIndex(audit),inventory=require('./inventory.cjs').loadInventory();
  for(const component of ['extension','server'])if(audit.upstream?.[component]!==inventory.upstream[component].commit)errors.push('source pin drift');
  return errors;
}
function main(args=process.argv.slice(2)){
  if(args[0]==='--check'){
    const audit=JSON.parse(fs.readFileSync(output,'utf8')),checked=require('./inventory.cjs').checkOffline(),errors=checked.mode==='full'?validate(audit):validateIndex(audit);if(errors.length)throw new Error(errors.join('\n'));
    if(checked.mode==='digest-only'){process.stdout.write('Digest-only: committed audit index structure and inventory/restore digest checked; full inventory pin reconciliation NOT run (H44 bundle absent). No runtime/parity pass.\n');return;}
    process.stdout.write(`Audited ${audit.counts.testFiles} test files and ${audit.counts.registrationSites} registration sites; unported cases remain unexamined.\n`);return;
  }
  const value=k=>{const i=args.indexOf(k);if(i<0||!args[i+1])throw new Error('Required '+k);return resolve(args[i+1]);};
  const actual=scan(value('--extension'),value('--server'));
  if(args.includes('--check-source')){if(JSON.stringify(actual)!==JSON.stringify(JSON.parse(fs.readFileSync(output,'utf8'))))throw new Error('Independent test discovery drifted; inspect and reconcile');}
  else if(args.includes('--write'))fs.writeFileSync(output,JSON.stringify(actual,null,2)+'\n');
  else process.stdout.write(JSON.stringify(actual,null,2)+'\n');
}
module.exports={enumerate,scan,validate,validateIndex};
if(require.main===module)try{main();}catch(e){process.stderr.write(e.stack+'\n');process.exitCode=1;}
