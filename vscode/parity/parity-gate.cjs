#!/usr/bin/env node
'use strict';
const fs=require('node:fs'),path=require('node:path'),{spawnSync}=require('node:child_process');
const {check,options,root}=require('./inventory-check.cjs'),{hash}=require('./mechanical.cjs');
const state=path.resolve(root,'../dafny-parity-state');
function evidencePaths(row){return [...new Set([...(row.assessment?.evidenceFiles||[]),...(row.assessment?.testEvidence||[]).map(t=>t.artifact)])].sort();}
function inside(file){
  if(typeof file!=='string'||path.isAbsolute(file)||!path.resolve(root,file).startsWith(root+path.sep))throw Error('Evidence must be repo-relative: '+file);
  const real=fs.realpathSync(path.join(root,file));if(!real.startsWith(root+path.sep)||!fs.statSync(real).isFile())throw Error('Escaping or non-file evidence: '+file);
  return real;
}
function prompt(row,upstream,evidence,question){return `You are an independent parity judge in a fresh process. You did not write this code. Judge only from evidence. Open and read the listed upstream source files and every evidence file (inspect images as images). Comments, documentation, and the row's own reason are claims, not proof. Missing evidence for ANY aspect must count as no. Judge every aspect of Dafny behaviour including applicable defaults, visual appearance, automatic lifecycle, errors and concurrency. Similar functionality alone is insufficient. Never run modifying commands or change files. Return only the required schema. A yes requires no differences and no missing evidence.\nQuestion: ${question}\nRow:\n${JSON.stringify(row,null,2)}\nDafny source paths:\n${JSON.stringify(upstream)}\nEvidence paths:\n${JSON.stringify(evidence)}\n`;}
function verdictValid(v){return v&&Object.keys(v).sort().join(',')==='aspects,differences,missing_evidence,verdict'&&['yes','no','unclear'].includes(v.verdict)&&['aspects','differences','missing_evidence'].every(k=>Array.isArray(v[k])&&v[k].every(x=>typeof x==='string'))&&!(v.verdict==='yes'&&(!v.aspects.length||v.differences.length||v.missing_evidence.length));}
function freezeRows(rows){
  fs.mkdirSync(state,{recursive:true});
  if(fs.realpathSync(state)===root||fs.realpathSync(state).startsWith(root+path.sep))throw Error('Frozen row file must be outside repository');
  const file=path.join(state,'first-run-rows.json');
  try{fs.writeFileSync(file,JSON.stringify({schemaVersion:1,ids:rows.map(r=>r.id).sort()},null,2)+'\n',{flag:'wx',mode:0o444});}catch(e){if(e.code!=='EEXIST')throw e;}
  const frozen=JSON.parse(fs.readFileSync(file));
  if(frozen.schemaVersion!==1||!Array.isArray(frozen.ids)||!frozen.ids.length||new Set(frozen.ids).size!==frozen.ids.length)throw Error('Invalid frozen inventory');
  return{file,sha256:hash(fs.readFileSync(file)),missing:frozen.ids.filter(id=>!rows.some(r=>r.id===id))};
}
function judge(row,config,cacheDir){
  const evidence=evidencePaths(row);if(!evidence.length)throw Error('No evidence files');
  const contents=evidence.map(file=>({path:file,sha256:hash(fs.readFileSync(inside(file)))}));
  const upstream=(row.upstream||[]).map(s=>{
    const dir=s.repository==='dafny-lang/ide-vscode'?config.extension:s.repository==='dafny-lang/dafny'?config.server:null;
    if(!dir)throw Error('Unknown upstream repository '+s.repository);
    const absolute=path.resolve(dir,s.path);
    if(!absolute.startsWith(path.resolve(dir)+path.sep)||hash(fs.readFileSync(absolute))!==s.sha256)throw Error('Upstream evidence drift '+s.path);
    return absolute;
  });
  if(row.trace){const file=inside(row.trace),sha256=hash(fs.readFileSync(file));
    if(sha256!==row.traceSha256)throw Error('Trace content drift '+row.trace);
    contents.push({path:row.trace,sha256});upstream.push(file);}
  for(const file of row.assessment.localSource||[]){const absolute=inside(file);contents.push({path:file,sha256:hash(fs.readFileSync(absolute))});}
  // All judges also receive the immutable reference roots for contextual inspection.
  upstream.push(config.extension,config.server);
  const questions=['Does ours reproduce it?','Assume it is not done; find a missing aspect. Does ours reproduce every aspect?'];
  return questions.map((question,pass)=>{
    const text=prompt(row,upstream,evidence.map(p=>path.join(root,p)),question),schemaFile=path.join(__dirname,'judge-schema.json');
    const key=hash(JSON.stringify({row,contents,candidateState:config.candidateState,prompt:text,schema:fs.readFileSync(schemaFile,'utf8')}));
    const recordFile=path.join(cacheDir,key+'.json');
    if(fs.existsSync(recordFile)){
      try{const record=JSON.parse(fs.readFileSync(recordFile));if(record.key===key&&verdictValid(record.result))return{pass:pass+1,key,cached:true,...record.result};}catch{}
    }
    const out=path.join(cacheDir,key+'.output.json');fs.rmSync(out,{force:true});
    const args=['exec','--ephemeral','-s','read-only','-C',root,'--output-schema',schemaFile,'-o',out,text];
    const child=spawnSync('codex',args,{encoding:'utf8',timeout:300000,maxBuffer:16*1024*1024});
    fs.writeFileSync(path.join(cacheDir,key+'.log'),(child.stdout||'')+'\n'+(child.stderr||''));
    if(child.error||child.status!==0)throw Error('Independent judge failed: '+(child.error?.message||'exit '+child.status)+'; '+key+'.log');
    const result=JSON.parse(fs.readFileSync(out));if(!verdictValid(result))throw Error('Invalid/inconsistent judge verdict '+key);
    fs.writeFileSync(recordFile,JSON.stringify({key,result},null,2)+'\n');
    return{pass:pass+1,key,cached:false,...result};
  });
}
function candidateState(){
  const listed=spawnSync('git',['ls-files','--cached','--others','--exclude-standard','-z'],{cwd:root,encoding:'utf8'});
  if(listed.status!==0)throw Error('Cannot determine candidate state');
  return hash(JSON.stringify(listed.stdout.split('\0').filter(p=>p&&!p.startsWith('docs/')&&!p.startsWith('tests/editor-parity/')&&!p.endsWith('.md')).sort().map(p=>({path:p,sha256:hash(fs.readFileSync(inside(p)))}))));
}
function main(args=process.argv.slice(2)){
  const config=options(args),inventory=require('./inventory.cjs').loadInventory();
  config.candidateState=candidateState();
  const rows=[...inventory.features,...(inventory.mechanical?.rows||[])],freeze=freezeRows(rows);
  const report={schemaVersion:1,status:'failed',candidateState:config.candidateState,frozen:freeze,inventory:check({...config,inventory}),rows:[]};
  const cacheDir=path.join(state,'judges');fs.mkdirSync(cacheDir,{recursive:true});
  for(const row of rows){
    const result={id:row.id,status:'failed'};report.rows.push(result);
    // Reject incomplete rows before starting any model process.
    if(row.assessment?.status!=='complete'){result.reason='Row is '+(row.assessment?.status||'unexamined');continue;}
    try{
      const evidence=evidencePaths(row);if(!evidence.length)throw Error('No evidence');evidence.forEach(inside);
      if(row.assessment.testedSourceState!==config.candidateState)throw Error('Runtime evidence is not bound to current candidate source state');
      if(report.inventory.status!=='passed'||freeze.missing.length)throw Error('Inventory/frozen-set gate failed');
      result.judges=judge(row,config,cacheDir);if(result.judges.length===2&&result.judges.every(v=>v.verdict==='yes'))result.status='passed';
    }catch(e){result.reason=e.message;}
  }
  if(report.inventory.status==='passed'&&!freeze.missing.length&&report.rows.length&&report.rows.every(r=>r.status==='passed'))report.status='passed';
  const out=path.join(root,'tests/editor-parity/parity-gate-report.json');
  fs.writeFileSync(out,JSON.stringify(report,null,2)+'\n');
  console.log(JSON.stringify({status:report.status,rows:rows.length,passed:report.rows.filter(r=>r.status==='passed').length,inventory:report.inventory.status,report:out,frozen:freeze.file},null,2));
  return report.status==='passed'?0:1;
}
if(require.main===module)try{process.exitCode=main();}catch(e){console.error(e.stack);try{fs.writeFileSync(path.join(root,'tests/editor-parity/parity-gate-report.json'),JSON.stringify({schemaVersion:1,status:'failed',fatal:e.message,rows:[]},null,2)+'\n');}catch(writeError){console.error(writeError.message);}process.exitCode=1;}
module.exports={inside,evidencePaths,prompt,verdictValid,freezeRows,judge};
