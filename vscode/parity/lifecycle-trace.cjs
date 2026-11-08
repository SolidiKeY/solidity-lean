#!/usr/bin/env node
'use strict';
// Reference discovery only: real default on-change verification, no explicit verify requests.
const assert=require('node:assert/strict');
const fs=require('node:fs'),path=require('node:path'),{pathToFileURL}=require('node:url'),{spawn}=require('node:child_process');
const {RpcPeer}=require('../src/rpc.cjs');
async function main(){
  if(process.argv[4]==='--configuration'){if(!process.argv[3])throw Error('Configuration needs a fresh output root');const out=path.resolve(process.argv[3]);if(fs.existsSync(out))throw Error('Choose a fresh configuration output');fs.mkdirSync(out,{recursive:true});const shared=path.join(out,'workspace');fs.mkdirSync(shared);fs.writeFileSync(path.join(shared,'configuration-owner.json'),JSON.stringify({root:out,cycle:require('node:crypto').randomUUID()}));for(const mode of require('./configuration-lifecycle.cjs').modes)await require('./stdio.cjs').main(['--scope','configuration','--configuration-mode',mode,'--configuration-workspace',shared,'--targets',mode==='default'?'dafny,local':'dafny','--workers','1','--obligations','1','--trials','1','--warmups','0','--dafny',path.resolve(process.argv[2]),'--output',path.join(out,mode)]);return;}

  if(process.argv[4]&&process.argv[4]!=='--migration')throw Error('Unknown lifecycle option');
  if(process.argv[4]==='--migration'&&!process.argv[3])throw Error('Migration run needs a separate output directory');
  const root=path.resolve(__dirname,'../..'),exe=path.resolve(process.argv[2]||path.join(root,'.cache/dafny-runtime/dafny/dafny'));
  const out=path.resolve(process.argv[3]||path.join(root,'tests/editor-parity/lifecycle')),workspace=path.join(root,'.cache/lifecycle-workspace');
  fs.mkdirSync(out,{recursive:true});fs.mkdirSync(workspace,{recursive:true});
  const trace=path.join(out,'dafny-lsp.jsonl');fs.writeFileSync(trace,'');
  fs.rmSync(path.join(out,'phases.json'),{force:true});
  if(process.argv[4]==='--migration')fs.rmSync(path.join(out,'migration.json'),{force:true});
  const append=r=>fs.appendFileSync(trace,JSON.stringify({time:Date.now(),...r})+'\n');
  const commandArgs=['server','--cores','1','--verification-time-limit','20','--notify-ghostness:true','--notify-line-verification-status:true'];
  const child=spawn(exe,commandArgs,{cwd:workspace,stdio:['pipe','pipe','pipe']});
  const closed=new Promise((resolve,reject)=>{child.once('close',code=>resolve(code));child.once('error',reject);});
  const log=fs.createWriteStream(path.join(out,'server.log'));child.stderr.pipe(log);
  const peer=new RpcPeer(child.stdout,child.stdin),states=[],diagnostics=[];
  const write=peer.write.bind(peer),receive=peer.receive.bind(peer);
  peer.write=m=>{append({direction:'client',message:m});return write(m);};
  peer.receive=m=>{append({direction:'server',message:m});return receive(m);};
  peer.onRequest('workspace/configuration',p=>p.items.map(()=>null));
  peer.onRequest('client/registerCapability',()=>null);peer.onRequest('window/workDoneProgress/create',()=>null);
  peer.onNotification('dafny/textDocument/symbolStatus',p=>states.push(p));
  peer.onNotification('textDocument/publishDiagnostics',p=>diagnostics.push(p));
  const uri=pathToFileURL(path.join(workspace,'lifecycle.dfy')).href;
  const initial=require('./configuration-lifecycle.cjs').initial;
  const texts=[initial,initial+'\n// edit\n',initial.replace('r := 1','r := 2'),initial+'\n// fixed\n'];
  const phases=[];let migrationResult;
  async function waitFor(version,status){
    const started=Date.now();
    while(!states.some(p=>p.uri===uri&&p.version===version&&p.namedVerifiables?.length&&p.namedVerifiables.every(s=>status===5?s.status===5:[4,5].includes(s.status))&&p.namedVerifiables.some(s=>s.status===status))){
      if(peer.closed||Date.now()-started>60000)throw Error('No automatic verification version '+version+' status '+status);
      await new Promise(r=>setTimeout(r,20));
    }
    if(status===4){
      while(!diagnostics.some(p=>p.uri===uri&&p.version===version&&p.diagnostics.some(d=>d.severity===1))){
        if(Date.now()-started>60000)throw Error('Missing broken-proof error diagnostic');await new Promise(r=>setTimeout(r,20));
      }
    }
    phases.push({version,status,text:texts[version-1],observed:states.filter(p=>p.uri===uri&&p.version===version),diagnostics:diagnostics.filter(p=>p.uri===uri&&p.version===version)});
  }
  try{
    await peer.request('initialize',{processId:process.pid,rootUri:pathToFileURL(workspace).href,capabilities:{workspace:{configuration:true},textDocument:{publishDiagnostics:{versionSupport:true},documentSymbol:{hierarchicalDocumentSymbolSupport:true}}}});
    peer.notify('initialized',{});
    peer.notify('textDocument/didOpen',{textDocument:{uri,languageId:'dafny',version:1,text:texts[0]}});await waitFor(1,5);
    for(let version=2;version<=4;version++){
      // Give the edit its own new declaration to avoid identical-symbol notification suppression.
      texts[version-1]+=`\nmethod Marker${version}() {}\n`;
      peer.notify('textDocument/didChange',{textDocument:{uri,version},contentChanges:[{text:texts[version-1]}]});await waitFor(version,version===3?4:5);
    }
    fs.writeFileSync(path.join(workspace,'lifecycle.dfy'),texts[3]);
    peer.notify('textDocument/didSave',{textDocument:{uri},text:texts[3]});
    await peer.request('textDocument/documentSymbol',{textDocument:{uri}});
    peer.notify('textDocument/didClose',{textDocument:{uri}});
    if(process.argv[4]==='--migration'){
      const migratedUri=pathToFileURL(path.join(workspace,'migration.dfy')).href;
      const broken='function GetConstant(): int ensures false { 1 }';
      const insertion='lemma {:neverVerify} HasNeverVerifyAttribute(p: nat, q: nat)\n  ensures true\n{\n}\n\n',lineDelta=5;
      const until=async(predicate,label)=>{const start=Date.now();while(!predicate()){if(peer.closed||Date.now()-start>60000)throw Error('Reference migration timed out: '+label);await new Promise(r=>setTimeout(r,10));}};
      peer.notify('textDocument/didOpen',{textDocument:{uri:migratedUri,languageId:'dafny',version:1,text:broken}});
      await until(()=>diagnostics.some(p=>p.uri===migratedUri&&p.version===1&&p.diagnostics.some(d=>d.severity===1&&d.relatedInformation?.length)),'original postcondition error');
      const original=diagnostics.filter(p=>p.uri===migratedUri&&p.version===1&&p.diagnostics.some(d=>d.severity===1)).at(-1);
      peer.notify('textDocument/didChange',{textDocument:{uri:migratedUri,version:2},contentChanges:[{range:{start:{line:0,character:0},end:{line:0,character:0}},text:insertion}]});
      await until(()=>diagnostics.some(p=>p.uri===migratedUri&&p.version===2&&p.diagnostics.some(d=>d.message.startsWith('Outdated: '))),'outdated diagnostic');
      const migrated=diagnostics.find(p=>p.uri===migratedUri&&p.version===2&&p.diagnostics.some(d=>d.message.startsWith('Outdated: ')));
      const old=original.diagnostics.find(d=>d.severity===1),next=migrated.diagnostics.find(d=>d.message.startsWith('Outdated: '));
      const shifted=range=>({start:{line:range.start.line+lineDelta,character:range.start.character},end:{line:range.end.line+lineDelta,character:range.end.character}});
      assert.equal(next.severity,2);assert.equal(next.message,'Outdated: '+old.message);
      assert.deepEqual(next.range,shifted(old.range));
      assert.deepEqual(next.relatedInformation,old.relatedInformation.map(r=>({...r,location:{...r.location,range:shifted(r.location.range)}})));
      peer.notify('textDocument/didChange',{textDocument:{uri:migratedUri,version:3},contentChanges:[{text:'method Repaired() {}\n'}]});
      await until(()=>diagnostics.some(p=>p.uri===migratedUri&&p.version===3&&p.diagnostics.length===0),'replacement clears old locations');
      const cleared=diagnostics.filter(p=>p.uri===migratedUri&&p.version===3).at(-1);
      peer.notify('textDocument/didClose',{textDocument:{uri:migratedUri}});
      migrationResult={status:'passed',scope:'Real pinned Dafny diagnostic migration; no local/editor parity or kernel certificate claim',fixtureSource:'Source/DafnyLanguageServer.Test/Various/DiagnosticMigrationTest.cs:ResolutionDiagnosticsContainPreviousVerificationResultsWhenCodeIsInsertedBefore',broken,insertion,lineDelta,original,migrated,cleared};
    }
    await peer.request('shutdown',null);peer.notify('exit',null);append({direction:'client',framingFinalized:true});
    let timer;const code=await Promise.race([closed,new Promise((_,reject)=>{timer=setTimeout(()=>reject(Error('Server exit timed out')),5000);})]).finally(()=>clearTimeout(timer));peer.frames.end();append({direction:'server',framingFinalized:true});
    if(code!==0)throw Error('Server exited '+code);
    if(migrationResult)fs.writeFileSync(path.join(out,'migration.json'),JSON.stringify({...migrationResult,serverExitCode:code},null,2)+'\n');
    fs.writeFileSync(path.join(out,'phases.json'),JSON.stringify({status:'passed',scope:'Reference server lifecycle discovery; no local/editor parity claim',command:exe,args:commandArgs,phases},null,2)+'\n');
    console.log('Reference lifecycle: open verified, edit verified, broken error, fixed verified, save, close; server exit 0.');
  }finally{if(child.exitCode===null)child.kill();peer.close();}
}
if(require.main===module)main().catch(e=>{console.error(e.stack);process.exitCode=1;});
