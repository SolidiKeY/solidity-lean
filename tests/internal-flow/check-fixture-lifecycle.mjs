#!/usr/bin/env node
// HOST ONLY. Fake lake/children and two fake reports test lifecycle, never Lean.
import * as fs from "node:fs";
import {resolve} from "node:path";
import {pathToFileURL} from "node:url";
import {spawn,spawnSync} from "node:child_process";
import {setTimeout as delay} from "node:timers/promises";
import assert from "node:assert/strict";
import {MAX_CHILD_OUTPUT_BYTES,visitFixturesAsync,StageJournal,run} from "./fixture-cache.mjs";
const out=process.argv[2];assert(out?.startsWith("/"));fs.mkdirSync(out,{recursive:true});
const bin=out+"/bin";fs.mkdirSync(bin);const lake=bin+"/lake";
fs.writeFileSync(lake,`#!/usr/bin/env node
const fs=require('node:fs'),{spawn}=require('node:child_process');
const mode=process.argv[2];
const good="'a' depends on axioms: [propext]\\n'b' does not depend on any axioms\\n";
if(mode==='wait'){
 process.on('SIGTERM',()=>{});
 const g=spawn(process.execPath,['-e',"process.on('SIGTERM',()=>{});setInterval(()=>{},1000)"],{stdio:'ignore'});
 setTimeout(()=>{fs.writeSync(1,'READY '+process.pid+' '+g.pid+'\\n');fs.writeSync(2,'stderr prefix\\n');},100);
 setInterval(()=>{},1000);
}else if(mode==='overflow'||mode==='mixed'){
 fs.writeSync(1,Buffer.alloc(mode==='mixed'?600:1200,120));if(mode==='mixed')fs.writeSync(2,Buffer.alloc(600,121));
}else if(mode==='signal'){process.kill(process.pid,'SIGTERM');
}else{
 if(mode==='grandchild')spawn(process.execPath,['-e','setInterval(()=>{},1000)'],{stdio:'ignore'}).unref();
 const text=mode==='missing'?good.split('\\n')[0]:mode==='duplicate'?good+good:mode==='reordered'?good.trim().split('\\n').reverse().join('\\n'):mode==='wrong'?good.replace('propext','BAD'):mode==='diagnostic'?good+'error: test\\n':good;
 fs.writeSync(1,Buffer.from([0xc3]));fs.writeSync(1,Buffer.concat([Buffer.from([0xa9,10]),Buffer.from(text)]));fs.writeSync(2,'warning: stderr\\n');
 if(mode==='fail')process.exit(7);
}
`,{mode:0o755});
const module=pathToFileURL(resolve('tests/internal-flow/fixture-cache.mjs')).href;
const witness=out+'/witness.mjs';
fs.writeFileSync(witness,`import * as fs from 'node:fs';import {runInNewContext} from 'node:vm';
import {StageJournal,run,cliFailure,splitBatchReports} from ${JSON.stringify(module)};
const [mode,out,limit]=process.argv.slice(2);
class FaultJournal extends StageJournal {record(event,data){super.record(event,data);if(event==='child-spawn'&&mode==='journal-fail'){const saved=this.path;this.path='/dev/full';try{super.record('injected-real-IO-failure',{});}finally{this.path=saved;}}}}
const journal=new FaultJournal(out);
const source=fs.readFileSync('tests/internal-flow/fixture-cache.mjs','utf8');
const guard=source.slice(source.indexOf('function guard(log) {'),source.indexOf('mkdirSync(dir,'));
try{await journal.measureAsync('root',async()=>{
 const log=await run([mode,'literal space','',"$literal"],out+'/child.log',journal,Number(limit));
 journal.measure('reports',()=>{splitBatchReports(log,[{names:['a','b']}]);runInNewContext(guard+'\\nguard(log)',{log,expected:{pins:{a:['propext'],b:[]}}});});
 journal.measure('post-auth-marker',()=>fs.writeFileSync(out+'/TEST_ONLY_SUCCESS','complete fake test, NOT cache evidence'));
});}catch(error){cliFailure(error);}
`);
const env={...process.env,PATH:bin+':'+process.env.PATH};
const rows=[];const jobs=[];
function events(dir){return fs.readFileSync(dir+'/fixture-stages.jsonl','utf8').trim().split('\n').map(x=>JSON.parse(x));}
function alive(pid){try{return fs.readFileSync('/proc/'+pid+'/stat','utf8').split(') ')[1][0]!=='Z';}catch{return false;}}
async function waitFor(fn){for(let i=0;i<200;i++){if(fn())return;await delay(20);}throw Error('host control deadline');}
function start(name,mode,extraEnv={},limit=1024){
 const dir=out+'/'+name;fs.mkdirSync(dir);
 const p=spawn(process.execPath,[witness,mode,dir,String(limit)],{env:{...env,V12_LIFECYCLE_OWNER:out,...extraEnv},stdio:['ignore','pipe','pipe']});
 let stdout='',stderr='';p.stdout.on('data',b=>stdout+=b);p.stderr.on('data',b=>stderr+=b);
 const done=new Promise(resolve=>p.on('close',(code,signal)=>resolve({code,signal,stdout,stderr})));
 const job={dir,p,done};jobs.push(job);return job;
}
function cleanup(job){
 if(job.cleaned)return;job.cleaned=true;
 if(!fs.existsSync(job.dir+'/fixture-stages.jsonl'))return;
 for(const row of events(job.dir).filter(r=>r.event==='child-spawn'&&r.process_group)){
  assert(row.process_group>0&&row.process_group!==process.pid);
  let owned=false;
  for(const entry of fs.readdirSync('/proc').filter(n=>/^\d+$/.test(n)))try{
    const stat=fs.readFileSync('/proc/'+entry+'/stat','utf8').split(') ')[1].split(' ');
    if(Number(stat[2])!==row.process_group||stat[0]==='Z')continue;
    assert(fs.readFileSync('/proc/'+entry+'/environ','utf8').split('\0').includes('V12_LIFECYCLE_OWNER='+out),'refuse nonowned group');owned=true;
  }catch(error){if(error.code!=='ENOENT'&&error.code!=='ESRCH')throw error;}
  if(owned)try{process.kill(-row.process_group,'SIGKILL');}catch(e){assert.equal(e.code,'ESRCH');}
 }
}
try {
 assert.equal(MAX_CHILD_OUTPUT_BYTES,64*1024*1024);
 // Compare output grouping/UTF8/arguments and failure status against REAL legacy
 // spawnSync, not a replacement report parser or a Lean process.
 for(const mode of ['good','fail','signal','missing','duplicate','reordered','wrong','diagnostic','overflow','mixed','grandchild']){
  const base=mode==='grandchild'?null:spawnSync('lake',[mode,'literal space','','$literal'],{env,encoding:'utf8',maxBuffer:1024});
  const job=start(mode,mode),result=await job.done,ev=events(job.dir);
  const success=mode==='good'||mode==='grandchild';assert.equal(result.code,success?0:mode==='fail'?7:1);
  assert.equal(fs.existsSync(job.dir+'/TEST_ONLY_SUCCESS'),success);
  if(success||mode==='fail')assert(!base||fs.readFileSync(job.dir+'/child.log','utf8')===(base.stdout??'')+(base.stderr??''));
  const args=ev.find(r=>r.event==='child-spawn').args;assert.deepEqual(args,[mode,'literal space','','$literal']);
  if(mode==='overflow'||mode==='mixed'){
   assert.equal(base.error.code,'ENOBUFS');
   assert(ev.some(r=>r.event==='failure'&&r.error.code==='ENOBUFS'));
   assert(fs.statSync(job.dir+'/child.log.stdout').size+fs.statSync(job.dir+'/child.log.stderr').size<=1024);
  }
  assert(ev.some(r=>r.event=== (success?'end':'failure')&&r.stage==='root'));
  if(!success)assert(!ev.some(r=>r.stage==='post-auth-marker'));
  assert(ev.every(r=>r.elapsed_ns===undefined||BigInt(r.elapsed_ns)>=0n));
  cleanup(job);rows.push({case:mode,...result,legacy_buffer_error:base?.error?.code,legacy_stdout_bytes:Buffer.byteLength(base?.stdout??''),legacy_stderr_bytes:Buffer.byteLength(base?.stderr??''),status:'pass'});
 }
 // Spawn failure must not advance parsing/authentication or leave handlers.
 const missing=start('spawn-missing','good',{PATH:out+'/absent'}),mr=await missing.done;
 assert.equal(mr.code,1);assert(events(missing.dir).some(r=>r.event==='failure'&&r.error.code==='ENOENT'));
 assert(!fs.existsSync(missing.dir+'/TEST_ONLY_SUCCESS'));rows.push({case:'spawn-missing',status:'pass'});
 // Direct parent SIGTERM: its own child group (including TERM-ignoring
 // descendants) is shut down and the parent preserves actual signal exit.
 const signal=start('parent-term','wait');
 await waitFor(()=>fs.existsSync(signal.dir+'/child.log.stdout')&&fs.readFileSync(signal.dir+'/child.log.stdout','utf8').includes('READY'));
 const ids=fs.readFileSync(signal.dir+'/child.log.stdout','utf8').trim().split(' ').slice(1).map(Number);
 signal.p.kill('SIGTERM');const sr=await signal.done;assert.equal(sr.signal,'SIGTERM');
 await waitFor(()=>ids.every(pid=>!alive(pid)));
 assert(fs.readFileSync(signal.dir+'/child.log.stderr','utf8').includes('stderr prefix'));
 assert(events(signal.dir).some(r=>r.event==='unfinished'&&r.stage==='root'));
 assert(!fs.existsSync(signal.dir+'/TEST_ONLY_SUCCESS'));rows.push({case:'parent-term',status:'pass'});
 // Uncatchable kill: no fabricated terminal event; an EXTERNAL supervisor must
 // clean the recorded owned group, as the production container does on exit.
 const killed=start('parent-kill','wait');
 await waitFor(()=>fs.existsSync(killed.dir+'/child.log.stdout')&&fs.readFileSync(killed.dir+'/child.log.stdout','utf8').includes('READY'));
 killed.p.kill('SIGKILL');const kr=await killed.done;assert.equal(kr.signal,'SIGKILL');
 assert(!events(killed.dir).some(r=>r.stage==='root'&&r.event!=='start'));
 assert(events(killed.dir).some(r=>r.stage==='root'&&r.state==='unfinished'));
 assert(!fs.existsSync(killed.dir+'/TEST_ONLY_SUCCESS'));cleanup(killed);rows.push({case:'parent-kill-supervised',status:'pass'});
 // Actual write/fsync failures after spawn must await/reap before returning.
 for(const kind of ['journal-fail','output-fail']){
  const name=kind,dir=out+'/'+name;fs.mkdirSync(dir);
  if(kind==='output-fail')fs.symlinkSync('/dev/full',dir+'/child.log.stdout');
  const p=spawn(process.execPath,[witness,kind,dir,'1024'],{env:{...env,V12_LIFECYCLE_OWNER:out},stdio:['ignore','pipe','pipe']});
  p.stdout.resume();p.stderr.resume();const result=await new Promise(resolve=>p.on('close',(code,signal)=>resolve({code,signal})));
  assert.equal(result.code,1);const ev=events(dir),row=ev.find(r=>r.event==='child-spawn');
  assert(ev.some(r=>r.event==='failure'&&['ENOSPC','EINVAL'].includes(r.error.code)));
  assert(ev.some(r=>r.event==='child-group-cleanup'&&r.observed_close!==null));
  await waitFor(()=>!alive(row.child_pid));assert(!fs.existsSync(dir+'/TEST_ONLY_SUCCESS'));
  rows.push({case:kind,status:'pass'});
 }
 // Actual outer timeout with the existing 10s grace, reduced TEST interval.
 const td=out+'/outer-timeout';fs.mkdirSync(td);
 const tr=spawnSync('timeout',['--signal=TERM','--kill-after=10s','0.5',process.execPath,witness,'wait',td,'1024'],{env,encoding:'utf8'});
 assert.equal(tr.status,124);assert(fs.readFileSync(td+'/child.log.stdout','utf8').includes('READY'));
 assert(!fs.existsSync(td+'/TEST_ONLY_SUCCESS'));cleanup({dir:td});rows.push({case:'outer-timeout',actual_exit:124,status:'pass'});
 const order=[];await assert.rejects(()=>visitFixturesAsync([0,1,2],async i=>{order.push('start'+i);await delay(2);order.push('end'+i);if(i===1)throw Error('fail');}));
 assert.deepEqual(order,['start0','end0','start1','end1']);rows.push({case:'awaited-serial-failfast',order,status:'pass'});
 const beforeHandlers=process.listenerCount('SIGTERM'),previousPath=process.env.PATH;process.env.PATH=env.PATH;
 const direct=out+'/direct';fs.mkdirSync(direct);const journal=new StageJournal(direct);
 try{await run(['good'],direct+'/one.log',journal,1024);await run(['good'],direct+'/two.log',journal,1024);}finally{process.env.PATH=previousPath;}
 assert.equal(process.listenerCount('SIGTERM'),beforeHandlers);
 journal.measure('protected-fields',()=>0,{id:-1,state:'complete'});
 const guarded=events(direct).find(e=>e.event==='start'&&e.stage==='protected-fields');assert.equal(guarded.state,'unfinished');assert.notEqual(guarded.id,-1);
 assert.throws(()=>journal.measure('wrong-sync',()=>Promise.resolve()));
 rows.push({case:'repeated-run-handler-restoration-and-stage-fields',status:'pass'});
 fs.writeFileSync(out+'/host-lifecycle-results.json',JSON.stringify({status:'pass',no_Lean:true,not_cache_or_proof_evidence:true,rows},null,2)+'\n');
 console.log(JSON.stringify({status:'pass',no_Lean:true,cases:rows.length}));
} finally {for(const job of jobs){if(job.p.exitCode===null&&job.p.signalCode===null)job.p.kill('SIGKILL');cleanup(job);}}
