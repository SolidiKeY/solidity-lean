/** Filesystem/transport checks with fabricated rows; no semantic execution evidence. */
import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {closeSync,existsSync,mkdirSync,mkdtempSync,readFileSync,readdirSync,readlinkSync,renameSync,rmSync,symlinkSync,unlinkSync,writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {dirname,join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {openRun,fingerprint} from './output.mjs';
import {generate} from './generate.mjs';
const ROOT=resolve(dirname(fileURLToPath(import.meta.url)),'../..');
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
const observation=()=>({failed:false,returnData:'0x',exception:null,slots:['0','1'],storage:['0','0']});
function entry(record,{blocked=false}={}) {
  return {record:structuredClone(record),row:{index:record.index,sourceSha256:sha(record.source),optimizer:true,reference:observation(),
    results:['ir','irOptimized'].map(stage=>blocked?{stage,status:'blocked',phase:'lean',reason:'fuel exhausted'}:
      {stage,status:'agree',lean:observation()})}};
}
function fixture(t) {
  const dir=mkdtempSync(join(tmpdir(),'differential-yul-output-'));
  t.after(()=>rmSync(dir,{recursive:true,force:true}));
  const input=join(dir,'input');writeFileSync(input,'pinned input');
  return {dir,input,options:{requested:2,inputPaths:[input]}};
}
const records=()=>generate(2);

test('fresh external output records complete shape, exact source and content checksum',t=>{
  const {dir,options}=fixture(t),writer=openRun(join(dir,'run'),options),r=records();
  t.after(()=>writer.abort());
  assert.equal(existsSync(join(writer.directory,'report.json')),false);
  for (const record of r) writer.append(entry(record));
  const report=writer.finish();
  assert.equal(report.summary.requested,2);assert.equal(report.summary.executedPrograms,2);
  const bytes=readFileSync(join(writer.directory,'observations.jsonl'));
  assert.equal(report.observationsSha256,sha(bytes));
  assert.deepEqual(bytes.toString().trim().split('\n').map(JSON.parse).map(e=>e.record.source),r.map(e=>e.source));
  assert.deepEqual(JSON.parse(readFileSync(join(writer.directory,'report.json'))),report);
  assert.deepEqual(JSON.parse(readFileSync(join(writer.directory,'inputs.json'))).inputs,fingerprint(options.inputPaths));
  assert.throws(()=>writer.append(entry(r[0])),/not open/);assert.throws(()=>writer.finish(),/not open/);
});

test('checkout paths and external symlinks into checkout are rejected',t=>{
  const {dir,options}=fixture(t),alias=join(dir,'checkout');symlinkSync(ROOT,alias,'dir');
  assert.throws(()=>openRun(join(ROOT,'forbidden-run'),options),/outside checkout/);
  assert.throws(()=>openRun(join(alias,'forbidden-run'),options),/outside checkout/);
  assert.equal(existsSync(join(ROOT,'forbidden-run')),false);
});

test('existing run directories and report files are never overwritten',t=>{
  const {dir,options}=fixture(t),path=join(dir,'run'),writer=openRun(path,options);t.after(()=>writer.abort());
  assert.throws(()=>openRun(path,options),/EEXIST/);
  for (const record of records()) writer.append(entry(record));
  writeFileSync(join(path,'report.json'),'existing result');
  assert.throws(()=>writer.finish(),/EEXIST/);
  assert.equal(readFileSync(join(path,'report.json'),'utf8'),'existing result');
  assert.throws(()=>writer.finish(),/not open/);
});

test('truncated run cannot finish; blocked rows retain the full requested denominator',t=>{
  const {dir,options}=fixture(t),r=records(),short=openRun(join(dir,'short'),options);t.after(()=>short.abort());
  short.append(entry(r[0]));assert.throws(()=>short.finish(),/incomplete campaign/);
  assert.equal(existsSync(join(short.directory,'report.json')),false);
  assert.throws(()=>short.append(entry(r[1])),/not open/);
  const blocked=openRun(join(dir,'blocked'),options);t.after(()=>blocked.abort());
  for (const record of r) blocked.append(entry(record,{blocked:true}));
  const {summary}=blocked.finish();
  assert.equal(summary.requested,2);assert.equal(summary.executedPrograms,0);assert.equal(summary.agreeingPrograms,0);
  assert.equal(summary.stages.ir.blocked,2);assert.equal(summary.stages.irOptimized.blocked,2);
});

test('append validates exact source and shape, and snapshots mutable callers',t=>{
  const {dir,options}=fixture(t),r=records();
  for (const [index,alter] of [e=>e.record.source='forged',e=>e.row.results.pop(),e=>e.row.index=1].entries()) {
    const writer=openRun(join(dir,'invalid-'+index),options);t.after(()=>writer.abort());
    const invalid=entry(r[0]);alter(invalid);assert.throws(()=>writer.append(invalid));
    assert.throws(()=>writer.append(entry(r[0])),/not open/);assert.throws(()=>writer.finish(),/not open/);
    assert.equal(readFileSync(join(writer.directory,'observations.jsonl'),'utf8'),'');
  }
  const writer=openRun(join(dir,'snapshot'),options);t.after(()=>writer.abort());
  const first=entry(r[0]);writer.append(first);first.row.results[0].status='blocked';first.record.source='mutated';
  writer.append(entry(r[1]));assert.equal(writer.finish().summary.agreeingPrograms,2);
  const saved=JSON.parse(readFileSync(join(writer.directory,'observations.jsonl'),'utf8').split('\n')[0]);
  assert.equal(saved.record.source,r[0].source);assert.equal(saved.row.results[0].status,'agree');
});

test('changed input bytes or retargeted input symlink poison finalization',t=>{
  const {dir,input,options}=fixture(t),r=records();
  const changed=openRun(join(dir,'changed'),options);t.after(()=>changed.abort());
  for (const record of r) changed.append(entry(record));writeFileSync(input,'mutated bytes');
  assert.throws(()=>changed.finish(),/execution inputs changed/);
  assert.throws(()=>changed.finish(),/not open/);assert.equal(existsSync(join(changed.directory,'report.json')),false);
  const other=join(dir,'other');writeFileSync(other,'mutated bytes');
  const link=join(dir,'input-link');symlinkSync(input,link);
  const retargeted=openRun(join(dir,'retargeted'),{...options,inputPaths:[link]});t.after(()=>retargeted.abort());
  for (const record of r) retargeted.append(entry(record));unlinkSync(link);symlinkSync(other,link);
  assert.throws(()=>retargeted.finish(),/execution inputs changed/);
  assert.equal(existsSync(join(retargeted.directory,'report.json')),false);
});

test('fingerprint rejects duplicate canonical inputs and nonfiles',t=>{
  const {dir,input}=fixture(t),alias=join(dir,'alias');symlinkSync(input,alias);
  assert.throws(()=>fingerprint([input,alias]),/duplicate execution input/);
  assert.throws(()=>fingerprint([input,input]),/duplicate execution input/);
  assert.throws(()=>fingerprint([dir]),/must be a file/);assert.throws(()=>fingerprint([]),/required/);
  assert.throws(()=>fingerprint([null]),/invalid execution input path/);
  assert.equal(fingerprint([alias])[0].canonical,input);
});

test('failed low-level append poisons the writer', {skip:process.platform!=='linux'},t=>{
  const {dir,options}=fixture(t),writer=openRun(join(dir,'io-failure'),options);t.after(()=>writer.abort());
  // Close only this writer's owned descriptor to simulate a failed filesystem write.
  const path=join(writer.directory,'observations.jsonl');
  const descriptors=readdirSync('/proc/self/fd').filter(n=>{
    try {return readlinkSync('/proc/self/fd/'+n)===path;} catch {return false;}
  });
  assert.equal(descriptors.length,1);closeSync(Number(descriptors[0]));
  assert.throws(()=>writer.append(entry(records()[0])),/EBADF/);
  assert.throws(()=>writer.append(entry(records()[0])),/not open/);
  assert.throws(()=>writer.finish(),/not open/);assert.equal(existsSync(join(writer.directory,'report.json')),false);
});


test('saved observation mutation or replacement cannot be certified by finish',t=>{
  const {dir,options}=fixture(t);
  for (const replacement of [false,true]) {
    const writer=openRun(join(dir,replacement?'replacement':'mutation'),options);t.after(()=>writer.abort());
    for (const record of records()) writer.append(entry(record));
    const file=join(writer.directory,'observations.jsonl');
    if (replacement) {unlinkSync(file);writeFileSync(file,'substituted observations');}
    else writeFileSync(file,'truncated observations');
    assert.throws(()=>writer.finish(),/saved observations changed/);
    assert.equal(existsSync(join(writer.directory,'report.json')),false);
    assert.throws(()=>writer.finish(),/not open/);
  }
});

test('directory replacement or symlink redirection is rejected before append or report',t=>{
  const {dir,options}=fixture(t);
  for (const atFinish of [false,true]) {
    for (const symlink of [false,true]) {
      const path=join(dir,'redirect-'+atFinish+'-'+symlink),writer=openRun(path,options);t.after(()=>writer.abort());
      if (atFinish) for (const record of records()) writer.append(entry(record));
      renameSync(path,path+'-original');
      const target=path+'-target';mkdirSync(target);
      if (symlink) symlinkSync(target,path,'dir');else mkdirSync(path);
      assert.throws(()=>atFinish?writer.finish():writer.append(entry(records()[0])),/output directory changed/);
      assert.equal(existsSync(join(path,'report.json')),false);
      assert.equal(existsSync(join(target,'report.json')),false);
      assert.equal(existsSync(join(path,'observations.jsonl')),false);
      assert.throws(()=>writer.finish(),/not open/);
    }
  }
});

test('findings are hash-bound and metadata is snapshotted',t=>{
  const {dir,options}=fixture(t),metadata={fuel:12};
  const writer=openRun(join(dir,'run'),{...options,metadata});t.after(()=>writer.abort());
  metadata.fuel=99;
  for(const record of records()) writer.append(entry(record));
  const path=writer.writeFinding({stage:'ir',complete:false});
  const report=writer.finish();
  assert.deepEqual(report.metadata,{fuel:12});
  assert.deepEqual(report.findings,[{path,sha256:sha(readFileSync(join(writer.directory,path)))}]);
});
test('changed finding bytes cannot be finalized',t=>{
  const {dir,options}=fixture(t),writer=openRun(join(dir,'run'),options);t.after(()=>writer.abort());
  for(const record of records()) writer.append(entry(record));
  const path=writer.writeFinding({stage:'ir'});
  writeFileSync(join(writer.directory,path),'changed');
  assert.throws(()=>writer.finish(),/saved finding changed/);
  assert.equal(existsSync(join(writer.directory,'report.json')),false);
});
test('directory substitution cannot redirect a finding',t=>{
  const {dir,options}=fixture(t),writer=openRun(join(dir,'run'),options);t.after(()=>writer.abort());
  renameSync(writer.directory,join(dir,'original'));
  mkdirSync(writer.directory);
  assert.throws(()=>writer.writeFinding({stage:'ir'}),/output directory changed/);
  assert.deepEqual(readdirSync(writer.directory),[]);
});
