import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,readdirSync,writeFileSync,mkdtempSync,symlinkSync,unlinkSync,lstatSync,rmSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {tmpdir} from 'node:os';
import {sha} from './index.mjs';
import {assertOracle} from './expect.mjs';
import {validateReferenceReport} from './reference.mjs';
const DIR=process.env.HOST1_REPORT_DIR??'/workspace/vy5-composition/host1-help-20261102/native-final-v2';
const json=p=>JSON.parse(readFileSync(p));
const originalHash=sha(readFileSync(join(DIR,'report.json')));
function sandbox(change){const dir=mkdtempSync(join(tmpdir(),'host1-mutant-'));try{for(const file of readdirSync(DIR))symlinkSync(resolve(DIR,file),join(dir,file));const put=(file,data)=>{const p=join(dir,file);if(lstatSync(p).isSymbolicLink())unlinkSync(p);writeFileSync(p,typeof data==='string'?data:JSON.stringify(data));};change(dir,put);assert.throws(()=>validateReferenceReport(dir));}finally{rmSync(dir,{recursive:true,force:true});assert.equal(sha(readFileSync(join(DIR,'report.json'))),originalHash);}}
test('all56 ordered native observations and source/settings/helper fingerprints replay',()=>assert.deepEqual(validateReferenceReport(DIR),{profiles:4,calls:56,fullProofGate:'pending'}));
for(const [name,mutate]of [['missing profile',r=>r.profiles.pop()],['reordered profile',r=>r.profiles.reverse()],['missing call',r=>r.rows.pop()],['reordered calls',r=>r.rows.reverse()],['mismatch cannot downgrade to blocked',r=>r.rows[0].status='blocked'],['stale source hash',r=>r.sourceSha256='0'.repeat(64)],['stale freeze',r=>r.freezeSha256='0'.repeat(64)],['stale actual receipt',r=>r.rows[0].receiptSha256='0'.repeat(64)],['false full closure',r=>r.fullProofGate='pass']])test(name,()=>sandbox((dir,put)=>{const r=json(join(dir,'report.json'));mutate(r);put('report.json',r);}));
for(const [name,mutate]of [['wrong oracle bytes',f=>f.profiles[0].cases[2].output='0xaabbccdd'],['wrong slot oracle',f=>f.profiles[0].cases[0].post[f.profiles[0].factory].persistent['0x'+'00'.repeat(32)]='0x'+'00'.repeat(31)+'09'],['wrong source',f=>f.sourceSha256='0'.repeat(64)],['wrong producer body',f=>f.helperHashes['scripts/host1-finalization/observe.mjs']='0'.repeat(64)],['wrong compiler version',f=>f.compiler='0.0.0'],['wrong optimizer profile',f=>f.profiles[0].optimized=true]])test(name,()=>sandbox((dir,put)=>{const f=json(join(dir,'freeze.json'));mutate(f);const bytes=JSON.stringify(f);put('freeze.json',bytes);const r=json(join(dir,'report.json'));r.freezeSha256=sha(bytes);put('report.json',r);}));
for(const [name,mutate]of [
 ['same bytes wrong final balance',r=>r.post[r.request.caller].balance='0'],
 ['same bytes coordinated wrong retained world',r=>{const a=r.request.to;for(const w of [r.post,r.messagePost,r.frames[0].post])w[a].nonce='17';}],
 ['same-length wrong full payload',r=>{r.message.bytes='0xaabbccdd';r.frames[0].output.bytes='0xaabbccdd';}],
 ['missing state domain',r=>r.domain.pop()],['missing frame memory',r=>delete r.frames[0].memory],
 ['wrong high log topic',r=>{r.message.logs[0].topics[1]='0x'+'00'.repeat(31)+'55';r.frames[0].output.logs[0].topics[1]=r.message.logs[0].topics[1];}],
 ['wrong CREATE address',r=>{r.message.createdAddress=r.request.caller;r.frames[0].createdAddress=r.request.caller;}],
 ])test(name,()=>sandbox((dir,put)=>{const report=json(join(dir,'report.json')),row=report.rows[name==='same-length wrong full payload'?2:name==='wrong high log topic'?1:name==='wrong CREATE address'?0:4],r=json(join(dir,row.receipt));mutate(r);const bytes=JSON.stringify(r);put(row.receipt,bytes);row.receiptSha256=sha(bytes);put('report.json',report);}));
test('missing receipt file never becomes a zero observation',()=>sandbox((dir,put)=>{const report=json(join(dir,'report.json'));put(report.rows[0].receipt,'null');}));

test('coordinated stale code-hash provenance rejected',()=>sandbox((dir,put)=>{const f=json(join(dir,'freeze.json'));f.profiles[0].codeHashes.Child.runtime='0'.repeat(64);const bytes=JSON.stringify(f);put('freeze.json',bytes);const r=json(join(dir,'report.json'));r.freezeSha256=sha(bytes);put('report.json',r);}));
test('additional compiler settings cannot hide behind a coordinated input hash',()=>sandbox((dir,put)=>{const f=json(join(dir,'freeze.json')),input=json(join(dir,'legacy-noopt.input.json'));input.settings.optimizer.details={yul:false};put('legacy-noopt.input.json',input);f.profiles[0].inputSha256=sha(JSON.stringify(input));const bytes=JSON.stringify(f);put('freeze.json',bytes);const r=json(join(dir,'report.json'));r.freezeSha256=sha(bytes);put('report.json',r);}));
