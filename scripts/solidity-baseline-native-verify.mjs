#!/usr/bin/env node
import {readFileSync,existsSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
const base=resolve(process.argv[2]??'tests/upstream/baseline-20261028/native-cache');
const cases=['NativePositive','SourceIdentifiers','CommentRanges','ConstantsEnums','SourceTypes','BadClause','CommentSpecPositive','ScalarMatrixValid','SourceLiterals','NominalStruct','PushedMember','PushedMemberPositive','TryContinue','TryContinuePositive','HexArrayExplicit','ExactRethrow','WrongRethrow','ComputedRevert','SpecBindings','PushedMemberMutation'];
const refused=new Set(['BadClause','NominalStruct','PushedMember','TryContinue','WrongRethrow','SpecBindings']);
const read=p=>JSON.parse(readFileSync(p));const sha=b=>createHash('sha256').update(b).digest('hex');
let observations=0;
for(const name of cases)for(const pipeline of ['legacy','viaIR']){
 const job=join(base,'runs',name,pipeline),r=read(join(job,'record.json'));assert.equal(r.pipeline,pipeline);assert.equal(r.case,name);assert.ok(r.typedImport.length);
 for(const s of r.stages){assert.equal(s.exitCode,0);assert.equal(s.timedOut,false);assert.equal(sha(readFileSync(join(base,s.log))),s.logSha256);if(s.command[0]==='lake')assert.ok(s.command.includes('--no-build'));}
 assert.equal(r.compilerSha256,'6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390');
 if(name==='ComputedRevert'){assert.ok(!r.runtime);continue;}
 const outcome=r.runtime[0];assert.equal(outcome.pipeline,pipeline);
 if(refused.has(name)){assert.equal(outcome.status,'broken');assert.equal(outcome.reason,'frontend import gaps');assert.ok(outcome.gaps.length);assert.equal(outcome.observed?.length??0,0);continue;}
 assert.equal(outcome.status,'working');const expected=read(join(job,'jobs.json'))[0].vectors;assert.equal(outcome.observed.length,expected.length);
 for(let i=0;i<expected.length;i++){const v=expected[i],o=outcome.observed[i];assert.equal(o.signature,v.signature);assert.equal(o.failed,v.failure);assert.deepEqual(o.values,v.expected);assert.deepEqual(o.revertBytes,v.revertBytes);observations++;}
 if(name==='NativePositive'){const n=r.negativeRuntime[0];assert.equal(n.status,'broken');assert.equal(n.reason,'runtime expectation mismatch: identifiers()');assert.deepEqual(n.observed[0].values,['7']);assert.deepEqual(n.expected.expected,['8']);assert.deepEqual(outcome.observed.at(-1).values,['3']);}
 if(name==='PushedMemberMutation')assert.deepEqual(outcome.observed.map(o=>o.values),[['107'],['207']]);
}
assert.equal(observations,122);
const b=read(join(base,'boundary-records.json'));assert.equal(b.length,6);
for(const x of b){assert.equal(x.timedOut,false);assert.equal(sha(readFileSync(x.log)),x.logSha256);if(x.control==='internal-entry'){assert.equal(x.exitCode,0);assert.match(x.result[0].reason,/no imported ABI entry/);}else assert.equal(x.exitCode,1);}
console.log(JSON.stringify({nativeModes:40,replayModes:38,matchingObservations:observations,expectedRefusalModes:12,negativeRuntimeControls:2,provenanceRefusals:4,internalAbiEntryRefusals:2,nativeValidationComplete:false,remaining:'nonzero msg.value external-entry discriminator'}));
