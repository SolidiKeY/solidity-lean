#!/usr/bin/env node
// Verify fresh raw diagnostic results without building or changing verdicts.
import {readFileSync,existsSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
const base=resolve(process.argv[2]??'tests/upstream/baseline-20261028/probes/rechecked');
const cases=JSON.parse(readFileSync('tests/upstream/baseline-20261028/probes/cases.json'));
const sha=b=>createHash('sha256').update(b).digest('hex');
const read=p=>JSON.parse(readFileSync(p));
let provenance=0;
for(const name of cases.cases)for(const pipeline of cases.pipelines){
 const job=join(base,'runs',name,pipeline),record=read(join(job,'record.json'));
 assert.equal(record.case,name);assert.equal(record.pipeline,pipeline);
 assert.equal(sha(readFileSync(join(base,record.source))),record.sourceSha256);
 assert.equal(record.compilerSha256,'6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390');
 const rejected=cases.compilerRejections.includes(name);
 assert.equal(record.stages[0].exitCode,rejected?1:0);
 for(const stage of record.stages){assert.equal(stage.tool.timedOut,false);assert.equal(sha(readFileSync(join(base,stage.log))),stage.logSha256);}
 if(rejected)continue;
 assert.ok(record.stages.every(s=>s.exitCode===0));
 const fixture=read(join(job,'source.ast.json'));assert.equal(fixture.header.sourceSha256,record.sourceSha256);assert.equal(fixture.header.settings.viaIR,pipeline==='viaIR');
 const complete=read(join(job,'reader-complete.json'));assert.deepEqual(complete.functions,record.reader.functions);
 for(const control of record.provenanceControls??[]){assert.equal(control.result.exitCode,0);assert.equal(control.observation.status,'refused');provenance++;}
 if(name==='CommentRanges')assert.deepEqual(record.sourceLocations.map(r=>r.range.start),[{line:2,character:34},{line:2,character:77}]);
 if(name==='NominalStruct')assert.ok(complete.functions.some(f=>f.function==='f'&&f.status==='reader-refused'&&f.reason.includes('type declaration #3')));
 if(name==='PushedMember')assert.ok(complete.functions.some(f=>f.function==='increment'&&f.status==='reader-refused'&&f.reason.includes('pushed element')));
 if(name==='BadClause')assert.ok(complete.functions.some(f=>f.function==='bad'&&f.status==='reader-emitted'));
}
assert.equal(provenance,4);
console.log(JSON.stringify({cases:cases.cases.length,pipelines:cases.pipelines,compilerModes:44,readerModes:30,provenanceRefusals:provenance,nativeValidation:'blocked/not attempted by this reduced adapter'}));
