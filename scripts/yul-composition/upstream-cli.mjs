/** Standalone corpus recovery; original reports and shared runners are immutable. */
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {checkedCompiler,compileRecord,ROOT,sha,PIN,COMPILER_SHA,VERSION} from './harness.mjs';
import {runFixture,validateFixtureEvidence} from './upstream.mjs';
const options={};for(let i=2;i<process.argv.length;i+=2){if(!['--compiler','--corpus','--out','--filter'].includes(process.argv[i])||!process.argv[i+1])throw Error('expected --compiler FILE --corpus DIR --out DIR [--filter NAME]');options[process.argv[i].slice(2)]=process.argv[i+1];}
for(const key of ['compiler','corpus','out'])if(!options[key])throw Error('missing '+key);
const out=resolve(options.out);mkdirSync(out,{recursive:true});
const snapshot=JSON.parse(readFileSync(join(ROOT,'tests/upstream/snapshot.json'))),inv=JSON.parse(readFileSync(join(options.corpus,'inventory.json')));
if(snapshot.commit!==PIN||inv.commit!==PIN||inv.snapshotSha256!==sha(readFileSync(join(ROOT,'tests/upstream/snapshot.json')))||inv.archiveSha256!=='9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d')throw Error('inventory identity mismatch');
const selected=snapshot.files.filter(f=>f.path.startsWith('test/libsolidity/semanticTests/inlineAssembly/'));
if(JSON.stringify(selected)!==JSON.stringify(inv.files))throw Error('missing or extra corpus entries');
for(const file of selected){const b=readFileSync(join(options.corpus,file.path));if(b.length!==file.bytes||sha(b)!==file.sha256)throw Error('fixture drift: '+file.path);}
const compile=checkedCompiler(options.compiler),results=[];let hits=0;
for(const file of selected){const id=file.path.split('/').at(-1);if(options.filter&&id!==options.filter)continue;hits++;let index=0;
 try{results.push(await runFixture(file.path,options.corpus,input=>compileRecord(compile,input,join(out,id+'.compile-'+index++)).output));}
 catch(e){results.push({path:file.path,status:'blocked',reason:e.message,stack:e.stack});}
 writeFileSync(join(out,'results.partial.json'),JSON.stringify(results,null,2)+'\n');
}
if(!hits)throw Error('filter did not select a pinned fixture');
const variants=results.flatMap(r=>r.variants??[]),counts={};for(const v of variants)counts[v.status]=(counts[v.status]??0)+1;
const validationFailures=[];for(const r of results)try{validateFixtureEvidence(r,options.corpus);}catch(e){validationFailures.push({path:r.path,reason:e.message});}
const report={schema:1,validationFailures,pin:PIN,compiler:VERSION,compilerSha256:COMPILER_SHA,oracleModuleSha256:sha(readFileSync(join(ROOT,'scripts/yul-composition/oracles.mjs'))),upstreamStateOraclesSha256:sha(readFileSync(join(ROOT,'tests/yul-composition/upstream-state-oracles.json'))),captureSha256:sha(readFileSync(join(ROOT,'scripts/yul-composition/capture.mjs'))),adapterSha256:sha(readFileSync(new URL('./upstream.mjs',import.meta.url))),engineSha256:sha(readFileSync(join(ROOT,'scripts/evm-reference/replay.mjs'))),lockSha256:sha(readFileSync(join(ROOT,'scripts/evm-reference/package-lock.json'))),scope:'Pinned legacy/viaIR runtime profiles, default-enabled SSA-CFG profile (SemanticTest.cpp), and explicitly named gas-metadata profiles. Separate from Osaka compilation probes, source admission and Lean correctness.',counts,results};
writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({fixtures:hits,variants:variants.length,counts,fixtureBlocked:results.filter(r=>r.status==='blocked').map(r=>r.path)}));
process.exitCode=validationFailures.length||results.some(r=>r.status==='broken'||r.variants?.some(v=>v.observed?.some(o=>o.comparison?.status==='broken')))?1:0;
