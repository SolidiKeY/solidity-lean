// Fail-closed controls for the exact-fixture adapter. Uses the unchanged public machine.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertTranscript,assertFixtureRun,assertPhysicalReport,rawPlan,ExpectationMismatch,observeStorageWrites} from './physical-upstream.mjs';
import {machine,creationObservation,observation} from '../../scripts/evm-reference/replay.mjs';
const file=process.argv[2];if(!file)throw Error('expected saved physical-reference report');
const report=JSON.parse(readFileSync(file,'utf8')).upstream;
const clone=x=>JSON.parse(JSON.stringify(x));
const rejects=fn=>assert.throws(fn,ExpectationMismatch);
const flip=h=>h.slice(0,-2)+(h.endsWith('00')?'01':'00');
let negatives=0;
assertPhysicalReport(report);
for(const f of report.results)for(const v of f.variants){
  assertFixtureRun(v);
  let x=clone(v);x.observed.pop();rejects(()=>assertFixtureRun(x));negatives++;
  x=clone(v);x.observed[0].returnData=flip(x.observed[0].returnData);rejects(()=>assertFixtureRun(x));negatives++;
  x=clone(v);x.observed[0].calldata=flip(x.observed[0].calldata);rejects(()=>assertFixtureRun(x));negatives++;
  x=clone(v);x.observed[0].failed=!x.observed[0].failed;rejects(()=>assertFixtureRun(x));negatives++;
  x=clone(v);x.observed[0].storageWritesAfter=1;rejects(()=>assertFixtureRun(x));negatives++;
  x=clone(v);delete x.deployment;rejects(()=>assertFixtureRun(x));negatives++;
  x=clone(v);x.deployment.failed=true;rejects(()=>assertFixtureRun(x));negatives++;
  x=clone(v);x.deployment.runtimeCodeSha256='wrong';rejects(()=>assertFixtureRun(x));negatives++;
  const artifact={evm:{methodIdentifiers:Object.fromEntries(v.plan.map(p=>[p.signature,p.calldata.slice(2,10)]))}};
  rejects(()=>rawPlan(v.vectors.slice(1),artifact,f.expectations));negatives++;
  if(v.observed.length>1){
    x=clone(v);[x.observed[0],x.observed[1]]=[x.observed[1],x.observed[0]];
    rejects(()=>assertFixtureRun(x));negatives++;
  }
}
let x=clone(report);x.results.pop();rejects(()=>assertPhysicalReport(x));negatives++;
x=clone(report);x.results[0].variants.pop();rejects(()=>assertPhysicalReport(x));negatives++;
x=clone(report);x.results[0].variants.reverse();rejects(()=>assertPhysicalReport(x));negatives++;
x=clone(report);x.results.reverse();rejects(()=>assertPhysicalReport(x));negatives++;

// Exercise the actual SSTORE -> public putStorage observer, not a fabricated root.
const vm=await machine(),writes=observeStorageWrites(vm);
const fromHex=h=>Uint8Array.from(Buffer.from(h,'hex'));
const created=await vm.call({data:fromHex('6006600c60003960066000f3600160005500')});
const deployment=creationObservation(created.result.execResult,'constructor',created.metrics);
assert.equal(deployment.failed,false);assert.equal(writes.length,0);
const address=created.result.createdAddress;assert.ok(address);
const run=await vm.call({to:address,data:new Uint8Array()});
const actual=observation(run.result.execResult,'mutating()',run.metrics);
assert.equal(actual.failed,false);assert.equal(writes.length,1);
const stored=await vm.evm.stateManager.getStorage(address,new Uint8Array(32));
assert.equal(BigInt('0x'+Buffer.from(stored).toString('hex')),1n);
const plan=[{ordinal:0,sourceLine:'mutation control',signature:'mutating()',calldata:'0x',failed:false,returnData:'0x'}];
rejects(()=>assertTranscript(plan,[{...plan[0],...actual,storageWritesBefore:0,storageWritesAfter:writes.length}]));negatives++;
console.log(JSON.stringify({positiveFixtureVariants:8,negativeControls:negatives,actualSstore:{writes,storedHex:'0x'+Buffer.from(stored).toString('hex'),metrics:run.metrics},status:'pass'}));
