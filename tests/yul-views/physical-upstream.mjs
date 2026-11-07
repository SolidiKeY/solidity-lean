// Exact-fixture raw replay adapter. No general host classifier or shared harness changes.
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {join} from 'node:path';
import {verifySnapshot,parseFixture,semanticVectors,withPreamble,PIN,evmCompatible} from '../../scripts/solidity-upstream.mjs';
import {machine,observation,creationObservation,HostLimit,INITIAL_GAS,STEP_LIMIT} from '../../scripts/evm-reference/replay.mjs';
const sha=b=>createHash('sha256').update(b).digest('hex');
const hex=bs=>'0x'+Buffer.from(bs).toString('hex');
const bytes=h=>Uint8Array.from(Buffer.from(h.slice(2),'hex'));
const word=n=>BigInt.asUintN(256,BigInt(n)).toString(16).padStart(64,'0');
export const FIXTURES=[
 ['calldata_length_read',6,'6f6d8edf0cdad127ef9f7170e6955d0679597bf795c4fac56d0bbd0f254fbb12'],
 ['mcopy_overlap',5,'a2a8dd19fe362e75375986e0b2744047b48cd4a5b016f25a551085a707bfdf97'],
 ['keccak256_assembly',1,'4ccbc461df2811def7772195f1668e2c98eb5345f93e95c8618e7cca572e7ee2'],
 ['inline_assembly_memory_access',1,'99060126b0b6186cbe2937222b52387f21e2fce62454b7616ce8db5ea4c4fc46'],
];
export class ExpectationMismatch extends Error {}
const requireMatch=(ok,message)=>{if(!ok)throw new ExpectationMismatch(message);};

/** Normalize both public semanticVectors shapes; do not ABI-canonicalize raw bytes. */
export function rawPlan(vectors,artifact,lines) {
  requireMatch(vectors.length===lines.length,'dropped source expectation');
  return vectors.map((v,ordinal)=>{
    if(v.signature==='constructor')throw new HostLimit('explicit constructor outside these exact fixture inventories');
    const selector=artifact.evm.methodIdentifiers[v.signature];
    if(!/^[0-9a-f]{8}$/.test(selector??''))throw new HostLimit('missing selector');
    let calldata,expected;
    if(Array.isArray(v.calldata)&&Array.isArray(v.expectedBytes)){
      calldata=hex(v.calldata);expected=hex(v.expectedBytes);
    }else if(Array.isArray(v.args)&&Array.isArray(v.expected)){
      calldata='0x'+v.args.map(word).join('');
      expected=v.failure?hex(v.revertBytes??[]):'0x'+v.expected.map(word).join('');
    }else throw new HostLimit('unrecognized public vector shape');
    return {ordinal,sourceLine:lines[ordinal],signature:v.signature,
      calldata:'0x'+selector+calldata.slice(2),failed:v.failure,returnData:expected};
  });
}

/** Every byte, ordinal, source expectation and storage-write observation participates. */
export function assertTranscript(plan,observed) {
  requireMatch(plan.length===observed.length,'dropped or extra vector');
  for(let i=0;i<plan.length;i++){
    const p=plan[i],o=observed[i];
    requireMatch(p.ordinal===i&&o.ordinal===i,'reordered ordinal');
    for(const key of ['sourceLine','signature','calldata','failed','returnData'])
      requireMatch(p[key]===o[key],`vector ${i} ${key} mismatch`);
    requireMatch(o.storageWritesBefore===0&&o.storageWritesAfter===0,`vector ${i} unexpected storage writes`);
  }
}

/** Observe public write API calls, not unsupported SimpleStateManager roots.
 * The four exact fixtures start on a fresh machine and perform no storage writes.
 * Record even attempted writes; this deliberately stronger invariant is explicit. */
export function observeStorageWrites(vm) {
  const writes=[],manager=vm.evm.stateManager,put=manager.putStorage.bind(manager);
  manager.putStorage=async(address,key,value)=>{
    writes.push({address:address.toString(),key:hex(key),value:hex(value)});
    return put(address,key,value);
  };
  return writes;
}

export function assertFixtureRun(run) {
  requireMatch(run.status==='working','nonworking fixture');
  requireMatch(run.deployment?.failed===false,'missing or failed deployment');
  requireMatch(run.deployment.runtimeCodeSha256===run.runtimeSha256,'wrong deployed code');
  requireMatch(run.deployment.storageWriteCount===0&&run.storageWrites.length===0,'unexpected deployment/storage writes');
  assertTranscript(run.plan,run.observed);
}

/** These exact contracts have no storage variables or world effects. `new bytes`
 * in memory_access is a local allocation. Never bypass the general host gate for
 * other sources. Retain machine's resets, limits, logs and exception admission. */
async function replayRaw(artifact,plan) {
  const observed=[];let deployment;let storageWrites=[];
  try{
    const vm=await machine();
    storageWrites=observeStorageWrites(vm);
    const created=await vm.call({data:bytes('0x'+artifact.evm.bytecode.object)});
    deployment=creationObservation(created.result.execResult,'constructor',created.metrics);
    requireMatch(!deployment.failed,'implicit deployment failed');
    if(!created.result.createdAddress)throw new HostLimit('successful creation has no address');
    requireMatch(deployment.runtimeCodeSha256===sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex')),'deployment runtime mismatch');
    const address=created.result.createdAddress;
    deployment.storageWriteCount=storageWrites.length;
    requireMatch(storageWrites.length===0,'unexpected constructor storage writes');
    for(const p of plan){
      const storageWritesBefore=storageWrites.length;
      const {result,metrics}=await vm.call({to:address,data:bytes(p.calldata)});
      const actual=observation(result.execResult,p.signature,metrics);
      observed.push({...p,...actual,storageWritesBefore,storageWritesAfter:storageWrites.length});
      // A mismatch stops fail-closed; unexecuted observations remain explicit in plan.
      assertTranscript(plan.slice(0,observed.length),observed);
    }
    assertTranscript(plan,observed);
    return {status:'working',deployment,plan,observed,storageWrites};
  }catch(e){return {status:e instanceof ExpectationMismatch?'broken':'blocked',reason:e.message,deployment,plan,observed,storageWrites};}
}

export async function replayPhysicalFixtures(compile) {
  const {manifest,directory}=verifySnapshot();
  const results=[];
  for(const [name,count,pinnedHash] of FIXTURES){
    const path=`test/libsolidity/semanticTests/inlineAssembly/${name}.sol`;
    const text=readFileSync(join(directory,path),'utf8');
    requireMatch(sha(text)===pinnedHash,'exact fixture hash mismatch');
    const fixture=parseFixture(text),lines=fixture.expectations.filter(x=>x.trim());
    requireMatch(lines.length===count,'changed fixture observation inventory');
    requireMatch(evmCompatible(fixture.settings.EVMVersion,'osaka'),'fixture fork mismatch');
    // No unsupported setting or non-call observation is silently discarded.
    requireMatch(Object.keys(fixture.settings).every(k=>k==='EVMVersion'),'unhandled fixture setting');
    const variants=[];
    for(const viaIR of [false,true]){
      const input={language:'Solidity',sources:Object.fromEntries([...fixture.sources].map(([k,s])=>[k,{content:withPreamble(s)}])),
        settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},
          outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers']}}}};
      const out=compile(input),errors=(out.errors??[]).filter(e=>e.severity==='error');
      if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
      const contracts=Object.values(out.contracts[fixture.mainSource]).filter(a=>a.evm.bytecode.object);
      requireMatch(contracts.length===1,'unexpected deployment contract inventory');
      const artifact=contracts[0],vectors=semanticVectors(fixture,artifact.abi);
      const plan=rawPlan(vectors,artifact,lines);
      const record={viaIR,inputSha256:sha(JSON.stringify(input)),creationSha256:sha(Buffer.from(artifact.evm.bytecode.object,'hex')),
        runtimeSha256:sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex')),vectors,...await replayRaw(artifact,plan)};
      if(record.status==='working')assertFixtureRun(record);
      variants.push(record);
    }
    results.push({path,sourceSha256:pinnedHash,expectations:lines,variants});
  }
  const report={kind:'external-reference-only',commit:PIN,archiveSha256:manifest.archiveSha256,
    adapterSha256:sha(readFileSync(new URL('./physical-upstream.mjs',import.meta.url))),
    helperSha256:sha(readFileSync(new URL('../../scripts/evm-reference/replay.mjs',import.meta.url))),
    observationInventory:{fixtures:4,callsPerPipeline:13,deploymentsPerPipeline:4,
      explicitConstructors:0,failureExpectations:0,storageExpectations:0,logExpectations:0,worldHostRequirements:0},
    addedInvariant:'fresh machine; no public putStorage calls during deployment or any call; attempted writes also refused',
    initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,results};
  report.status=results.some(f=>f.variants.some(v=>v.status==='broken'))?'broken':
    results.every(f=>f.variants.length===2&&f.variants.every(v=>v.status==='working'))?'working':'blocked';
  if(report.status==='working')assertPhysicalReport(report);
  return report;
}

export function assertPhysicalReport(report) {
  requireMatch(report.commit===PIN,'wrong upstream commit');
  requireMatch(report.results.length===FIXTURES.length,'dropped fixture');
  for(let i=0;i<FIXTURES.length;i++){
    const [name,count,hash]=FIXTURES[i],f=report.results[i];
    requireMatch(f.path===`test/libsolidity/semanticTests/inlineAssembly/${name}.sol`&&f.sourceSha256===hash,'reordered/drifting fixture');
    requireMatch(f.variants.length===2,'dropped pipeline');
    for(let j=0;j<2;j++){
      const v=f.variants[j];
      requireMatch(v.viaIR===Boolean(j)&&v.plan.length===count,'reordered pipeline or dropped call');
      assertFixtureRun(v);
    }
  }
}
