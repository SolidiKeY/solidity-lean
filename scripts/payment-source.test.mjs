import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdtempSync,rmSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {tmpdir} from 'node:os';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {execFileSync} from 'node:child_process';
import {preparePaymentSource,certifyPaymentEvidence} from './payment-source.mjs';
import {parseFixture,withPreamble,runtimePipelines,semanticVectors,evmCompatible,verifySnapshot,COMPILER_SHA} from './solidity-upstream.mjs';
const compiler=resolve(process.env.SOLC_REFERENCE??'/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js');
assert.equal(createHash('sha256').update(readFileSync(compiler)).digest('hex'),COMPILER_SHA);
const c=createRequire(import.meta.url)(compiler).cwrap('solidity_compile','string',['string','number','number']);
const compile=input=>JSON.parse(c(JSON.stringify(input),0,0));
const api={withPreamble,runtimePipelines,semanticVectors,evmCompatible,COMPILER_SHA,VERSION:'0.8.38+commit.1835d247.Emscripten.clang'};
const {directory}=verifySnapshot();
function prepare(name,work){
 const path='test/libsolidity/semanticTests/'+name;
 const raw=readFileSync(join(directory,path));
 return preparePaymentSource(path,parseFixture(raw.toString()),compile,work,{...api,fixtureSha256:createHash('sha256').update(raw).digest('hex')});
}
function execute(cases,work){
 const input=join(work,'cases.json'),out=join(work,'out.json'),wrapper=join(work,'Run.lean');
 writeFileSync(input,JSON.stringify(cases));writeFileSync(out,'[]');
 writeFileSync(wrapper,`import Solidity.Tools.PaymentReplay\n#payment_batch ${JSON.stringify(input)} to ${JSON.stringify(out)}\n`);
 execFileSync('lake',['--quiet','--no-build','lean',wrapper,'--','--tstack=131072'],{timeout:120000,stdio:'pipe'});
 return JSON.parse(readFileSync(out));
}
function scratch(f){const work=mkdtempSync(join(tmpdir(),'payment-source-'));try{return f(work);}finally{rmSync(work,{recursive:true,force:true});}}
test('actual source frames retain debug bytes and reject wrong expected bytes',()=>scratch(work=>{
 const job=prepare('revertStrings/transfer.sol',work).jobs[0];
 const [good]=execute([job],work);assert.equal(good.status,'working',JSON.stringify(good));
 assert.deepEqual(good.observed.map(x=>[x.signature,x.failed,x.values,x.revertBytes.length]),[
 ['()',false,[],0],['g()',false,['10'],0],['f()',true,[],100],['h()',true,[],0]]);
 const wrong=structuredClone(job);wrong.vectors.find(x=>x.signature==='f()').revertBytes=[];
 const [bad]=execute([wrong],work);assert.equal(bad.status,'broken');assert.equal(bad.observed[2].revertBytes.length,100);
}));
test('wrong source receiver identity and unsupported full-gas call shape remain blocked',()=>scratch(work=>{
 const job=prepare('functionCall/send_zero_ether.sol',work).jobs[0];
 for(const mutation of ['receiver','full-gas','internal']){
  const data=JSON.parse(readFileSync(job.fixture));
  const nodes=[];const walk=x=>{if(x&&typeof x==='object'){nodes.push(x);for(const v of Object.values(x))Array.isArray(v)?v.forEach(walk):walk(v);}};walk(data.ast);
  const payment=nodes.find(x=>x.nodeType==='MemberAccess'&&x.memberName==='send');
  if(mutation==='receiver')payment.expression.arguments[0].referencedDeclaration=999999;
  else if(mutation==='internal')nodes.find(x=>x.nodeType==='FunctionDefinition'&&x.name==='s').visibility='internal';
  else payment.typeDescriptions.typeIdentifier='t_function_barecall_payable';
  const file=join(work,mutation+'.ast.json');writeFileSync(file,JSON.stringify(data));
  const [r]=execute([{...job,fixture:file}],work);assert.equal(r.status,'blocked',JSON.stringify(r));
 }
}));
test('repeated creation and calls after failed constructor do not masquerade as Solidity failures',()=>scratch(work=>{
 const job=prepare('functionCall/send_zero_ether.sol',work).jobs[0];
 const repeat=structuredClone(job);repeat.vectors.push(structuredClone(repeat.vectors[1]));
 const [r]=execute([repeat],work);assert.equal(r.status,'blocked');assert.match(r.reason,/fresh-address/);assert.equal(r.observed.length,2);
 const failed=structuredClone(job);failed.vectors[0].value=(10n**30n+1n).toString();failed.vectors[0].failure=true;
 const [f]=execute([failed],work);assert.equal(f.status,'blocked');assert.match(f.reason,/after failed/);assert.equal(f.observed[0].failed,true);
}));
test('source whole-fixture verdict requires exact independent gas correspondence',()=>scratch(work=>{
 const jobs=prepare('functionCall/send_zero_ether.sol',work).jobs;const job=jobs[0];
 const variants=execute(jobs,work);const typed={status:'working',variants,requiredPipelines:job.requiredPipelines};
 assert.ok(variants.every(v=>v.status==='working'));
 const absent=certifyPaymentEvidence(typed,job,null,{});assert.equal(absent.status,'blocked');
 const out=join(work,'original.json');
 execFileSync('node',['scripts/evm-reference/payment-replay.mjs','--compiler',compiler,'--filter',job.path,'--out',out],{timeout:120000});
 const report=JSON.parse(readFileSync(out));
 assert.equal(certifyPaymentEvidence(typed,job,report,{}).status,'working');
 const wrong=structuredClone(job);wrong.originalOrderedObservations.find(x=>x.kind==='independent-bytecode-gas').original='gas irOptimized: 0';
 assert.equal(certifyPaymentEvidence(typed,wrong,report,{}).status,'broken','source route cannot discharge a wrong frozen gas row');
 const provenance=certifyPaymentEvidence(typed,job,report,{compilerSha256:'wrong'});assert.equal(provenance.status,'blocked');
}));

test('zero send executes a refusing receive and retains the preceding creation',()=>scratch(work=>{
 const source='contract R {receive() external payable {revert("refuse");}} contract M {constructor() payable{} function s() public returns(bool){R r=new R(); return payable(r).send(0);}}\n// ----\n// constructor(), 20 wei ->\n// s() -> false\n';
 const fixture=parseFixture(source);
 const jobs=preparePaymentSource('tests/payment-source/refusal.sol',fixture,compile,work,{
 ...api,fixtureSha256:createHash('sha256').update(source).digest('hex')}).jobs;
 const [r]=execute([jobs[0]],work);assert.equal(r.status,'working',JSON.stringify(r));
 assert.deepEqual(r.observed[1].values,['0']);
 assert.equal(r.observed[1].worldAfter.recipientInstalled,true);
 assert.equal(r.observed[1].worldAfter.ownerBalance,'20');
}));

test('saved complete typed rows with pending reference evidence resume to actual verified completion',()=>scratch(work=>{
 const out=join(work,'resume');
 const args=['scripts/solidity-upstream.mjs','run','--compiler',compiler,'--filter','semanticTests/functionCall/send_zero_ether.sol','--out',out];
 execFileSync('node',args,{timeout:120000,stdio:'pipe'});
 const file=join(out,'results.json');const report=JSON.parse(readFileSync(file));const row=report.results[0];
 assert.equal(row.status,'working');assert.equal(row.variants.length,2);
 row.status='blocked';row.pendingPaymentGas=true;row.typedSourceStatus='working';delete row.paymentReferenceEvidence;
 writeFileSync(file,JSON.stringify(report));
 execFileSync('node',[...args,'--resume'],{timeout:120000,stdio:'pipe'});
 const final=JSON.parse(readFileSync(file)).results[0];
 assert.equal(final.status,'working',JSON.stringify(final));assert.equal(final.pendingPaymentGas,false);
 assert.equal(final.paymentReferenceEvidence.result.status,'working');
}));
