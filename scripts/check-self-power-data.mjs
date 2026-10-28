#!/usr/bin/env node
/** Pinned solc/EVM evidence, separate from Lean proofs. Dependencies are external.
 * node scripts/check-self-power-data.mjs SOLJSON NODE_MODULES [OUTPUT_JSON]
 */
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
import {execFileSync} from 'node:child_process';
import {parseFixture, semanticVectors, withPreamble} from './solidity-upstream.mjs';
const [compiler,modules,output] = process.argv.slice(2);
assert.ok(compiler && modules, 'expected compiler and external node_modules');
const sha = b => createHash('sha256').update(b).digest('hex');
const compilerSha256 = sha(readFileSync(compiler));
assert.equal(compilerSha256,'6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390');
const require = createRequire(resolve(modules,'reference.cjs'));
const {createVM} = require('@ethereumjs/vm');
const {Common,Mainnet,Hardfork} = require('@ethereumjs/common');
const {createAddressFromString,hexToBytes,bytesToHex} = require('@ethereumjs/util');
const {Interface} = require('ethers');
const solc = createRequire(import.meta.url)(resolve(compiler));
const compile = solc.cwrap('solidity_compile','string',['string','number','number']);
const version = solc.cwrap('solidity_version','string',[])();
assert.equal(version,'0.8.38+commit.1835d247.Emscripten.clang');
const observations=[];
const panic = n => '0x4e487b71'+BigInt(n).toString(16).padStart(64,'0');
const sourcePath='tests/solc/SelfPowerData.sol';
const own=readFileSync(sourcePath,'utf8');
const upstreamPaths=['test/libsolidity/semanticTests/tryCatch/panic.sol',
 'test/libsolidity/semanticTests/revertStrings/empty_v2.sol'];
const inputs=[{path:sourcePath,text:own,own:true},...upstreamPaths.map(path=>({path,
 text:execFileSync('tar',['-xOzf','tests/upstream/solidity-0.8.38.tar.gz',path],{encoding:'utf8'})}))];
for (const input of inputs) for (const viaIR of [false,true]) {
 const fixture=input.own?undefined:parseFixture(input.text);
 const sources=input.own?{'SelfPowerData.sol':{content:input.text}}:
  Object.fromEntries([...fixture.sources].map(([k,v])=>[k,{content:withPreamble(v)}]));
 const settings={viaIR,evmVersion:'cancun',optimizer:{enabled:true,runs:200},
  ...(fixture?.settings.revertStrings?{debug:{revertStrings:fixture.settings.revertStrings}}:{}),
  outputSelection:{'*':{'*':['abi','evm.deployedBytecode.object']}}};
 const out=JSON.parse(compile(JSON.stringify({language:'Solidity',sources,settings}),0,0));
 assert.deepEqual((out.errors??[]).filter(e=>e.severity==='error'),[]);
 const c=Object.values(Object.values(out.contracts)[0])[0];
 const iface=new Interface(c.abi);
 const code=hexToBytes('0x'+c.evm.deployedBytecode.object);
 const to=createAddressFromString('0x0000000000000000000000000000000000001000');
 const caller=createAddressFromString('0x0000000000000000000000000000000000002000');
 async function check(signature,args,expected,failure=false,calldata) {
  const data=calldata??iface.encodeFunctionData(signature,args);
  const vm=await createVM({common:new Common({chain:Mainnet,hardfork:Hardfork.Cancun})});
  await vm.stateManager.putCode(to,code);
  const {execResult:r}=await vm.evm.runCall({to,caller,data:hexToBytes(data),gasLimit:30000000n});
  const actual=bytesToHex(r.returnValue).toLowerCase();
  assert.equal(!!r.exceptionError,failure,`${input.path} ${signature} ${viaIR}`);
  assert.equal(actual,expected.toLowerCase(),`${input.path} ${signature} ${viaIR}`);
  observations.push({path:input.path,sourceSha256:sha(input.text),pipeline:viaIR?'viaIR':'legacy',
   settings,signature,args:args.map(String),calldata:data,failure,expected,actual});
 }
 if(input.own) {
  for(const f of ['cutoff','multiply','declaration','nestedCode','internalCode','narrowCode','fit','shortcuts','uncheckedCode','rawData','shortcutFailures','andCode','orCode','ternaryCode','indexCode'])
   await check(f,[],'0x');
  await check('priority',[viaIR?1:18],'0x');
  await check('nestedPriorityCode',[viaIR?18:17],'0x');
  await check('nestedPriorityCode',[viaIR?17:18],panic(1),true);
  await check('priority',[viaIR?18:1],panic(1),true);
  for(const f of ['wrongCode','wrongRaw']) await check(f,[],panic(1),true);
  await check('indexPower',[2,256],panic(17),true);
  await check('indexBase',[2,256],panic(50),true);
  for(const args of [[2n,256n],[2n**255n,2n]]) await check('power',args,panic(17),true);
  for(const [a,b,r] of [[2n,255n,2n**255n],[0n,0n,1n],[0n,2n**256n-1n,0n],[1n,2n**256n-1n,1n]])
   await check('power',[a,b],iface.encodeFunctionResult('power',[r]));
 } else {
  for(const v of semanticVectors(fixture,c.abi)) {
   const hex=bs=>'0x'+Buffer.from(bs).toString('hex');
   const data=v.calldata===undefined?undefined:iface.getFunction(v.signature).selector+hex(v.calldata).slice(2);
   const expected=v.expectedBytes!==undefined?hex(v.expectedBytes):
    v.failure?hex(v.revertBytes??[]):iface.encodeFunctionResult(v.signature,v.expected);
   await check(v.signature,v.args??[],expected,v.failure,data);
  }
 }
}
const result={version:1,compiler:version,compilerSha256,archiveSha256:sha(readFileSync('tests/upstream/solidity-0.8.38.tar.gz')),
 scope:'Compiler/EVM evidence only; original upstream expectations preserved, including debug revertStrings. No Lean agreement claimed for settings refused by the importer.',observations};
if(output) writeFileSync(output,JSON.stringify(result,null,2)+'\n');
console.log(`${observations.length} exact-byte compiler/EVM observations passed in legacy and viaIR`);
