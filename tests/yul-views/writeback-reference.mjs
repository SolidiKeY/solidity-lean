// Closed owned canonical/source-frame observations, not a general composition harness.
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {replayBytecode} from '../../scripts/evm-reference/replay.mjs';
const sha=b=>createHash('sha256').update(b).digest('hex');
const number=hex=>BigInt(hex).toString();
const prefix='0x'+'a5'.repeat(30);
export function checkWritebackReplay(replay){
 if(replay.status!=='working')return replay;
 const failed=replay.observed[5];
 if(replay.observed.length!==9||failed?.signature!=='outerRevertAfterChild()'||
    failed.failed!==true||failed.exception!=='revert'||failed.returnData!=='0x')
  return {...replay,status:'broken',reason:'explicit outer revert observation mismatch (resource failure is not this fixture outcome)'};
 return replay;
}
export async function replayWriteback(compile){
 const source=readFileSync(new URL('./Writeback.sol',import.meta.url),'utf8');
 const vectors=[
  {signature:'unchangedDefault()',args:[],failure:false,expected:[number(prefix+'0000'),'0']},
  {signature:'changedAndDisjoint()',args:[],failure:false,expected:[number(prefix+'0101'),'1','1']},
  {signature:'repeated()',args:[],failure:false,expected:[number(prefix+'0001'),'1','0']},
  {signature:'rawNoncanonical()',args:[],failure:false,expected:[number(prefix+'0002'),'1']},
  {signature:'innerRevertPrefix()',args:[],failure:false,expected:[number(prefix+'0001'),'0']},
  {signature:'outerRevertAfterChild()',args:[],failure:true,expected:[]},
  {signature:'readStored()',args:[],failure:false,expected:[number(prefix+'0001'),'0']},
  {signature:'successAndTransient()',args:[],failure:false,expected:[number(prefix+'0101'),'1']},
  {signature:'readStored()',args:[],failure:false,expected:[number(prefix+'0101'),'0']},
 ];
 const variants=[];
 for(const viaIR of [false,true]){
  const input={language:'Solidity',sources:{'Writeback.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',
   optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'*':
    ['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers','storageLayout','transientStorageLayout']}}}};
  const out=compile(input),errors=(out.errors??[]).filter(e=>e.severity==='error');
  if(errors.length){variants.push({viaIR,status:'blocked',errors});continue;}
  const artifact=out.contracts['Writeback.sol'].Writeback;
  const layout=artifact.storageLayout.storage,transient=artifact.transientStorageLayout.storage;
  if(!layout.some(x=>x.label==='first'&&x.slot==='7'&&x.offset===0)||
     !layout.some(x=>x.label==='second'&&x.slot==='7'&&x.offset===1)||
     !transient.some(x=>x.label==='txFlag'&&x.slot==='0'&&x.offset===0))
   throw Error('writeback fixture layout drift');
  variants.push({viaIR,inputSha256:sha(JSON.stringify(input)),sourceSha256:sha(source),storageLayout:artifact.storageLayout,
   transientStorageLayout:artifact.transientStorageLayout,vectors,...checkWritebackReplay(await replayBytecode(artifact,vectors))});
 }
 return {kind:'external-reference-only',sourceSha256:sha(source),
  boundary:'Source none versus explicit-default identity is kernel-only. Raw noncanonical bool2 remains observable; unsupported canonical preparation is not source/EVM semantics.',
  variants,status:variants.every(v=>v.status==='working')?'working':variants.some(v=>v.status==='broken')?'broken':'blocked'};
}
