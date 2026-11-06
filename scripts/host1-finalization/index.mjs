/** HOST1: actual bounded message execution plus explicit supported finalization.
 * NOT VM.runTx, signed-envelope validation, intrinsic gas/fees, state-root or
 * untouched-world adequacy. Shared engine/files/pins remain read-only. */
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {resolve} from 'node:path';
import {machine,INITIAL_GAS,STEP_LIMIT} from '../evm-reference/replay.mjs';
import {defaultBlock} from '../evm-reference/node_modules/@ethereumjs/evm/dist/esm/evm.js';
import {Account,createAddressFromString,hexToBytes,bytesToHex} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
import {observeFresh,ADDRESS,WORD,BYTES,address,logsOf} from './observe.mjs';
import {validateFinalizedMessage} from './receipt.mjs';
export const ROOT=fileURLToPath(new URL('../../',import.meta.url));
export const CALLER='0x'+'12'.repeat(20);
export const SCOPE='Bounded runCall message plus explicit Osaka EIP6780/EIP161/1153 finalization over API-touched+declared accounts/slots; no runTx/envelope/fee/state-root/untouched-world claim';
const INPUTS='tests/host1-finalization/engine-inputs.json';
const INPUTS_SHA='825155cd6d86506a842dddbcb644c22a910215bd9fdb936e96ec15f33888d559';
export const sha=b=>createHash('sha256').update(b).digest('hex');
export function verifyEngine(read=p=>readFileSync(resolve(ROOT,p))){const bytes=read(INPUTS);if(sha(bytes)!==INPUTS_SHA)throw Error('HOST1 input manifest changed');const inputs=JSON.parse(bytes);for(const [path,hash]of Object.entries(inputs.files))if(sha(read(path))!==hash)throw Error('HOST1 pinned input changed: '+path);return {inputSha256:INPUTS_SHA,base:inputs.base,engine:inputs.engine,hardfork:inputs.hardfork,messageGas:inputs.messageGas,stepLimit:inputs.stepLimit};}
const freeze=x=>{if(x&&typeof x==='object'){for(const v of Object.values(x))freeze(v);Object.freeze(x);}return x;};
const nat=x=>typeof x==='bigint'&&x>=0n&&x<2n**256n;
function request(req){if(!req||Object.getPrototypeOf(req)!==Object.prototype||!['call','create','static'].includes(req.kind)||typeof req.id!=='string'||!req.id||!BYTES.test(req.data)||req.value!==undefined&&!nat(req.value)||Object.keys(req).some(k=>!['id','kind','to','data','value'].includes(k)))throw Error('malformed HOST1 request');if(req.kind==='create'?req.to!==undefined:!ADDRESS.test(req.to))throw Error('wrong HOST1 request target');if(req.kind==='static'&&(req.value??0n)!==0n)throw Error('static value refused');return {...req,value:req.value??0n};}
export class Host1Blocked extends Error { constructor(message){super(message);this.name='Host1Blocked';} }
/** Owns a FRESH exported machine. No assumed call result or caller-supplied
 * created/selfdestruct sets are accepted. execute() cannot finalize twice. */
export async function createFinalizationSession(options={}){
 if(!options||Object.getPrototypeOf(options)!==Object.prototype||Object.keys(options).some(k=>!['seeds','watch'].includes(k)))throw Error('unknown HOST1 configuration');
 const {seeds=[],watch=[]}=options;if(!Array.isArray(seeds)||!Array.isArray(watch))throw Error('invalid HOST1 configuration');
 const engine=verifyEngine();if(INITIAL_GAS!==100000000n||STEP_LIMIT!==5000000)throw Error('reference budget changed');
 const vm=await machine(),evm=vm.evm,sm=evm.stateManager;
 if(evm.common.hardfork()!=='osaka'||!evm.common.isActivatedEIP(6780)||!evm.common.isActivatedEIP(1153)||evm.common.isActivatedEIP(8246))throw Error('HOST1 unsupported protocol profile');
 const obs=observeFresh(vm);await obs.watch(CALLER);
 const seeded=new Set();for(const s of seeds){if(!s||!ADDRESS.test(s.address)||s.address===CALLER||seeded.has(s.address)||!nat(s.balance)||!nat(s.nonce)||!BYTES.test(s.code)||!s.storage||Object.getPrototypeOf(s.storage)!==Object.prototype||Object.entries(s.storage).some(([k,v])=>!WORD.test(k)||!WORD.test(v)))throw Error('invalid HOST1 setup seed');seeded.add(s.address);const a=createAddressFromString(s.address);await sm.putAccount(a,new Account(s.nonce,s.balance));await sm.putCode(a,hexToBytes(s.code));for(const [k,v]of Object.entries(s.storage))await sm.putStorage(a,hexToBytes(k),hexToBytes(v));}
 for(const w of watch){if(!w||!ADDRESS.test(w.address)||!Array.isArray(w.persistent)||!Array.isArray(w.transient)||[...w.persistent,...w.transient].some(k=>!WORD.test(k)))throw Error('invalid HOST1 watch domain');await obs.watch(w.address,w);}
 let busy=false,poisoned=false,ordinal=0;const ids=new Set();let actions=null,deleteReason=null;
 const deleteAccount=evm.journal.deleteAccount.bind(evm.journal);
 // SimpleStateManager deletion removes metadata only. Normalize through public
 // APIs in the EXPLICIT FINALIZATION phase; never alter message opcode behavior.
 evm.journal.deleteAccount=async a=>{if(actions){actions.push({ordinal:actions.length,kind:'delete',reason:deleteReason,address:address(a)});await sm.clearStorage(a);await sm.putCode(a,new Uint8Array());}await deleteAccount(a);};
 return Object.freeze({engine:freeze(engine),caller:CALLER,
  async snapshot(){if(busy||poisoned)throw new Host1Blocked('snapshot of unavailable session');return freeze(await obs.snapshot());},
  async execute(rawRequest){const req=request(rawRequest);if(busy||poisoned||ids.has(req.id))throw new Host1Blocked('overlapping, poisoned or reused HOST1 request');busy=true;ids.add(req.id);const seq=ordinal++;
   try{
    await obs.watch(CALLER);if(req.to)await obs.watch(req.to);
    const tx=await obs.begin();await sm.checkpoint();
    const block=defaultBlock(),{result,metrics}=await vm.call({...(req.to?{to:createAddressFromString(req.to)}:{}),data:hexToBytes(req.data),value:req.value,isStatic:req.kind==='static',block,gasPrice:0n});
    obs.assertCaptured();
    if(obs.depth!==1||!tx.frames.length||tx.trace.at(-1)?.kind!=='exit')throw Error('incomplete message execution');
    const exec=result.execResult;if(exec.exceptionError?.error==='internal error')throw Error('unadapted engine internal error');
    // Missing substate is UNSUPPORTED, never silently inferred empty.
    if(!(exec.selfdestruct instanceof Map)||!(exec.createdAddresses instanceof Set))throw Error('missing committed root Map/Set finalization evidence');
    const destruct=[...exec.selfdestruct].map(([a,b])=>({address:address(a),beneficiary:address(b)}));
    const created=[...exec.createdAddresses].map(address);if(new Set(created).size!==created.length)throw Error('duplicate created address');
    if(exec.exceptionError&&(destruct.length||created.length))throw Error('failed root retained uncommitted substate');
    const eligible=destruct.filter(x=>created.includes(x.address)),retained=destruct.filter(x=>!created.includes(x.address));
    const messagePost=await obs.snapshot();const transientBefore=JSON.parse(JSON.stringify(evm.transientStorage.toJSON()));
    const root=tx.frames[0];if(!(exec.returnValue instanceof Uint8Array)||root.output.bytes!==bytesToHex(exec.returnValue)||root.output.exception!==(exec.exceptionError?.error??null)||metrics.steps!==tx.frames.reduce((n,f)=>n+f.steps,0))throw Error('root/result identity mismatch');
    actions=[];deleteReason='selfdestruct';obs.phase('finalization');
    for(const d of eligible)await evm.journal.deleteAccount(createAddressFromString(d.address));
    actions.push({ordinal:actions.length,kind:'journal-cleanup'});deleteReason='eip161';await evm.journal.cleanup();
    actions.push({ordinal:actions.length,kind:'transient-clear'});evm.transientStorage.clear();
    actions.push({ordinal:actions.length,kind:'state-commit'});await sm.commit();
    const post=await obs.snapshot(),domain=obs.domain();const savedActions=actions;actions=null;deleteReason=null;
    const captured=obs.finish();
    for(const a of eligible.map(x=>x.address)){const v=post[a];if(!v||v.exists||v.code!=='0x'||Object.values(v.persistent).some(x=>BigInt(x)!==0n))throw Error('incomplete eligible account deletion');}
    if(Object.keys(evm.transientStorage.toJSON()).length)throw Error('transient state survived finalization');
    const deleted=Object.keys(post).filter(a=>messagePost[a]?.exists&&!post[a].exists).sort();
    const normalizedRequest={id:req.id,kind:req.kind,to:req.to??null,data:req.data,value:req.value.toString(),caller:CALLER,origin:CALLER};
    const receipt={schema:1,scope:SCOPE,ordinal:seq,request:normalizedRequest,requestSha256:sha(JSON.stringify(normalizedRequest)),engine,
     environment:{hardfork:evm.common.hardfork(),chainId:evm.common.chainId().toString(),messageGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,caller:CALLER,origin:CALLER,gasPrice:'0',block:{number:block.header.number.toString(),coinbase:address(block.header.coinbase),timestamp:block.header.timestamp.toString(),difficulty:block.header.difficulty.toString(),prevRandao:bytesToHex(block.header.prevRandao),gasLimit:block.header.gasLimit.toString(),baseFeePerGas:block.header.baseFeePerGas?.toString()??null,slotNumber:block.header.slotNumber?.toString()??null,blobGasPrice:block.header.getBlobGasPrice()?.toString()??null},unlimitedCodeAndInitcodeSize:true,transactionEnvelope:false,feeAccounting:false},
     domain,pre:captured.pre,messagePost,post,frames:captured.frames,trace:captured.trace,operations:captured.operations,
     message:{...root.output,createdAddress:result.createdAddress?address(result.createdAddress):null,selfdestruct:destruct,createdAddresses:created,executionGasUsed:exec.executionGasUsed.toString(),gasRefund:exec.gasRefund?.toString()??null,metrics:{steps:metrics.steps,maxStack:metrics.maxStack}},
     finalization:{kind:'explicit-osaka-message-finalization',eligible,retained,deletedAccounts:deleted,transientBefore,transientAfter:evm.transientStorage.toJSON(),actions:savedActions,originalStorageCache:'cleared by shared factory at next message boundary'}};
    validateFinalizedMessage(receipt,req,seq);return freeze(receipt);
   }catch(e){actions=null;deleteReason=null;poisoned=true;try{await obs.abort();evm.transientStorage.clear();evm.journal.cleanJournal();}catch{}throw new Host1Blocked('HOST1 did not produce a finalized receipt: '+e.message);
   }finally{busy=false;}
  }
 });
}

export function parseAddress(s){return address(s);}
export function parseWord(s){if(typeof s!=='string'||!WORD.test(s))throw Error('invalid word hex');return s;}
export function parseBytes(s){if(typeof s!=='string'||!BYTES.test(s))throw Error('invalid bytes hex');return s;}
export {validateFinalizedMessage} from './receipt.mjs';

/** Missing unobserved state is an error, never an assumed empty account/slot. */
export function readObservedAccount(r,phase,a){if(!['pre','messagePost','post'].includes(phase)||!ADDRESS.test(a)||!r.domain.some(d=>d.address===a)||!Object.hasOwn(r[phase],a))throw Error('unobserved account/phase');return r[phase][a];}
export function readObservedSlot(r,phase,a,bank,key){const account=readObservedAccount(r,phase,a),domain=r.domain.find(d=>d.address===a);if(!['persistent','transient'].includes(bank)||!WORD.test(key)||!domain[bank].includes(key)||!Object.hasOwn(account[bank],key))throw Error('unobserved slot');return parseWord(account[bank][key]);}
