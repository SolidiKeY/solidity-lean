/** Public-API observation only. No execution or finalization policy lives here. */
import {createHash} from 'node:crypto';
import {createAddressFromString,hexToBytes,bytesToHex} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
const hex=bytesToHex,sha=b=>createHash('sha256').update(b).digest('hex');
export const ADDRESS=/^0x[0-9a-f]{40}$/, WORD=/^0x[0-9a-f]{64}$/, BYTES=/^0x(?:[0-9a-f]{2})*$/;
export const ZERO='0x'+'00'.repeat(32);
export function address(a){const s=typeof a==='string'?a:a.toString();if(!ADDRESS.test(s))throw Error('noncanonical address');return s;}
export function word(b){if(!(b instanceof Uint8Array)||b.length>32)throw Error('invalid slot bytes');return '0x'+hex(b).slice(2).padStart(64,'0');}
export function logsOf(exec,steps){
 if(!Array.isArray(exec.logs)){if(exec.logs!==undefined||steps)throw Error('missing executed-frame logs');return {status:'not-provided',logs:null};}
 return {status:'captured',logs:exec.logs.map(l=>{if(!Array.isArray(l)||l.length!==3||!(l[0] instanceof Uint8Array)||l[0].length!==20||!Array.isArray(l[1])||l[1].length>4||!l[1].every(x=>x instanceof Uint8Array&&x.length===32)||!(l[2] instanceof Uint8Array))throw Error('malformed actual EVM log');return {emitter:hex(l[0]),topics:l[1].map(hex),data:hex(l[2])};})};
}
/** Only called immediately after the exported fresh factory, before setup. */
export function observeFresh(vm){
 const sm=vm.evm.stateManager,ts=vm.evm.transientStorage,known=new Map();
 const methods=['getAccount','putAccount','deleteAccount','modifyAccountFields','getCode','putCode','getCodeSize','getStorage','putStorage','clearStorage','checkpoint','commit','revert'];
 const raw=Object.fromEntries(methods.map(k=>{if(typeof sm[k]!=='function')throw Error('missing public state API '+k);return[k,sm[k].bind(sm)];}));
 const transient=Object.fromEntries(['get','put','clear','checkpoint','commit','revert','toJSON'].map(k=>{if(typeof ts[k]!=='function')throw Error('missing transient API '+k);return[k,ts[k].bind(ts)];}));
 let tx=null,stack=[],depth=0;const errors=[],messages=new WeakMap();
 const event=(name,fn)=>vm.evm.events.on(name,(data,done)=>{Promise.resolve().then(()=>fn(data)).catch(e=>errors.push(name+': '+e.message)).finally(done);});
 async function acct(a){const obj=createAddressFromString(a),v=await raw.getAccount(obj),code=await raw.getCode(obj);if(!(code instanceof Uint8Array))throw Error('missing code');return {exists:v!==undefined,nonce:v===undefined?null:v.nonce.toString(),balance:v===undefined?null:v.balance.toString(),code:hex(code),codeSha256:sha(code),codeHash:v===undefined?null:hex(v.codeHash),persistent:{},transient:{}};}
 const scopes=()=>tx?[tx,...stack]:[];
 async function touch(a,bank,key){a=address(a);if(!known.has(a))known.set(a,{persistent:new Set(),transient:new Set()});
  for(const s of scopes())if(!Object.hasOwn(s.pre,a))s.pre[a]=await acct(a);
  if(bank){if(!WORD.test(key))throw Error('noncanonical slot');known.get(a)[bank].add(key);const obj=createAddressFromString(a),slot=hexToBytes(key);const v=word(bank==='persistent'?await raw.getStorage(obj,slot):transient.get(obj,slot));for(const s of scopes())if(!Object.hasOwn(s.pre[a][bank],key))s.pre[a][bank][key]=v;}
 }
 async function snapshot(){const result={};for(const a of [...known.keys()].sort()){const v=await acct(a),obj=createAddressFromString(a);for(const bank of ['persistent','transient'])for(const k of [...known.get(a)[bank]].sort())v[bank][k]=word(bank==='persistent'?await raw.getStorage(obj,hexToBytes(k)):transient.get(obj,hexToBytes(k)));result[a]=v;}return result;}
 function op(kind,a=null,slot=null,value=null){if(tx)tx.operations.push({ordinal:tx.operations.length,phase:tx.phase,frame:stack.at(-1)?.id??null,kind,address:a,slot,value});}
 for(const k of methods){sm[k]=async(...args)=>{
  const a=args[0]&&k!=='checkpoint'&&k!=='commit'&&k!=='revert'?address(args[0]):null;
  if(a)await touch(a,['getStorage','putStorage'].includes(k)?'persistent':undefined,['getStorage','putStorage'].includes(k)?word(args[1]):undefined);
  let value=null;if(k==='putStorage'||k==='putCode')value=hex(args.at(-1));
  if(k==='putAccount'&&args[1])value={nonce:args[1].nonce.toString(),balance:args[1].balance.toString()};
  op(k,a,['getStorage','putStorage'].includes(k)?word(args[1]):null,value);
  const result=await raw[k](...args);if(k==='checkpoint')depth++;if(k==='commit'||k==='revert')depth--;if(depth<0)throw Error('unbalanced state API');return result;
 };}
 for(const k of ['get','put'])ts[k]=(...args)=>{
  const a=address(args[0]),key=word(args[1]);if(!known.has(a))throw Error('transient address not observed before step');known.get(a).transient.add(key);
  // S/T slot keys are registered by the asynchronous step hook before mutation.
  for(const s of scopes())if(!Object.hasOwn(s.pre[a]?.transient??{},key))throw Error('missing transient pre-state');
  op('transient.'+k,a,key,k==='put'?hex(args[2]):null);return transient[k](...args);
 };
 for(const k of ['clear','checkpoint','commit','revert'])ts[k]=(...args)=>{op('transient.'+k);return transient[k](...args);};
 event('beforeMessage',async m=>{
  if(!tx)throw Error('execution outside HOST1 boundary');const f={id:tx.frames.length,parent:stack.at(-1)?.id??null,depth:m.depth,caller:address(m.caller),to:m.to?address(m.to):null,kind:m.to?'call':'create',delegatecall:!!m.delegatecall,messageCodeAddress:m.to?address(m.codeAddress):null,messageFinalCodeAddress:null,executionAddress:m.to?address(m.to):null,codeAddress:m.to?address(m.codeAddress):null,invocationOpcode:stack.at(-1)?.lastOpcode??'ROOT',lastOpcode:null,value:m.value.toString(),data:hex(m.data),static:m.isStatic,pre:await snapshot(),steps:0,regions:[],output:null,memory:null,lastCallReturnData:null,createdAddress:null,post:null};
  messages.set(f,m);tx.frames.push(f);tx.trace.push({kind:'enter',frame:f.id});stack.push(f);await touch(f.caller);if(f.to)await touch(f.to);
 });
 event('step',async s=>{
  const f=stack.at(-1);if(!f||!tx)throw Error('orphan step');f.steps++;const a=address(s.address),code=s.codeAddress?address(s.codeAddress):f.kind==='create'?null:(()=>{throw Error('missing executed call code address');})();if(f.executionAddress!==null&&f.executionAddress!==a)throw Error('changed execution owner');if(f.kind==='call'&&f.codeAddress!==null&&f.codeAddress!==code)throw Error('changed code address');f.executionAddress=a;f.codeAddress=code;f.lastOpcode=s.opcode.name;if(!known.has(a))await touch(a);
  if(['SLOAD','SSTORE','TLOAD','TSTORE'].includes(s.opcode.name))await touch(a,s.opcode.name.startsWith('S')?'persistent':'transient','0x'+s.stack.at(-1).toString(16).padStart(64,'0'));
  if(/^(LOG[0-4]|RETURN|REVERT)$/.test(s.opcode.name)){
   if(!(s.memory instanceof Uint8Array)||s.memory.length!==Number(s.memoryWordCount)*32)throw Error('missing step memory');
   f.regions.push({step:f.steps,pc:s.pc,opcode:s.opcode.name,phase:'before-opcode',offset:s.stack.at(-1).toString(),length:s.stack.at(-2).toString(),allocatedBytes:s.memory.length,bytes:hex(s.memory)});
  }
 });
 event('afterMessage',async r=>{
  const f=stack.at(-1),e=r.execResult;if(!f||!(e.returnValue instanceof Uint8Array))throw Error('missing frame result');
  const message=messages.get(f);if(message.to){const a=address(message.to),c=address(message.codeAddress);if(f.executionAddress!==null&&f.executionAddress!==a||f.kind==='call'&&f.codeAddress!==null&&f.codeAddress!==c)throw Error('message/execution address mismatch');f.executionAddress=a;f.messageFinalCodeAddress=c;if(f.kind==='call')f.codeAddress=c;await touch(a);await touch(c);}
  f.output={bytes:hex(e.returnValue),exception:e.exceptionError?.error??null,...logsOf(e,f.steps)};f.createdAddress=r.createdAddress?address(r.createdAddress):null;if(f.createdAddress)await touch(f.createdAddress);
  if(e.runState){const size=Number(e.runState.memoryWordCount)*32;if(!Number.isSafeInteger(size)||size<0||typeof e.runState.memory?.read!=='function')throw Error('missing final memory');const b=e.runState.memory.read(0,size);if(!(b instanceof Uint8Array)||b.length!==size)throw Error('missing memory bytes');f.memory={status:'captured',phase:'after-interpreter',allocatedBytes:size,bytes:hex(b)};
   const i=e.runState.interpreter;if(typeof i?.getReturnData!=='function'||typeof i?.getReturnDataSize!=='function')throw Error('missing returndata API');const bytes=i.getReturnData();if(!(bytes instanceof Uint8Array)||BigInt(bytes.length)!==i.getReturnDataSize())throw Error('invalid returndata');f.lastCallReturnData={status:'captured',bytes:hex(bytes)};
  }else{if(f.steps)throw Error('missing executed memory');f.memory={status:'not-executed'};f.lastCallReturnData={status:'not-executed'};}
  f.post=await snapshot();tx.trace.push({kind:'exit',frame:f.id});stack.pop();
 });
 return {raw,async watch(a,slots={persistent:[],transient:[]}){await touch(a);for(const bank of ['persistent','transient'])for(const k of slots[bank]??[])await touch(a,bank,k);},snapshot,
  async begin(){if(tx||stack.length||depth!==0)throw Error('overlapping HOST1 boundary');tx={phase:'message',pre:await snapshot(),frames:[],trace:[],operations:[]};return tx;},
  phase(value){if(!tx)throw Error('no boundary');tx.phase=value;},
  assertCaptured(){if(errors.length)throw Error('observer failure: '+errors.join('; '));},
  finish(){if(errors.length)throw Error('observer failure: '+errors.join('; '));if(!tx||stack.length||depth!==0)throw Error('unfinished HOST1 boundary');const value=tx;tx=null;return value;},
  get depth(){return depth;},async abort(){while(depth>0)await sm.revert();stack=[];tx=null;},
  domain(){return [...known].sort(([a],[b])=>a.localeCompare(b)).map(([a,s])=>({address:a,persistent:[...s.persistent].sort(),transient:[...s.transient].sort()}));},
 };
}
