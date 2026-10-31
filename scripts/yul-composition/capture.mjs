/** Lane-owned observer of public instance APIs; no engine source/limits change.
 * Domain is all API-touched accounts/slots since installation, not all Ethereum.
 * Frame pre-state is at beforeMessage (after engine caller nonce handling).
 * Transaction pre-state is before machine.call/optional transaction cleanup.
 */
import {isDeepStrictEqual} from 'node:util';
import {machine} from '../evm-reference/replay.mjs';
import {createHash} from 'node:crypto';
import {keccak_256} from '../evm-reference/node_modules/@noble/hashes/sha3.js';
import {createAddressFromString,hexToBytes,bytesToHex} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
const hex=bytesToHex,word=b=>'0x'+hex(b).slice(2).padStart(64,'0');
const address=a=>a.toString().toLowerCase();
const sha=b=>createHash('sha256').update(b).digest('hex');
const ADDRESS=/^0x[0-9a-f]{40}$/,WORD=/^0x[0-9a-f]{64}$/,BYTES=/^0x(?:[0-9a-f]{2})*$/;
const plain=o=>o!==null&&typeof o==='object'&&!Array.isArray(o);
const number=n=>Number.isSafeInteger(n)&&n>=0;
export const CAPTURE_SCOPE='API-touched account/slot domain since observer installation; no untouched-world enumeration or state-root proof. Frame memory is raw diagnostic evidence, never cross-pipeline semantic equality.';
const FRESH=Symbol('fresh-exported-machine');
export async function capturedMachine() {
 const vm=await machine();return {vm,observer:observeMachine(vm,{},FRESH)};
}
export function observeMachine(vm,{seeds=['0x'+'12'.repeat(20)]}={},fresh) {
 const persistentInitiallyEmpty=fresh===FRESH;
 const sm=vm.evm.stateManager,ts=vm.evm.transientStorage;
 const methods=['getAccount','putAccount','deleteAccount','modifyAccountFields','getCode','putCode','getCodeSize','getStorage','putStorage','clearStorage','checkpoint','commit','revert'];
 const raw=Object.fromEntries(methods.map(k=>{if(typeof sm[k]!=='function')throw Error('missing public state API: '+k);return[k,sm[k].bind(sm)];}));
 const tr=Object.fromEntries(['get','put','clear','checkpoint','commit','revert','toJSON'].map(k=>{if(typeof ts[k]!=='function')throw Error('missing transient API: '+k);return[k,ts[k].bind(ts)];}));
 const known=new Map(seeds.map(a=>[a,{persistent:new Set(),transient:new Set()}]));
 for(const [a,slots]of Object.entries(tr.toJSON())) {
  if(!known.has(a))known.set(a,{persistent:new Set(),transient:new Set()});
  for(const key of Object.keys(slots))known.get(a).transient.add(key);
 }
 // Persistent storage has no public enumeration API. Never infer an unknown
 // boundary slot value after a bulk clear; a caller must discover it first.
 const cleared=new WeakMap();
 let tx=null,stack=[],errors=[];
 const scopes=()=>tx?[tx,...stack]:[];
 async function account(a) {
  const obj=createAddressFromString(a),value=await raw.getAccount(obj),code=await raw.getCode(obj);
  if(!(code instanceof Uint8Array))throw Error('missing code capture');
  return {exists:value!==undefined,balance:(value?.balance??0n).toString(),nonce:(value?.nonce??0n).toString(),code:hex(code),codeSha256:sha(code),persistent:{},transient:{}};
 }
 async function touch(a,kind,key) {
  if(!known.has(a))known.set(a,{persistent:new Set(),transient:new Set()});
  for(const s of scopes())if(!Object.hasOwn(s.pre,a))s.pre[a]=await account(a);
  if(kind) {
   known.get(a)[kind].add(key);const obj=createAddressFromString(a),b=hexToBytes(key);
   const value=word(kind==='persistent'?await raw.getStorage(obj,b):tr.get(obj,b));
   for(const s of scopes())if(!Object.hasOwn(s.pre[a][kind],key)) {
    if(kind==='persistent'&&!persistentInitiallyEmpty&&cleared.get(s)?.has(a))throw Error('unknown persistent pre-value after bulk clear');
    s.pre[a][kind][key]=value;
   }
  }
 }
 async function snapshot() {
  const result={};
  for(const a of [...known.keys()].sort()) {
   const entry=await account(a),obj=createAddressFromString(a);
   for(const kind of ['persistent','transient'])for(const key of [...known.get(a)[kind]].sort())entry[kind][key]=word(kind==='persistent'?await raw.getStorage(obj,hexToBytes(key)):tr.get(obj,hexToBytes(key)));
   result[a]=entry;
  }return result;
 }
 function operation(kind,a=null,key=null,value=null) {
  if(!tx)return;
  const frame=stack.at(-1)?.id??null,id=[kind,a,key,frame].join('/');
  const access=tx.accesses[id]??={kind,address:a,slot:key,frame,count:0};access.count++;
  if(!kind.startsWith('get')&&kind!=='transient.get')tx.operations.push({sequence:tx.operations.length,frame,kind,address:a,slot:key,value});
 }
 for(const k of methods)sm[k]=async function(...args) {
  const a=args[0]&&typeof args[0].toString==='function'?address(args[0]):null;
  const slot=['getStorage','putStorage'].includes(k)?hex(args[1]):null;
  if(a)await touch(a,slot?'persistent':null,slot);
  if(k==='clearStorage')for(const s of scopes()){if(!cleared.has(s))cleared.set(s,new Set());cleared.get(s).add(a);}
  operation(k,a,slot,k==='putStorage'?word(args[2]):k==='putCode'?hex(args[1]):null);
  return raw[k](...args);
 };
 for(const k of ['get','put','clear','checkpoint','commit','revert'])ts[k]=function(...args) {
  const a=['get','put'].includes(k)?address(args[0]):null,key=a?hex(args[1]):null;
  if(a) {
   if(!known.has(a))known.set(a,{persistent:new Set(),transient:new Set()});known.get(a).transient.add(key);
   const before=word(tr.get(args[0],args[1]));
   for(const s of scopes())if(s.pre[a]){if(!Object.hasOwn(s.pre[a].transient,key))s.pre[a].transient[key]=before;}else errors.push('transient access without account pre-state');
  }
  operation('transient.'+k,a,key,k==='put'?word(args[2]):k==='clear'?structuredClone(tr.toJSON()):null);
  return tr[k](...args);
 };
 const event=(name,fn)=>vm.evm.events.on(name,(data,done)=>{if(!tx){done();return;}Promise.resolve().then(()=>fn(data)).catch(e=>errors.push(name+': '+e.message)).then(done);});
 event('beforeMessage',async m=>{
  await touch(address(m.caller));if(m.to)await touch(address(m.to));
  const f={id:tx.frames.length,parent:stack.at(-1)?.id??null,depth:m.depth,caller:address(m.caller),address:m.to?address(m.to):null,codeAddress:m.to?address(m.codeAddress):null,kind:m.to?'call':'create',delegatecall:!!m.delegatecall,isStatic:!!m.isStatic,value:m.value.toString(),input:hex(m.data),pre:await snapshot(),steps:0,regions:[]};
  tx.frames.push(f);stack.push(f);tx.events.push({kind:'enter',frame:f.id});
 });
 event('step',async s=>{
  const f=stack.at(-1);if(!f||f.depth!==s.depth)throw Error('missing/reordered frame');f.steps++;f.address=address(s.address);f.codeAddress=s.codeAddress?address(s.codeAddress):f.kind==='create'?null:(()=>{throw Error('missing call code address');})();
  await touch(f.address);
  const name=s.opcode.name;
  if(['SLOAD','SSTORE','TLOAD','TSTORE'].includes(name))await touch(f.address,name.startsWith('S')?'persistent':'transient','0x'+s.stack.at(-1).toString(16).padStart(64,'0'));
  if(/^(LOG[0-4]|RETURN|REVERT)$/.test(name)) {
   if(!(s.memory instanceof Uint8Array)||s.memory.length!==Number(s.memoryWordCount)*32)throw Error('invalid step memory');
   f.regions.push({step:f.steps,pc:s.pc,opcode:name,phase:'before-opcode',offset:s.stack.at(-1).toString(),length:s.stack.at(-2).toString(),allocatedBytes:s.memory.length,bytes:hex(s.memory)});
  }
 });
 event('afterMessage',async r=>{
  const f=stack.at(-1);if(!f)throw Error('orphan afterMessage');const e=r.execResult;
  if(!(e.returnValue instanceof Uint8Array))throw Error('missing frame output');
  f.output={exception:e.exceptionError?.error??null,bytes:hex(e.returnValue)};
  if(Array.isArray(e.logs)) {f.output.logStatus='captured';f.output.logs=e.logs.map(l=>{if(!Array.isArray(l)||l.length!==3||!(l[0]instanceof Uint8Array)||l[0].length!==20||!Array.isArray(l[1])||!l[1].every(t=>t instanceof Uint8Array&&t.length===32)||!(l[2]instanceof Uint8Array))throw Error('malformed frame logs');return{emitter:hex(l[0]),topics:l[1].map(hex),data:hex(l[2])};});}
  else {if(f.steps)throw Error('missing executed-frame logs');f.output.logStatus='not-provided';f.output.logReason='No interpreter log array exposed';}f.createdAddress=r.createdAddress?address(r.createdAddress):null;
  if(f.createdAddress)await touch(f.createdAddress);
  if(e.runState) {
   const size=Number(e.runState.memoryWordCount)*32;
   if(!number(size)||typeof e.runState.memory?.read!=='function')throw Error('missing final memory API');
   const b=e.runState.memory.read(0,size);if(!(b instanceof Uint8Array)||b.length!==size)throw Error('missing final memory bytes');
   f.memory={status:'captured',phase:'after-interpreter',allocatedBytes:size,bytes:hex(b)};
   const interpreter=e.runState.interpreter;
   if(typeof interpreter?.getReturnData!=='function'||typeof interpreter.getReturnDataSize!=='function')throw Error('missing frame returndata API');
   const buffer=interpreter.getReturnData(),length=interpreter.getReturnDataSize();
   if(!(buffer instanceof Uint8Array)||BigInt(buffer.length)!==length)throw Error('malformed frame returndata');
   f.lastCallReturnData={status:'captured',bytes:hex(buffer),length:buffer.length};
  } else {if(f.steps)throw Error('missing executed-frame final memory');f.memory={status:'not-executed',reason:'no interpreter steps/runState (empty-code, precompile or admission failure)'};f.lastCallReturnData={status:'not-executed',reason:'no interpreter frame/register'};}
  f.post=await snapshot();tx.events.push({kind:'exit',frame:f.id});stack.pop();
 });
 return {async boundary(nextCallOrdinal,action) {
  if(tx)throw Error('overlapping boundary capture');errors=[];
  tx={pre:await snapshot(),frames:[],events:[],operations:[],accesses:{}};
  try {
   const effects=await action();if(stack.length||tx.frames.length||errors.length)throw Error('boundary unexpectedly executed EVM message');
   const evidence={schema:1,scope:CAPTURE_SCOPE,kind:'host-beginFrame',nextCallOrdinal,pre:tx.pre,post:await snapshot(),domain:[...known].sort(([a],[b])=>a.localeCompare(b)).map(([address,k])=>({address,persistent:[...k.persistent].sort(),transient:[...k.transient].sort()})),operations:tx.operations,accesses:Object.values(tx.accesses),effects};
   validateBoundary(evidence);return evidence;
  }finally{tx=null;stack=[];}
 },async run(options,id,before) {
  if(tx)throw Error('overlapping capture transaction');errors=[];
  tx={schema:1,scope:CAPTURE_SCOPE,persistentInitialDomain:persistentInitiallyEmpty?'fresh-exported-machine':'unknown-preinstallation',transaction:id,request:{caller:options.caller?address(options.caller):'0x'+'12'.repeat(20),to:options.to?address(options.to):null,input:hex(options.data??new Uint8Array()),value:(options.value??0n).toString()},pre:await snapshot(),frames:[],events:[],operations:[],accesses:{}};
  try {
   const boundary=before?await before():null,result=await vm.call(options);if(stack.length)throw Error('unclosed capture frames');if(errors.length)throw Error(errors.join(';'));
   tx.post=await snapshot();tx.domain=[...known].sort(([a],[b])=>a.localeCompare(b)).map(([a,k])=>({address:a,persistent:[...k.persistent].sort(),transient:[...k.transient].sort()}));
   tx.accesses=Object.values(tx.accesses).sort((a,b)=>JSON.stringify(a).localeCompare(JSON.stringify(b)));
   const capture=tx;validateCapture(capture);return {...result,capture,boundary};
  } finally {tx=null;stack=[];}
 }};
}
function validateWorld(w) {
  if(!plain(w))throw Error('missing account world');
  for(const [a,v]of Object.entries(w)) {
   if(!ADDRESS.test(a)||!plain(v)||typeof v.exists!=='boolean'||!/^\d+$/.test(v.balance)||!/^\d+$/.test(v.nonce)||!BYTES.test(v.code)||v.codeSha256!==sha(hexToBytes(v.code)))throw Error('malformed account capture');
   for(const kind of ['persistent','transient']){if(!plain(v[kind]))throw Error('missing slots');for(const[k,b]of Object.entries(v[kind]))if(!WORD.test(k)||!WORD.test(b))throw Error('malformed slot capture');}
  }
 }
/** Shape/domain/order validation; not an EVM execution proof. */
export function validateCapture(c) {
 if(!c||c.schema!==1||c.scope!==CAPTURE_SCOPE||!['fresh-exported-machine','unknown-preinstallation'].includes(c.persistentInitialDomain)||!number(c.transaction)||!c.transaction||!Array.isArray(c.domain)||!c.domain.length||!Array.isArray(c.frames)||!c.frames.length||!Array.isArray(c.events)||!Array.isArray(c.operations)||!Array.isArray(c.accesses))throw Error('missing capture evidence');
 validateWorld(c.pre);validateWorld(c.post);
 if(!plain(c.request)||!ADDRESS.test(c.request.caller)||!(c.request.to===null||ADDRESS.test(c.request.to))||!BYTES.test(c.request.input)||!/^\d+$/.test(c.request.value))throw Error('missing/malformed capture request');
 const domains=c.domain.map(d=>d.address);if(!isDeepStrictEqual(domains,[...new Set(domains)].sort()))throw Error('unordered/duplicate account domain');
 if(!isDeepStrictEqual(Object.keys(c.post).sort(),domains)||!isDeepStrictEqual(Object.keys(c.pre).sort(),domains))throw Error('missing account domain');
 for(const d of c.domain)for(const kind of ['persistent','transient']) {
  if(!Array.isArray(d[kind])||!isDeepStrictEqual(d[kind],[...new Set(d[kind])].sort()))throw Error('malformed slot domain');
  for(const w of [c.pre,c.post])if(!isDeepStrictEqual(Object.keys(w[d.address][kind]).sort(),d[kind]))throw Error('missing slot domain');
 }
 let next=0;const active=[];
 for(const ev of c.events) {
  const f=c.frames[ev.frame];if(!f)throw Error('missing frame');
  if(ev.kind==='enter'){if(f.id!==next++||f.parent!==(active.at(-1)??null)||f.depth!==active.length)throw Error('reordered frames');active.push(f.id);}
  else if(ev.kind==='exit'){if(active.pop()!==f.id)throw Error('reordered exits');}else throw Error('unknown frame event');
 }
 if(c.frames.filter(f=>f.parent===null).length!==1)throw Error('multiple/missing root frames');
 if(active.length||next!==c.frames.length||c.events.length!==2*c.frames.length)throw Error('incomplete frame events');
 for(const f of c.frames) {
  validateWorld(f.pre);validateWorld(f.post);
  if(!Object.keys(f.pre).length||!isDeepStrictEqual(Object.keys(f.pre).sort(),Object.keys(f.post).sort())||!f.pre[f.caller]||f.address&&!f.pre[f.address])throw Error('missing frame world domain');
  for(const a of Object.keys(f.pre))for(const kind of ['persistent','transient'])if(!isDeepStrictEqual(Object.keys(f.pre[a][kind]).sort(),Object.keys(f.post[a][kind]).sort()))throw Error('missing frame slot domain');
  if(!['call','create'].includes(f.kind)||typeof f.delegatecall!=='boolean'||typeof f.isStatic!=='boolean'||!(f.codeAddress===null||ADDRESS.test(f.codeAddress))||!(f.createdAddress===null||ADDRESS.test(f.createdAddress))||f.kind==='call'&&f.createdAddress!==null)throw Error('missing/malformed frame context');
  if(!number(f.steps)||!ADDRESS.test(f.caller)||!(f.address===null||ADDRESS.test(f.address))||!BYTES.test(f.input)||!/^\d+$/.test(f.value)||!plain(f.output)||!BYTES.test(f.output.bytes)||!(f.output.exception===null||typeof f.output.exception==='string'))throw Error('malformed frame evidence');
  if(f.output.logStatus==='captured'){if(!Array.isArray(f.output.logs)||!f.output.logs.every(l=>l&&ADDRESS.test(l.emitter)&&Array.isArray(l.topics)&&l.topics.every(t=>WORD.test(t))&&BYTES.test(l.data)))throw Error('missing/malformed frame logs');}else if(f.output.logStatus!=='not-provided'||f.steps!==0||typeof f.output.logReason!=='string')throw Error('missing frame logs');
  const m=f.memory;if(!m)throw Error('missing memory');
  if(m.status==='captured'){if(!number(m.allocatedBytes)||m.allocatedBytes%32||!BYTES.test(m.bytes)||hexToBytes(m.bytes).length!==m.allocatedBytes||m.phase!=='after-interpreter')throw Error('malformed final memory');}
  else if(m.status!=='not-executed'||f.steps!==0||typeof m.reason!=='string')throw Error('missing executed memory');
  const buffer=f.lastCallReturnData;if(!buffer||(f.memory.status==='captured'?(buffer.status!=='captured'||!number(buffer.length)||!BYTES.test(buffer.bytes)||hexToBytes(buffer.bytes).length!==buffer.length):(buffer.status!=='not-executed'||typeof buffer.reason!=='string')))throw Error('missing/malformed frame returndata');
  if(!Array.isArray(f.regions))throw Error('missing memory regions');let step=0;
  for(const r of f.regions){if(!number(r.step)||r.step<=step||r.step>f.steps||!number(r.pc)||r.phase!=='before-opcode'||!/^\d+$/.test(r.offset)||!/^\d+$/.test(r.length)||!number(r.allocatedBytes)||!BYTES.test(r.bytes)||hexToBytes(r.bytes).length!==r.allocatedBytes||!/^(LOG[0-4]|RETURN|REVERT)$/.test(r.opcode))throw Error('malformed/reordered memory region');step=r.step;}
 }
 for(const o of c.operations)if(o.kind==='transient.clear'&&(!plain(o.value)||!Object.entries(o.value).every(([a,v])=>ADDRESS.test(a)&&plain(v)&&Object.entries(v).every(([k,b])=>WORD.test(k)&&typeof b==='string'&&BYTES.test(b)&&hexToBytes(b).length<=32))))throw Error('malformed transient clear payload');
 const root=c.frames[0];
 if(root.caller!==c.request.caller||root.input!==c.request.input||root.value!==c.request.value||root.kind!==(c.request.to?'call':'create')||c.request.to&&root.address!==c.request.to||!isDeepStrictEqual(root.post,c.post))throw Error('inconsistent root request/world');
 for(const [i,o]of c.operations.entries())if(o.sequence!==i||!(o.frame===null||c.frames[o.frame])||typeof o.kind!=='string'||!(o.address===null||domains.includes(o.address))||!(o.slot===null||WORD.test(o.slot)))throw Error('malformed/reordered state operation');
 for(const a of c.accesses)if(!(a.frame===null||c.frames[a.frame])||!number(a.count)||!a.count||typeof a.kind!=='string'||!(a.address===null||domains.includes(a.address))||!(a.slot===null||WORD.test(a.slot)))throw Error('malformed access evidence');
 for(const a of [...c.accesses,...c.operations])if(a.address!==null&&a.frame!==null)for(const phase of ['pre','post'])if(!c.frames[a.frame][phase][a.address])throw Error('accessed account missing from frame domain');
 for(const a of [...c.accesses,...c.operations])if(a.slot!==null) {
  const kind=['getStorage','putStorage'].includes(a.kind)?'persistent':['transient.get','transient.put'].includes(a.kind)?'transient':null;
  const domain=c.domain.find(d=>d.address===a.address);
  if(!kind||!domain?.[kind].includes(a.slot))throw Error('accessed slot missing from declared domain');
  if(a.frame!==null)for(const phase of ['pre','post'])if(!Object.hasOwn(c.frames[a.frame][phase][a.address]?.[kind]??{},a.slot))throw Error('accessed slot missing from frame domain');
 }
 return c;
}
/** Independent controlled-fixture assertions; exact fields/regions only.
 * Never compares arbitrary compiler memory, allocation addresses or gas. */
export function compareState(c,oracle,aliases={}) {
 try {validateCapture(c);}catch(e){return{status:'blocked',reason:e.message};}
 if(oracle===null||oracle===undefined)return {status:'pending',reason:'no independent state/memory oracle'};
 if(!plain(oracle)||Object.keys(oracle).some(k=>!['accounts','slots','memory','buffers','slotMaps','frames','logs','installations','operations'].includes(k))||!['accounts','slots','memory','buffers','slotMaps','frames','logs','installations','operations'].some(k=>Array.isArray(oracle[k])&&oracle[k].length)||['accounts','slots','memory','buffers','slotMaps','frames','logs','installations','operations'].some(k=>oracle[k]!==undefined&&!Array.isArray(oracle[k])))return{status:'blocked',reason:'malformed/empty state oracle'};
 const differences=[],resolve=a=>aliases[a]??a;
 const validAddress=a=>typeof a==='string'&&ADDRESS.test(resolve(a));
 const keys=(o,allowed)=>plain(o)&&Object.keys(o).every(k=>allowed.includes(k));
 for(const e of oracle.accounts??[]) {
  if(!keys(e,['phase','address','fields'])||!['pre','post'].includes(e.phase)||!validAddress(e.address)||!plain(e.fields)||!Object.keys(e.fields).length)return{status:'blocked',reason:'malformed/empty account oracle'};
  for(const [k,v]of Object.entries(e.fields))if(!['exists','balance','nonce','code','codeSha256','hasCode'].includes(k)||(['exists','hasCode'].includes(k)?typeof v!=='boolean':k==='code'?!BYTES.test(v):k==='codeSha256'?!/^[0-9a-f]{64}$/.test(v):typeof v!=='string'||!/^\d+$/.test(v)))return{status:'blocked',reason:'malformed account field oracle'};
 }
 for(const e of oracle.slots??[])if(!keys(e,['phase','address','kind','slot','value'])||!['pre','post'].includes(e.phase)||!validAddress(e.address)||!['persistent','transient'].includes(e.kind)||!WORD.test(e.slot)||!WORD.test(e.value))return{status:'blocked',reason:'malformed slot oracle'};
 for(const e of oracle.memory??[])if(!keys(e,['frame','depth','exception','at','offset','bytes','count','occurrence','relativeOffset','windowLength','regionOffset'])||e.frame===undefined&&e.depth===undefined||e.frame!==undefined&&!number(e.frame)||e.depth!==undefined&&!number(e.depth)||e.count!==undefined&&(!number(e.count)||!e.count)||e.exception!==undefined&&![null,'revert','out of gas','stack overflow'].includes(e.exception))return{status:'blocked',reason:'malformed memory selector'};
 for(const e of oracle.memory??[])if(e.occurrence!==undefined&&(!number(e.occurrence)||!number(e.count)||e.count<1||e.occurrence>=e.count)||e.relativeOffset!==undefined&&typeof e.relativeOffset!=='boolean'||e.windowLength!==undefined&&!number(e.windowLength)||e.regionOffset!==undefined&&(typeof e.regionOffset!=='string'||!/^\d+$/.test(e.regionOffset)))return{status:'blocked',reason:'malformed memory window selector'};
 for(const e of oracle.slotMaps??[])if(!keys(e,['phase','address','kind','value'])||!['pre','post'].includes(e.phase)||!validAddress(e.address)||!['persistent','transient'].includes(e.kind)||!plain(e.value)||!Object.entries(e.value).every(([k,v])=>WORD.test(k)&&WORD.test(v)))return{status:'blocked',reason:'malformed slot-map oracle'};
 for(const e of oracle.slotMaps??[]) {
  const value=c[e.phase]?.[resolve(e.address)]?.[e.kind];if(!plain(value))return{status:'blocked',reason:'missing slot-map evidence'};
  if(!isDeepStrictEqual(value,e.value))differences.push('slotMap/'+e.phase+'/'+e.address+'/'+e.kind);
 }
 const frameFields=['kind','address','caller','codeAddress','createdAddress','depth','parent','delegatecall','isStatic','value','input','inputSignature','exception','bytes'];
 if(oracle.frames) {
  if(!oracle.frames.length)return{status:'blocked',reason:'empty frame oracle'};
  if(c.frames.length!==oracle.frames.length)differences.push('frame-count');
  for(const [index,e]of oracle.frames.entries()) {
   if(!keys(e,['frame','fields'])||e.frame!==index||!plain(e.fields)||!['kind','address','caller','depth','parent','exception'].every(k=>Object.hasOwn(e.fields,k)))return{status:'blocked',reason:'malformed/partial frame oracle'};
   for(const [k,v]of Object.entries(e.fields)) {
    if(!frameFields.includes(k)||['address','caller','codeAddress','createdAddress'].includes(k)&&!(v===null&&['codeAddress','createdAddress'].includes(k))&&!validAddress(v)||k==='kind'&&!['call','create'].includes(v)||['depth','parent'].includes(k)&&!(k==='parent'&&v===null)&&!number(v)||['delegatecall','isStatic'].includes(k)&&typeof v!=='boolean'||k==='value'&&(typeof v!=='string'||!/^\d+$/.test(v))||k==='exception'&&![null,'revert','out of gas','stack overflow','static state change'].includes(v)||['bytes','input'].includes(k)&&!BYTES.test(v)||k==='inputSignature'&&(typeof v!=='string'||!/^\w+\(\)$/.test(v)))return{status:'blocked',reason:'malformed frame field oracle'};
    const f=c.frames[e.frame];if(!f)return{status:'blocked',reason:'missing requested frame'};
    const actual=['bytes','exception'].includes(k)?f.output[k]:k==='inputSignature'?f.input:f[k];
    const expected=['address','caller','codeAddress','createdAddress'].includes(k)?(v===null?null:resolve(v)):k==='inputSignature'?hex(keccak_256(new TextEncoder().encode(v)).slice(0,4)):v;
    if(!isDeepStrictEqual(actual,expected))differences.push('frame/'+e.frame+'/'+k);
   }
  }
 }
 for(const e of oracle.logs??[]) {
  if(!keys(e,['frame','expected'])||!number(e.frame)||!Array.isArray(e.expected)||!e.expected.every(l=>keys(l,['emitter','topics','data'])&&validAddress(l.emitter)&&Array.isArray(l.topics)&&l.topics.every(t=>WORD.test(t))&&BYTES.test(l.data)))return{status:'blocked',reason:'malformed log oracle'};
  const f=c.frames[e.frame];if(f?.output.logStatus!=='captured')return{status:'blocked',reason:'missing frame log evidence'};
  if(!isDeepStrictEqual(f.output.logs,e.expected.map(l=>({...l,emitter:resolve(l.emitter)}))))differences.push('logs/'+e.frame);
 }
 for(const e of oracle.installations??[]) {
  if(!keys(e,['frame','address'])||!number(e.frame)||!validAddress(e.address))return{status:'blocked',reason:'malformed installation oracle'};
  const f=c.frames[e.frame],a=resolve(e.address),installed=f?.post[a]?.code,final=c.post[a]?.code;
  if(!f||installed===undefined||final===undefined)return{status:'blocked',reason:'missing installation evidence'};
  if(f.kind!=='create'||f.createdAddress!==a||f.output.exception!==null||f.output.bytes==='0x'||installed!==f.output.bytes||final!==installed)differences.push('installation/'+e.frame);
 }
 for(const e of oracle.operations??[]) {
  if(!keys(e,['kind','frame','address','slot','value','contains','count'])||!['putStorage','transient.put','transient.clear','revert','transient.revert'].includes(e.kind)||!number(e.count)||(e.count===0&&!(e.kind==='transient.put'&&e.address!==undefined&&e.slot!==undefined))||e.frame!==undefined&&!number(e.frame)||e.address!==undefined&&!validAddress(e.address)||e.slot!==undefined&&!WORD.test(e.slot)||e.value!==undefined&&!WORD.test(e.value)||e.contains!==undefined&&(!Array.isArray(e.contains)||!e.contains.length||!e.contains.every(x=>keys(x,['address','slot','value'])&&validAddress(x.address)&&WORD.test(x.slot)&&WORD.test(x.value))))return{status:'blocked',reason:'malformed operation oracle'};
  const matches=c.operations.filter(o=>o.kind===e.kind&&(e.frame===undefined||o.frame===e.frame)&&(e.address===undefined||o.address===resolve(e.address))&&(e.slot===undefined||o.slot===e.slot)&&(e.value===undefined||o.value===e.value)&&(!e.contains||e.contains.every(x=>typeof o.value?.[resolve(x.address)]?.[x.slot]==='string'&&BYTES.test(o.value[resolve(x.address)][x.slot])&&word(hexToBytes(o.value[resolve(x.address)][x.slot]))===x.value)));
  if(matches.length!==e.count)differences.push('operations/'+e.kind);
 }
 for(const e of oracle.buffers??[])if(!keys(e,['frame','bytes'])||!number(e.frame)||!BYTES.test(e.bytes))return{status:'blocked',reason:'malformed returndata oracle'};
 for(const e of oracle.buffers??[]) {
  const buffer=c.frames[e.frame]?.lastCallReturnData;
  if(buffer?.status!=='captured')return{status:'blocked',reason:'missing requested returndata buffer'};
  if(buffer.bytes!==e.bytes)differences.push('returndata/'+e.frame);
 }
 for(const e of oracle.accounts??[]) {
  const w=e.phase==='pre'?c.pre:e.phase==='post'?c.post:null,a=w?.[resolve(e.address)];
  if(!a)return {status:'blocked',reason:'missing requested account/phase'};
  for(const [k,v]of Object.entries(e.fields))if(k==='hasCode'?!isDeepStrictEqual(a.code!=='0x',v):!Object.hasOwn(a,k)) {if(k==='hasCode')differences.push(e.phase+'/'+e.address+'/'+k);else return{status:'blocked',reason:'missing account field'};}else if(k!=='hasCode'&&!isDeepStrictEqual(a[k],v))differences.push(e.phase+'/'+e.address+'/'+k);
 }
 for(const e of oracle.slots??[]) {
  const w=e.phase==='pre'?c.pre:e.phase==='post'?c.post:null,v=w?.[resolve(e.address)]?.[e.kind]?.[e.slot];
  if(v===undefined)return{status:'blocked',reason:'missing requested slot'};if(v!==e.value)differences.push(e.phase+'/'+e.address+'/'+e.kind+'/'+e.slot);
 }
 for(const e of oracle.memory??[]) {
  if(!number(e.offset)||!BYTES.test(e.bytes)||e.bytes==='0x'&&!(e.windowLength===0&&e.relativeOffset===true)||!(e.at==='final'||/^(LOG[0-4]|RETURN|REVERT)$/.test(e.at)))return{status:'blocked',reason:'malformed memory oracle'};
  const frames=c.frames.filter(f=>(e.frame===undefined||f.id===e.frame)&&(e.depth===undefined||f.depth===e.depth)&&(e.exception===undefined||f.output.exception===e.exception));
  const regions=frames.flatMap(f=>e.at==='final'&&f.memory.status==='captured'?[f.memory]:f.regions.filter(r=>r.opcode===e.at));
  if(!regions.length)return{status:'blocked',reason:'missing requested memory frame/region'};
  if(regions.length!==(e.count??1)){differences.push('memory-count/'+e.at);continue;}
  const selected=e.occurrence===undefined?regions:[regions[e.occurrence]];
  for(const r of selected) {
   if(e.windowLength!==undefined&&r.length!==String(e.windowLength)||e.regionOffset!==undefined&&r.offset!==e.regionOffset){differences.push('memory-operands/'+e.at);continue;}
   const start=e.offset+(e.relativeOffset?Number(r.offset):0);if(!number(start)||start+hexToBytes(e.bytes).length>r.allocatedBytes)return{status:'blocked',reason:'missing captured memory window'};
   if(hex(hexToBytes(r.bytes).slice(start,start+hexToBytes(e.bytes).length))!==e.bytes)differences.push('memory/'+e.at+'/'+(e.occurrence??'all'));
  }
 }
 return {status:differences.length?'mismatch':'match',differences};
}

/** Bind captured execution to its separately recorded observable result. */
export function validateCallCapture(c,actual,expected={}) {
 validateCapture(c);
 const root=c.frames[0];
 if(root.output.logStatus!=='captured'||!isDeepStrictEqual(root.output.logs,actual?.rawLogs??actual?.logs))throw Error('capture/log result mismatch');
 if(!actual||!actual.metrics||root.output.bytes!==actual.returnData||root.output.exception!==actual.exception||actual.failed!==(actual.exception!==null)||c.frames.reduce((n,f)=>n+f.steps,0)!==actual.metrics.steps)throw Error('capture/result mismatch');
 for(const [key,value]of Object.entries(expected))if((key==='transaction'?c.transaction:c.request[key])!==value)throw Error('capture/call identity mismatch: '+key);
 return c;
}

/** A host cleanup action, explicitly not an EVM message or runTx receipt. */
export function validateBoundary(c) {
 if(!c||c.schema!==1||c.scope!==CAPTURE_SCOPE||c.kind!=='host-beginFrame'||!number(c.nextCallOrdinal)||!c.nextCallOrdinal||Object.hasOwn(c,'frames')||Object.hasOwn(c,'request')||!Array.isArray(c.domain)||!Array.isArray(c.operations)||!Array.isArray(c.accesses)||!plain(c.effects)||!Array.isArray(c.effects.deletedAccounts)||!c.effects.deletedAccounts.every(a=>ADDRESS.test(a))||c.effects.transientReset!==true||!plain(c.effects.transientBeforeReset))throw Error('missing/malformed host boundary evidence');
 const transientJSON=v=>plain(v)&&Object.entries(v).every(([a,slots])=>ADDRESS.test(a)&&plain(slots)&&Object.entries(slots).every(([k,b])=>WORD.test(k)&&typeof b==='string'&&BYTES.test(b)&&hexToBytes(b).length<=32));
 if(!transientJSON(c.effects.transientBeforeReset))throw Error('malformed boundary transient metadata');
 for(const o of c.operations)if(o.kind==='transient.clear'&&!transientJSON(o.value)||o.kind==='putCode'&&(typeof o.value!=='string'||!BYTES.test(o.value)))throw Error('malformed host boundary payload');
 validateWorld(c.pre);validateWorld(c.post);
 const names=c.domain.map(d=>d.address);if(!isDeepStrictEqual(names,[...new Set(names)].sort())||!isDeepStrictEqual(Object.keys(c.pre).sort(),names)||!isDeepStrictEqual(Object.keys(c.post).sort(),names))throw Error('missing host boundary domain');
 for(const d of c.domain)for(const k of ['persistent','transient'])if(!Array.isArray(d[k])||!isDeepStrictEqual(d[k],[...new Set(d[k])].sort())||!isDeepStrictEqual(Object.keys(c.pre[d.address][k]).sort(),d[k])||!isDeepStrictEqual(Object.keys(c.post[d.address][k]).sort(),d[k]))throw Error('missing host boundary slots');
 for(const [i,o]of c.operations.entries())if(o.sequence!==i||o.frame!==null||!['putCode','putAccount','modifyAccountFields','clearStorage','deleteAccount','transient.clear'].includes(o.kind)||o.slot!==null||!(o.address===null||names.includes(o.address)))throw Error('malformed host boundary operation');
 for(const a of c.accesses)if(a.frame!==null||!number(a.count)||!a.count||a.slot!==null||!(a.address===null||names.includes(a.address)))throw Error('malformed host boundary access');
 return c;
}
