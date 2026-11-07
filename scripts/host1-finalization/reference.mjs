#!/usr/bin/env node
/** Tiny pinned native matrix. Freeze source-derived values BEFORE execution.
 * No Source/Lean/compiler correctness or signed-transaction claim. */
import {readFileSync,writeFileSync,mkdirSync,existsSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {createRequire} from 'node:module';
import {isDeepStrictEqual} from 'node:util';
import {createFinalizationSession,CALLER,sha,verifyEngine} from './index.mjs';
import {assertOracle} from './expect.mjs';
import {createAddressFromString,createContractAddress,createContractAddress2,hexToBytes,bytesToHex} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
import {keccak_256} from '../evm-reference/node_modules/@noble/hashes/sha3.js';
const ROOT=resolve(new URL('../..',import.meta.url).pathname),SRC='tests/host1-finalization/Boundary.sol';
const HELPER_FILES=['index.mjs','observe.mjs','receipt.mjs','expect.mjs','reference.mjs','interface.mts','index.d.mts'].map(n=>'scripts/host1-finalization/'+n);
const helperHashes=()=>Object.fromEntries(HELPER_FILES.map(p=>[p,sha(readFileSync(resolve(ROOT,p)))]));
const COMPILER_SHA='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390',VERSION='0.8.38+commit.1835d247.Emscripten.clang';
export const BENEFICIARY='0x'+'00'.repeat(18)+'beef',EMPTY='0x'+'00'.repeat(18)+'cafe';
export const word=n=>BigInt(n).toString(16).padStart(64,'0');
const W=n=>'0x'+word(n),M=10n**30n,V=0x1122334400000000000000000000000000000000000000000000000000000055n;
const codeHash=c=>bytesToHex(keccak_256(hexToBytes(c)));
const signature=s=>bytesToHex(keccak_256(new TextEncoder().encode(s)));
const callData=(sig,...args)=>signature(sig).slice(0,10)+args.map(word).join('');
const absent=()=>({exists:false,nonce:null,balance:null,code:'0x',codeSha256:sha(new Uint8Array()),codeHash:null,persistent:{[W(0)]:W(0)},transient:{[W(99)]:W(0)}});
const present=(nonce,balance,code='0x',stored=0)=>({exists:true,nonce:String(nonce),balance:String(balance),code,codeSha256:sha(hexToBytes(code)),codeHash:codeHash(code),persistent:{[W(0)]:W(stored)},transient:{[W(99)]:W(0)}});
const clone=structuredClone;
const compilerInput=(pipeline,optimized,source)=>({language:'Solidity',sources:{'Boundary.sol':{content:source}},settings:{viaIR:pipeline==='viaIR',evmVersion:'osaka',optimizer:{enabled:optimized,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'*':['abi','storageLayout','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers']}}}});
const artifactHashes=a=>Object.fromEntries(Object.entries(a).map(([k,v])=>[k,{creation:sha(hexToBytes('0x'+v.evm.bytecode.object)),runtime:sha(hexToBytes('0x'+v.evm.deployedBytecode.object))}]));
const seed=(emitter)=>({emitter,topics:[signature('Seed(uint256)'),W(V)],data:'0x'});
const spawn=(factory,child)=>({emitter:factory,topics:[signature('Spawn(address)')],data:W(child)});
export function profilePlan(artifacts,pipeline,optimized){
 const factory=createContractAddress(createAddressFromString(CALLER),0n).toString(),childNonce=n=>createContractAddress(createAddressFromString(factory),BigInt(n)).toString();
 const init='0x'+artifacts.Child.evm.bytecode.object,childCode='0x'+artifacts.Child.evm.deployedBytecode.object,hostInit='0x'+artifacts.Boundary.evm.bytecode.object,hostCode='0x'+artifacts.Boundary.evm.deployedBytecode.object;
 const salted=createContractAddress2(createAddressFromString(factory),hexToBytes(W(1)),hexToBytes(init)).toString();
 // Exact actor/domain predictions from CREATE nonce and CREATE2 initcode inputs,
 // not addresses returned by the machine under test.
 const failAddress=createContractAddress(createAddressFromString(CALLER),13n).toString();
 const actors=[...new Set([CALLER,BENEFICIARY,EMPTY,factory,salted,failAddress,...Array.from({length:8},(_,i)=>childNonce(i+1))])].sort();
 const watch=actors.map(address=>({address,persistent:[W(0)],transient:[W(99)]}));
 let model=Object.fromEntries(actors.map(a=>[a,absent()]));model[CALLER]=present(0,M);model[BENEFICIARY]=present(0,9);model[EMPTY]=present(0,0);let nonce=0n,balance=M,hostNonce=1n,beneficiary=9n,hostBalance=0n;
 const cases=[];
 const frame=(parent,to,data,value,bytes='0x',exception=null,logs=[])=>({parent,to,data,value:String(value),output:{bytes,exception,status:'captured',logs}});
 function add(id,kind,to,data,value,update,output,exception,logs,frames,eligible=[],retained=[],deleted=[]){for(const [i,f]of frames.entries()){f.id=i;f.depth=f.parent===null?0:frames[f.parent].depth+1;f.caller=f.parent===null?CALLER:frames[f.parent].to;f.static=f.static??false;f.kind=f.to===null?'create':'call';f.delegatecall=false;f.invocationOpcode=f.parent===null?'ROOT':f.to===null?(id.startsWith('create2-')?'CREATE2':'CREATE'):'CALL';f.messageCodeAddress=f.to;f.executionAddress=f.to??(f.parent===null?(id==='deploy'?factory:failAddress):(id.startsWith('create2-')?salted:childNonce(hostNonce)));f.createdAddress=f.kind==='create'?f.executionAddress:null;f.messageFinalCodeAddress=f.executionAddress;f.codeAddress=f.kind==='create'?null:f.executionAddress;}const pre=clone(model);nonce++;balance-=exception?0n:value;model[CALLER]=present(nonce,balance);update();const post=clone(model);cases.push({ordinal:cases.length,request:{id,kind,to,data,value:String(value)},pre,messagePost:clone(post),post,output,exception,logs,frames,eligible,retained,deleted});return cases.at(-1);}
 add('deploy','create',null,hostInit,0n,()=>{model[factory]=present(1,0,hostCode,7);},hostCode,null,[],[frame(null,null,hostInit,0,hostCode)]);
 function createCase(id,mode,value,salt=false){const child=salt?salted:childNonce(hostNonce),sig=salt?'create2AndDestroy(address,bytes32)':'createAndDestroy(address)',input=salt?callData(sig,BENEFICIARY,1):callData(sig,BENEFICIARY);const logs=[seed(child),spawn(factory,child)],die=callData('die(address)',BENEFICIARY),fin=[{address:child,beneficiary:BENEFICIARY}];
  const row=add(id,'call',factory,input,value,()=>{hostNonce++;beneficiary+=value;model[factory]=present(hostNonce,hostBalance,hostCode,7);model[BENEFICIARY]=present(0,beneficiary);model[child]=absent();},W(child),null,logs,[frame(null,factory,input,value,W(child),null,logs),frame(0,null,init,value,childCode,null,[seed(child)]),frame(0,child,die,0)],fin,[],[child]);row.messagePost[child]=present(1,0,childCode,42);return row;
 }
 createCase('new-destroy',null,5n);
 {
  const child=childNonce(hostNonce),input=callData('createDestroyAndRevert(address)',BENEFICIARY),die=callData('die(address)',BENEFICIARY);
  add('outer-revert','call',factory,input,7n,()=>{},'0xdeadbeef','revert',[],[frame(null,factory,input,7,'0xdeadbeef','revert'),frame(0,null,init,7,childCode,null,[seed(child)]),frame(0,child,die,0)]);
 }
 {
  const child=childNonce(hostNonce),input=callData('catchChildRevert(address)',BENEFICIARY),inner=callData('createDestroyAndRevert(address)',BENEFICIARY),die=callData('die(address)',BENEFICIARY),encoded='0x'+word(32)+word(4)+'deadbeef'.padEnd(64,'0');
  hostBalance+=11n;
  add('caught-child-revert','call',factory,input,11n,()=>{model[factory]=present(hostNonce,hostBalance,hostCode,7);},encoded,null,[],[({...frame(null,factory,input,11,encoded),lastCallReturnData:'0xdeadbeef'}),frame(0,factory,inner,11,'0xdeadbeef','revert'),frame(1,null,init,11,childCode,null,[seed(child)]),frame(1,child,die,0)]);
 }
 const alive=childNonce(hostNonce),aliveInput=callData('createAlive()');
 add('create-alive','call',factory,aliveInput,13n,()=>{hostNonce++;model[factory]=present(hostNonce,hostBalance,hostCode,7);model[alive]=present(1,13,childCode,42);},W(alive),null,[seed(alive),spawn(factory,alive)],[frame(null,factory,aliveInput,13,W(alive),null,[seed(alive),spawn(factory,alive)]),frame(0,null,init,13,childCode,null,[seed(alive)])]);
 const kill=callData('die(address)',BENEFICIARY);add('old-destroy','call',alive,kill,0n,()=>{beneficiary+=13n;model[BENEFICIARY]=present(0,beneficiary);model[alive]=present(1,0,childCode,42);},'0x',null,[],[frame(null,alive,kill,0)],[],[{address:alive,beneficiary:BENEFICIARY}]);
 const self=callData('die(address)',alive);add('old-self-beneficiary','call',alive,self,3n,()=>{model[alive]=present(1,3,childCode,42);},'0x',null,[],[frame(null,alive,self,3)],[],[{address:alive,beneficiary:alive}]);
 createCase('create2-destroy',null,17n,true);createCase('create2-reuse',null,19n,true);
 const write=callData('transientWrite(uint256)',V),seen=[{emitter:factory,topics:[signature('Seen(uint256)')],data:W(V)}];add('transient-write','call',factory,write,0n,()=>{},W(V),null,seen,[frame(null,factory,write,0,W(V),null,seen)]);
 const read=callData('transientRead()');add('transient-next-message','call',factory,read,0n,()=>{},W(0),null,[],[frame(null,factory,read,0,W(0))]);
 add('static-refusal','static',factory,write,0n,()=>{},'0x','static state change',[],[({...frame(null,factory,write,0,'0x','static state change'),static:true})]);
 const empty=callData('touchEmpty(address)',EMPTY);const emptyRow=add('touched-empty','call',factory,empty,0n,()=>{model[EMPTY]=absent();},'0x',null,[],[frame(null,factory,empty,0),{parent:0,to:EMPTY,data:'0x',value:'0',output:{bytes:'0x',exception:null,status:'not-provided',logs:null}}],[],[],[EMPTY]);emptyRow.messagePost[EMPTY]=present(0,0);
 const failure='0x'+artifacts.Failing.evm.bytecode.object;
 add('constructor-revert','create',null,failure,23n,()=>{},'0xdeadbeef','revert',[],[frame(null,null,failure,23,'0xdeadbeef','revert')]);
 return {pipeline,optimized,factory,childNonce2:childNonce(2),salted,failAddress,watch,seeds:[{address:BENEFICIARY,nonce:'0',balance:'9',code:'0x',storage:{}},{address:EMPTY,nonce:'0',balance:'0',code:'0x',storage:{}}],cases,derivation:'Source values42/7, fixed full256bit event/transient value; CREATE RLPnonce and CREATE2 keccak initcode identities; EIP6780 old/new distinction, EIP161 touched-empty deletion, EIP1153 reset. Caller nonce increments outside EVM message rollback; no fee accounting. All expected state/code/bytes/log/frame fields frozen before execution.'};
}
export async function runReference(compilerFile,destination){
 const out=resolve(destination);if(existsSync(join(out,'freeze.json')))throw Error('HOST1 output prefix already frozen');mkdirSync(out,{recursive:true});const source=readFileSync(resolve(ROOT,SRC),'utf8');if(sha(readFileSync(compilerFile))!==COMPILER_SHA)throw Error('compiler SHA mismatch');const solc=createRequire(import.meta.url)(resolve(compilerFile));if(solc.cwrap('solidity_version','string',[])()!==VERSION)throw Error('compiler version mismatch');const compile=solc.cwrap('solidity_compile','string',['string','number','number']);const profiles=[];
 for(const pipeline of ['legacy','viaIR'])for(const optimized of [false,true]){const input=compilerInput(pipeline,optimized,source);const raw=compile(JSON.stringify(input),0,0),output=JSON.parse(raw);if(output.errors?.some(e=>e.severity==='error'))throw Error(JSON.stringify(output.errors));const id=pipeline+(optimized?'-opt':'-noopt');writeFileSync(join(out,id+'.input.json'),JSON.stringify(input,null,2)+'\n');writeFileSync(join(out,id+'.output.json'),raw);profiles.push({...profilePlan(output.contracts['Boundary.sol'],pipeline,optimized),id,inputSha256:sha(JSON.stringify(input)),outputSha256:sha(raw),codeHashes:artifactHashes(output.contracts['Boundary.sol'])});}
 const freeze={schema:1,helperHashes:helperHashes(),compiler:VERSION,compilerSha256:COMPILER_SHA,compilerCommit:'1835d247de183f23e7b0e2bc4a50732af525b77c',source:SRC,sourceSha256:sha(source),engine:verifyEngine(),profiles};const bytes=JSON.stringify(freeze,null,2)+'\n';writeFileSync(join(out,'freeze.json'),bytes);
 // No machine exists until all independent expectations/settings are immutable.
 const rows=[],errors=[];for(const p of profiles){const s=await createFinalizationSession({seeds:p.seeds.map(x=>({...x,nonce:BigInt(x.nonce),balance:BigInt(x.balance)})),watch:p.watch});for(const o of p.cases){try{const req={...o.request,value:BigInt(o.request.value)};if(req.to===null)delete req.to;const actual=await s.execute(req);writeFileSync(join(out,p.id+'-'+o.ordinal+'.json'),JSON.stringify(actual,null,2)+'\n');assertOracle(actual,o);rows.push({profile:p.id,id:o.request.id,ordinal:o.ordinal,status:'match',receipt:p.id+'-'+o.ordinal+'.json',receiptSha256:sha(JSON.stringify(actual,null,2)+'\n')});}catch(e){errors.push({profile:p.id,id:o.request.id,ordinal:o.ordinal,message:e.message});break;}}}
 if(readFileSync(join(out,'freeze.json'),'utf8')!==bytes)throw Error('frozen oracle changed');const report={schema:1,scope:'Finite native message/finalization evidence only; no Source/compiler theorem or runTx/envelope fees',sourceSha256:freeze.sourceSha256,freezeSha256:sha(bytes),profiles:profiles.map(p=>p.id),expectedCalls:profiles.reduce((n,p)=>n+p.cases.length,0),rows,errors,fullProofGate:'pending'};writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');return report;
}
export function validateReferenceReport(destination){
 const out=resolve(destination),report=JSON.parse(readFileSync(join(out,'report.json'))),freezeBytes=readFileSync(join(out,'freeze.json')),freeze=JSON.parse(freezeBytes);
 if(!isDeepStrictEqual(freeze.helperHashes,helperHashes()))throw Error('stale HOST1 producer body');
 if(report.schema!==1||report.fullProofGate!=='pending'||report.freezeSha256!==sha(freezeBytes)||freeze.sourceSha256!==sha(readFileSync(resolve(ROOT,SRC)))||report.sourceSha256!==freeze.sourceSha256||freeze.compiler!==VERSION||freeze.compilerSha256!==COMPILER_SHA||freeze.compilerCommit!=='1835d247de183f23e7b0e2bc4a50732af525b77c'||!isDeepStrictEqual(freeze.engine,verifyEngine()))throw Error('stale/malformed HOST1 provenance');
 const required=['legacy-noopt','legacy-opt','viaIR-noopt','viaIR-opt'];if(!isDeepStrictEqual(report.profiles,required)||!Array.isArray(freeze.profiles)||!isDeepStrictEqual(freeze.profiles.map(p=>p.id),required)||!Array.isArray(report.rows)||!Array.isArray(report.errors)||report.errors.length)throw Error('missing/reordered/failed HOST1 profiles');
 let ordinal=0;for(const p of freeze.profiles){const input=JSON.parse(readFileSync(join(out,p.id+'.input.json'))),raw=readFileSync(join(out,p.id+'.output.json')),output=JSON.parse(raw),pipeline=p.id.startsWith('legacy')?'legacy':'viaIR',optimized=p.id.endsWith('-opt');
  if(p.pipeline!==pipeline||p.optimized!==optimized||p.inputSha256!==sha(JSON.stringify(input))||p.outputSha256!==sha(raw)||input.sources['Boundary.sol'].content!==readFileSync(resolve(ROOT,SRC),'utf8')||input.settings.viaIR!==(pipeline==='viaIR')||input.settings.evmVersion!=='osaka'||input.settings.optimizer.enabled!==optimized||input.settings.optimizer.runs!==200||input.settings.metadata.appendCBOR!==false)throw Error('wrong compiler profile/input');
  if(!isDeepStrictEqual(input,compilerInput(pipeline,optimized,readFileSync(resolve(ROOT,SRC),'utf8')))||output.errors?.some(e=>e.severity==='error')||!isDeepStrictEqual(p.codeHashes,artifactHashes(output.contracts['Boundary.sol'])))throw Error('incomplete compiler settings/code provenance');
  const derived=profilePlan(output.contracts['Boundary.sol'],pipeline,optimized);for(const [k,v]of Object.entries(derived))if(!isDeepStrictEqual(p[k],v))throw Error('frozen oracle changed: '+k);
  for(const o of p.cases){const row=report.rows[ordinal++];if(!row||row.profile!==p.id||row.id!==o.request.id||row.ordinal!==o.ordinal||row.status!=='match'||row.receipt!==p.id+'-'+o.ordinal+'.json')throw Error('missing/reordered/incorrect actual call');const bytes=readFileSync(join(out,row.receipt));if(sha(bytes)!==row.receiptSha256)throw Error('actual receipt hash mismatch');assertOracle(JSON.parse(bytes),o);}
 }
 if(report.expectedCalls!==ordinal||report.rows.length!==ordinal)throw Error('missing/extra actual observations');return {profiles:4,calls:ordinal,fullProofGate:'pending'};
}
if(process.argv[1]===new URL(import.meta.url).pathname){const report=await runReference(process.argv[2],process.argv[3]);console.log(JSON.stringify({expectedCalls:report.expectedCalls,matches:report.rows.length,errors:report.errors,fullProofGate:report.fullProofGate}));if(report.errors.length)process.exitCode=1;}
