/** Guarded regression: a failing EIP-7002/7251 system call must not be silently
 * accepted by the native request accumulator. Minimal reference-engine probe;
 * no source semantics or additional fixture matches are claimed. Exit1 exposes
 * the pinned engine disagreement, rather than turning it into a passing gate.
 */
import {createRequire} from 'node:module';
import {resolve,dirname} from 'node:path';
import {pathToFileURL} from 'node:url';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
if(!process.argv[2])throw new Error('usage: node system_request_reproducer.mjs H44_BULK');
const bulk=resolve(process.argv[2]), require=createRequire(bulk+'/reference/package.json');
const load=name=>import(pathToFileURL(require.resolve(name)).href);
const vmModule=await load('@ethereumjs/vm'), commonModule=await load('@ethereumjs/common'), util=await load('@ethereumjs/util');
const requestsPath=resolve(dirname(require.resolve('@ethereumjs/vm')),'requests.js');
const {accumulateRequests}=await import(pathToFileURL(requestsPath).href);
const {createVM}=vmModule,{Common,Mainnet,Hardfork}=commonModule;
const {Account,createAddressFromString,hexToBytes}=util;
const common=new Common({chain:Mainnet,hardfork:Hardfork.Osaka});
if(!common.isActivatedEIP(7002)||!common.isActivatedEIP(7251))throw new Error('required Osaka rules inactive');
// VM/EVM constructors install their pinned parameter tables on Common.
await createVM({common});
const address=n=>createAddressFromString('0x'+n.toString(16).padStart(40,'0'));
const caller=address(common.param('systemAddress'));
const cases=[];
for(const [eip,param] of [[7002,'withdrawalRequestPredeployAddress'],[7251,'consolidationRequestPredeployAddress']]) {
 for(const code of ['0xfe','0x5f5ffd']) {
  const to=address(common.param(param));
  const setup=async()=>{const vm=await createVM({common});await vm.stateManager.putAccount(to,new Account(1n,0n));await vm.stateManager.putCode(to,hexToBytes(code));return vm;};
  const direct=await (await setup()).evm.runCall({caller,to,gasLimit:common.param('systemCallGasLimit')});
  const directException=direct.execResult.exceptionError?.error??null;
  if(!directException)throw new Error('minimal probe did not fail execution');
  let accumulatorException=null,requestCount=null;
  try{requestCount=(await accumulateRequests(await setup(),[],30000000n,false)).length;}
  catch(error){accumulatorException=error.message;}
  cases.push({eip,address:to.toString(),code,direct_exception:directException,accumulator_exception:accumulatorException,request_count:requestCount,suppressed_failure:accumulatorException===null});
 }
}
const hash=p=>createHash('sha256').update(readFileSync(p)).digest('hex');
console.log(JSON.stringify({scope:'minimal native request accumulator; not a blockchain fixture or source proof',reference_lock_sha256:hash(bulk+'/reference/package-lock.json'),native_requests_sha256:hash(requestsPath),cases}));
if(cases.some(c=>c.suppressed_failure))process.exitCode=1;
