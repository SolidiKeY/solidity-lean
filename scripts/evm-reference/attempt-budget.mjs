/** Explicit modern CommonJS engine budget; no loader/preload or opcode override. */
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve,dirname,join} from 'node:path';
const pins=JSON.parse(readFileSync(new URL('./attempt-budget-pins.json',import.meta.url)));
const sha=b=>createHash('sha256').update(b).digest('hex');
export const ATTEMPT_LIMIT=5_000_000;
export class AttemptLimit extends Error {
  constructor(message='EVM attempted-instruction budget exhausted') {super(message);this.name='AttemptLimit';this.code='ERR_EVM_ATTEMPT_LIMIT';}
}
export class AttemptBudget {
  #used=0; #aborted=false; #error; #maxDepth=0;
  constructor(limit=ATTEMPT_LIMIT) {
    if(!Number.isSafeInteger(limit)||limit<1||limit>ATTEMPT_LIMIT)throw new RangeError('invalid attempt limit');
    Object.defineProperty(this,'limit',{value:limit,enumerable:true});
  }
  get used(){return this.#used;}
  get aborted(){return this.#aborted;}
  get maxDepth(){return this.#maxDepth;}
  assertLive(){if(this.#aborted)throw this.#error;}
  poison(error){this.#aborted=true;this.#error??=error;}
  consume(depth=0){
    this.assertLive();
    if(this.#used===this.limit){const error=new AttemptLimit();this.poison(error);throw error;}
    this.#used++;this.#maxDepth=Math.max(this.#maxDepth,depth);
  }
}
export function verifyBudgetArtifact(modules){
  const req=createRequire(resolve(modules,'reference.cjs'));
  const entry=req.resolve('@ethereumjs/evm');
  const packageRoot=resolve(dirname(entry),'../..');
  for(const file of pins.files){
    const suffix=file.path.replace('@ethereumjs/evm/','');
    if(sha(readFileSync(join(packageRoot,suffix)))!==file.patchedSHA256)throw new Error('patched EVM source pin mismatch: '+suffix);
  }
}
/** Reset at an explicit original root only; nested calls keep this exact object. */
export async function runWithAttemptBudget(vm,kind,options,{limit=ATTEMPT_LIMIT,label='',onRecord=r=>console.log('ATTEMPT_BUDGET '+JSON.stringify(r))}={}){
  if(!['runCode','runCall'].includes(kind))throw new Error('unsupported budget root');
  const evm=vm.evm;
  if(evm.attemptBudgetAPIVersion!==pins.api)throw new Error('pinned attempt API missing');
  const budget=new AttemptBudget(limit);
  evm.beginAttemptBudget(budget);
  try{
    const result=await evm[kind](options);
    const exec=kind==='runCall'?result.execResult:result;
    onRecord({label,limit,used:budget.used,maxDepth:budget.maxDepth,status:'completed',
      exception:exec.exceptionError?.error??null,returnData:'0x'+Buffer.from(exec.returnValue).toString('hex'),gasUsed:exec.executionGasUsed.toString()});
    evm.endAttemptBudget(budget);
    return result;
  }catch(error){
    budget.poison(error); // Poisoned VM remains attached to this object forever.
    onRecord({label,limit,used:budget.used,maxDepth:budget.maxDepth,status:'blocked',code:error.code??null,error:error.message});
    throw error; // Never return a Solidity FAILURE or reuse a partial machine.
  }
}
