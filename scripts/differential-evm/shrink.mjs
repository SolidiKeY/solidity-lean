import {assemble} from './generate.mjs';
/** Delta debugging to a deletion-1-minimal mismatch. Invalid and blocked
 * candidates never preserve a mismatch. Predicate must rerun both engines. */
export async function shrink(record, check) {
  const valid=r=>{try{assemble(r);return true;}catch{return false;}};
  if(await check(record)!=='mismatch')throw Error('initial case is not a mismatch');
  let best=structuredClone(record),n=2,attempts=0;
  while(best.instructions.length) {
    const size=Math.ceil(best.instructions.length/n);let reduced=false;
    for(let start=0;start<best.instructions.length;start+=size) {
      const candidate={...best,instructions:best.instructions.filter((_,i)=>i<start||i>=start+size)};
      if(!valid(candidate))continue;
      attempts++;
      if(await check(candidate)==='mismatch'){best=candidate;n=Math.max(2,n-1);reduced=true;break;}
    }
    if(reduced)continue;
    if(n>=best.instructions.length)break;
    n=Math.min(best.instructions.length,n*2);
  }
  return {record:best,attempts,minimality:'instruction deletion; fixed calldata and operands; any mismatch cause'};
}
