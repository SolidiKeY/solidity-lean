/** Independent finite expectations, not a Source evaluator or proof. */
import assert from 'node:assert/strict';
import {validateFinalizedMessage} from './index.mjs';
export function assertOracle(r,o){
 const req={...o.request,value:BigInt(o.request.value)};if(req.to===null)delete req.to;validateFinalizedMessage(r,req,o.ordinal);
 assert.deepEqual(r.domain.map(d=>d.address),Object.keys(o.post).sort());
 assert.equal(r.message.bytes,o.output);assert.equal(r.message.exception,o.exception);assert.equal(r.message.status,'captured');assert.deepEqual(r.message.logs,o.logs);
 assert.deepEqual(r.finalization.eligible,o.eligible);assert.deepEqual(r.finalization.retained,o.retained);assert.deepEqual(r.finalization.deletedAccounts,o.deleted);
 for(const phase of ['pre','messagePost','post'])for(const [address,fields]of Object.entries(o[phase])){const a=r[phase][address];assert.ok(a,'missing '+phase+' '+address);for(const [key,value]of Object.entries(fields)){if(key==='persistent'||key==='transient'){for(const [k,v]of Object.entries(value))assert.equal(a[key][k],v,phase+'/'+address+'/'+key+'/'+k);}else assert.deepEqual(a[key],value,phase+'/'+address+'/'+key);}}
 assert.equal(r.frames.length,o.frames.length);for(const [i,f]of o.frames.entries())for(const [key,value]of Object.entries(f)){if(key==='output'){for(const [k,v]of Object.entries(value))assert.deepEqual(r.frames[i].output[k],v,'frame'+i+'/'+k);}else if(key==='lastCallReturnData'){assert.equal(r.frames[i].lastCallReturnData.status,'captured');assert.equal(r.frames[i].lastCallReturnData.bytes,value);}else assert.deepEqual(r.frames[i][key],value,'frame'+i+'/'+key);}
 // Raw memory is preserved per frame. Compare only the exact semantic terminal
 // byte window against independent output, never arbitrary compiler pointers.
 if(o.output!=='0x'){
  const f=r.frames[0],opcode=o.exception?'REVERT':'RETURN',region=f.regions.findLast(x=>x.opcode===opcode);assert.ok(region,'missing terminal memory region');assert.equal(region.length,String((o.output.length-2)/2));assert.equal(f.memory.status,'captured');const off=Number(region.offset),bytes=Buffer.from(f.memory.bytes.slice(2),'hex');assert.ok(Number.isSafeInteger(off)&&off>=0&&off+(o.output.length-2)/2<=bytes.length);assert.equal('0x'+bytes.subarray(off,off+(o.output.length-2)/2).toString('hex'),o.output);
 }
}
