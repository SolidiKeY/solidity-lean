/** Guarded regression: host resource refusal must never be counted as a native
 * payload match. Shared serial orchestration guard; no semantic implementation.
 * The external process-group guard remains required for CPU-blocked parents.
 */
import {readFileSync,readdirSync} from 'node:fs';import {getHeapStatistics} from 'node:v8';
const GiB=1024**3;
export function hostResourceGuard(onStop) {
 const memory=()=>{const text=readFileSync('/proc/meminfo','utf8');return {swap:Number(/^SwapTotal:\s+(\d+)/m.exec(text)[1])*1024,available:Number(/^MemAvailable:\s+(\d+)/m.exec(text)[1])*1024};};
 const first=memory();if(first.swap!==0)throw new Error('no-swap prerequisite');if(first.available<4*GiB)throw new Error('4GiB reserve prerequisite');if(getHeapStatistics().heap_size_limit>4*GiB+256*1024**2)throw new Error('parent heap prerequisite: use --max-old-space-size=4096');
 let reason=null,peak=0;
 const poll=()=>{const processes=new Map();for(const id of readdirSync('/proc')){if(!/^[0-9]+$/.test(id))continue;try{const s=readFileSync('/proc/'+id+'/status','utf8');processes.set(Number(id),{parent:Number(/^PPid:\s+(\d+)/m.exec(s)[1]),rss:Number(/^VmRSS:\s+(\d+)/m.exec(s)?.[1]??0)*1024});}catch{}}
 const owned=new Set([process.pid]);let changed=true;while(changed){changed=false;for(const [id,p] of processes)if(owned.has(p.parent)&&!owned.has(id)){owned.add(id);changed=true;}}
 let rss=0;for(const id of owned)rss+=processes.get(id)?.rss??0;peak=Math.max(peak,rss);const m=memory();if(!reason&&(m.swap!==0||m.available<4*GiB||rss>12*GiB)){reason=m.swap!==0?'swap detected':m.available<4*GiB?'4GiB reserve':'12GiB aggregate RSS';onStop(reason);}};
 poll();const timer=setInterval(poll,250);return {check(){if(reason)throw new Error('host resource stop: '+reason);},stop(){clearInterval(timer);},get peakAggregateRss(){return peak;}};
}
