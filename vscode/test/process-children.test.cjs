// Injected kernel readbacks, never permission to kill an unowned process.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs');
const {directChildren}=require('../src/process-state.cjs');
function fixture(t,{unavailable=false,reused=false,partial=false,live=false}={}){const read=fs.readFileSync,list=fs.readdirSync;let scans=0,parentReads=0;
 function stat(pid,parent,birth){const f=Array(22).fill('0');f[0]=pid===100&&!live?'T':'S';f[1]=String(parent);f[19]=birth;return pid+' (node) '+f.join(' ');}
 t.mock.method(fs,'readdirSync',(p,...args)=>{if(p==='/proc/100/task'){if(unavailable)throw Error('CONFIG_PROC_CHILDREN unavailable');return ['100','105'];}if(p==='/proc'){scans++;return ['100','200','201','202'];}return list(p,...args);});
 t.mock.method(fs,'readFileSync',(p,...args)=>{if(p==='/proc/100/task/100/children')return '200 201';if(p==='/proc/100/task/105/children'){if(partial)throw Error('Thread child list disappeared');return '202 200';}if(p==='/proc/100/stat'){parentReads++;return stat(100,1,reused&&parentReads>1?'99':'10');}if(p==='/proc/200/stat')return stat(200,100,'20');if(p==='/proc/201/stat')return stat(201,999,'21');if(p==='/proc/202/stat')return stat(202,100,'22');return read(p,...args);});return()=>scans;
}
test('child discovery reads every thread, deduplicates and rejects foreign PPIDs',{skip:process.platform!=='linux'},t=>{const scans=fixture(t);assert.deepEqual(directChildren({pid:100,birth:'10'}).map(p=>p.pid),[200,202]);assert.equal(scans(),0);});
test('unavailable kernel lists retain the existing full PPID scan',{skip:process.platform!=='linux'},t=>{const scans=fixture(t,{unavailable:true});assert.deepEqual(directChildren({pid:100,birth:'10'}).map(p=>p.pid),[200,202]);assert.equal(scans(),1);});
test('parent PID reuse refuses child discovery',{skip:process.platform!=='linux'},t=>{fixture(t,{reused:true});assert.throws(()=>directChildren({pid:100,birth:'10'}),/identity changed/);});
test('partial or unconfirmed-stop child lists fall back rather than omit descendants',{skip:process.platform!=='linux'},t=>{
 for(const mode of [{partial:true},{live:true}]){const scans=fixture(t,mode);assert.deepEqual(directChildren({pid:100,birth:'10'}).map(p=>p.pid),[200,202]);assert.equal(scans(),1);t.mock.restoreAll();}
});
