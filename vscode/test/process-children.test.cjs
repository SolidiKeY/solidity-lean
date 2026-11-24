// Injected kernel readbacks, never permission to kill an unowned process.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs');
const {directChildren}=require('../src/process-state.cjs');
function fixture(t,{unavailable=false,reused=false,partial=false,live=false,stopsAfterEnumeration=false,disappears=false,extraForeign=false,failure=Error('CONFIG_PROC_CHILDREN unavailable')}={}){const read=fs.readFileSync,list=fs.readdirSync;let scans=0,parentReads=0,tasksRead=0;const statReads=[];
 function stat(pid,parent,birth){const f=Array(22).fill('0');f[0]=pid===100&&(!live||stopsAfterEnumeration&&parentReads>1)?'T':'S';f[1]=String(parent);f[19]=birth;return pid+' (node) '+f.join(' ');}
 t.mock.method(fs,'readdirSync',(p,...args)=>{if(p==='/proc/100/task'){tasksRead++;if(unavailable)throw failure;return ['100','105'];}if(p==='/proc'){scans++;return ['100','200','201','202',...(extraForeign?['999']:[])];}return list(p,...args);});
 t.mock.method(fs,'readFileSync',(p,...args)=>{if(/^\/proc\/\d+\/stat$/.test(p))statReads.push(Number(p.split('/')[2]));if(p==='/proc/100/task/100/children')return '200 201';if(p==='/proc/100/task/105/children'){if(partial)throw Error('Thread child list disappeared');return '202 200';}if(p==='/proc/100/stat'){parentReads++;if(disappears&&parentReads>1)throw Object.assign(Error('gone'),{code:'ENOENT'});return stat(100,1,reused&&parentReads>1?'99':'10');}if(p==='/proc/200/stat')return stat(200,100,'20');if(p==='/proc/201/stat')return stat(201,999,'21');if(p==='/proc/202/stat')return stat(202,100,'22');if(p==='/proc/999/stat')return stat(999,1,'99');return read(p,...args);});return Object.assign(()=>scans,{statReads:()=>statReads.slice(),tasksRead:()=>tasksRead});
}
test('child discovery reads every thread, deduplicates and rejects foreign PPIDs',{skip:process.platform!=='linux'},t=>{const scans=fixture(t);assert.deepEqual(directChildren({pid:100,birth:'10'}).map(p=>p.pid),[200,202]);assert.equal(scans(),0);});
test('unavailable kernel lists retain the existing full PPID scan',{skip:process.platform!=='linux'},t=>{const scans=fixture(t,{unavailable:true});assert.deepEqual(directChildren({pid:100,birth:'10'}).map(p=>p.pid),[200,202]);assert.equal(scans(),1);});
test('parent PID reuse refuses child discovery',{skip:process.platform!=='linux'},t=>{fixture(t,{reused:true});assert.throws(()=>directChildren({pid:100,birth:'10'}),/identity changed/);});
test('partial or unconfirmed-stop child lists fall back rather than omit descendants',{skip:process.platform!=='linux'},t=>{
 for(const mode of [{partial:true},{live:true}]){const scans=fixture(t,mode);assert.deepEqual(directChildren({pid:100,birth:'10'}).map(p=>p.pid),[200,202]);assert.equal(scans(),1);t.mock.restoreAll();}
});

test('optional discovery diagnostics expose kernel versus full scan without changing selected children',{skip:process.platform!=='linux'},t=>{
 for(const mode of [{},{live:true},{unavailable:true},{partial:true}]){const scans=fixture(t,mode),events=[];assert.deepEqual(directChildren({pid:100,birth:'10'},(event,details)=>events.push({event,...details})).map(r=>r.pid),[200,202]);
  const fallback=Object.keys(mode).length>0;assert.equal(scans(),fallback?1:0);assert.equal(events.some(r=>r.event==='child.discovery.fallback'),fallback);assert.equal(events.at(-1).childCount,2);assert.equal(events.at(-1).mode,fallback?'ppid-scan':'kernel-children');assert.equal(events.find(r=>r.event==='child.discovery.enumerated').candidateCount,fallback?4:3);t.mock.restoreAll();
 }
});
test('throwing diagnostic callbacks cannot suppress discovery or birth-identity refusal',{skip:process.platform!=='linux'},t=>{
 fixture(t,{live:true});assert.deepEqual(directChildren({pid:100,birth:'10'},()=>{throw Error('diagnostic sink failed');}).map(r=>r.pid),[200,202]);t.mock.restoreAll();fixture(t,{reused:true});assert.throws(()=>directChildren({pid:100,birth:'10'},()=>{throw Error('diagnostic sink failed');}),/identity changed/);
});

test('fallback diagnostics do not inspect thrown null or hostile error accessors',{skip:process.platform!=='linux'},t=>{
 for(const failure of [null,Object.defineProperty({},'message',{get(){throw Error('must not inspect original failure');}})]){fixture(t,{unavailable:true,failure});const events=[];assert.deepEqual(directChildren({pid:100,birth:'10'},(event,details)=>events.push({event,...details})).map(r=>r.pid),[200,202]);assert.equal(events.find(r=>r.event==='child.discovery.fallback').reason,'kernel-child-list-unavailable');t.mock.restoreAll();}
});

test('a parent confirmed stopped after fallback enumeration uses the guarded kernel path',{skip:process.platform!=='linux'},t=>{
 const scan=fixture(t,{live:true,stopsAfterEnumeration:true,extraForeign:true}),events=[];assert.deepEqual(directChildren({pid:100,birth:'10'},(event,details)=>events.push({event,...details})).map(r=>r.pid),[200,202]);
 assert.equal(scan(),1);assert.equal(scan.tasksRead(),1);assert.equal(scan.statReads().includes(999),false);assert.equal(scan.statReads().filter(pid=>pid===100).length,3);assert.equal(events.find(r=>r.event==='child.discovery.stop-check').state,'T');assert.equal(events.at(-1).mode,'kernel-children-after-stop');assert.equal(events.find(r=>r.event==='child.discovery.enumerated').candidateCount,3);
});
test('late stop confirmation retains full scan when kernel lists are unavailable',{skip:process.platform!=='linux'},t=>{
 const scan=fixture(t,{live:true,stopsAfterEnumeration:true,unavailable:true}),events=[];assert.deepEqual(directChildren({pid:100,birth:'10'},(event,details)=>events.push({event,...details})).map(r=>r.pid),[200,202]);assert.equal(scan(),1);assert.equal(scan.tasksRead(),1);assert.equal(events.at(-1).mode,'ppid-scan');assert.equal(events.find(r=>r.event==='child.discovery.enumerated').candidateCount,4);
});
test('late stopped-state check refuses a reused parent before reading child identities',{skip:process.platform!=='linux'},t=>{
 const scan=fixture(t,{live:true,stopsAfterEnumeration:true,reused:true});assert.throws(()=>directChildren({pid:100,birth:'10'}),/identity changed/);assert.equal(scan.tasksRead(),0);assert.deepEqual(scan.statReads(),[100,100]);
});
test('a disappeared parent produces no discovered children',{skip:process.platform!=='linux'},t=>{
 fixture(t,{live:true,stopsAfterEnumeration:true,disappears:true});assert.deepEqual(directChildren({pid:100,birth:'10'}),[]);
});

test('late kernel fallback diagnostics never invoke error code getters',{skip:process.platform!=='linux'},t=>{
 let reads=0;const failure=Object.defineProperty({},'code',{get(){reads++;throw Error('must not evaluate diagnostic error accessor');}});fixture(t,{live:true,stopsAfterEnumeration:true,unavailable:true,failure});
 assert.deepEqual(directChildren({pid:100,birth:'10'},()=>{}).map(r=>r.pid),[200,202]);assert.equal(reads,0);
});
