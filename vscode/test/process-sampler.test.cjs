// Injected /proc controls; no native parallelism or benchmark acceptance.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs');
test('sampler retains zombie stat evidence without reading its empty command line',t=>{
 if(process.platform!=='linux')return;
 const originalRead=fs.readFileSync,originalList=fs.readdirSync,core=require.resolve('../parity/core.cjs');let zombieCmdReads=0;const reads=[];
 function stat(pid,state,ppid,rss){const fields=Array(22).fill('0');fields[0]=state;fields[1]=String(ppid);fields[11]='2';fields[12]='3';fields[19]='birth'+pid;fields[21]=String(rss);return pid+' (node) '+fields.join(' ');}
 t.mock.method(fs,'readdirSync',(file,...args)=>file==='/proc'?['self','100','net','101','thread-self']:originalList(file,...args));
 t.mock.method(fs,'readFileSync',(file,...args)=>{if(file==='/proc/100/stat'){reads.push(100);return stat(100,'S',1,1);}if(file==='/proc/101/stat'){reads.push(101);return stat(101,'Z',100,0);}if(file==='/proc/100/cmdline')return 'node\0fixture';if(file==='/proc/101/cmdline'){zombieCmdReads++;throw Error('Zombie cmdline should not be opened');}return originalRead(file,...args);});
 let sampler;try{delete require.cache[core];const {ProcessSampler}=require(core);sampler=new ProcessSampler(100);const result=sampler.stop();assert.equal(zombieCmdReads,0);assert.deepEqual(reads.slice(0,2),[101,100]);assert.ok(result.samples.every(s=>s.processes.some(p=>p.pid===101&&p.ticks===5&&p.rssBytes===0&&p.start==='birth101')));assert.deepEqual(sampler.survivors(),[{pid:100,start:'birth100',name:'node'}]);}finally{if(sampler)clearInterval(sampler.timer);t.mock.restoreAll();delete require.cache[core];}
});
