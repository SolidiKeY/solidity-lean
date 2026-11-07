// Guard against DOM-resident but clipped output and observed capture ABA.
const {test}=require("node:test"),assert=require("node:assert/strict"),{errors}=require("../parity/output-visibility.cjs"),{sample}=require("./output-visibility-fixture.cjs");
test("output geometry rejects hidden/clipped/foreign/stale and capture replacement (injected)",()=>{
 const text="Owned readiness",before=sample(text);assert.deepEqual(errors(before,sample(text),text,"Solidity Lean"),[]);
 for(const mutate of [s=>s.characters[0].covered=false,s=>s.characters[0].boxes=[],s=>s.characters.pop(),s=>s.characters[0].unit="X",s=>s.text="foreign",s=>s.channel="foreign",s=>s.watchId="replacement",s=>s.epoch++,s=>s.scroll=[{left:1}],s=>s.viewport.right=900,s=>s.clock=0,s=>s.expected="foreign"]){const after=sample(text);mutate(after);assert.ok(errors(before,after,text,"Solidity Lean").length);}
 assert.ok(errors(null,null,text,"Solidity Lean").length);
});

test("stable foreign channel never authorizes owned geometry",()=>{const a=sample("ready"),b=sample("ready");a.channel=b.channel="foreign";assert.ok(errors(a,b,"ready","Solidity Lean").length);});
test("probe watches external DOM mutation, resize and scroll and removes owned observers (injected DOM)",()=>{
 const vm=require("node:vm"),{probe}=require("../parity/output-visibility.cjs"),listeners=new Map(),root={},panel={querySelector:()=>null,querySelectorAll:()=>[],getBoundingClientRect:()=>({left:0,top:0,right:100,bottom:100}),closest:()=>({querySelectorAll:()=>[]})};let callback,observed,disconnected=0;
 const context={crypto:{randomUUID:()=>"watch"},performance:{now:()=>1},MutationObserver:class{constructor(fn){callback=fn;}observe(target){observed=target;}takeRecords(){return [];}disconnect(){disconnected++;}},document:{documentElement:root,querySelector:()=>panel,addEventListener:(k,f)=>listeners.set(k,f),removeEventListener:k=>listeners.delete(k)},window:{addEventListener:(k,f)=>listeners.set(k,f),removeEventListener:k=>listeners.delete(k)}};vm.createContext(context);const run=()=>vm.runInContext("("+probe.toString()+")("+JSON.stringify("required")+")",context);
 assert.equal(run().epoch,0);assert.equal(observed,root,"ancestor/sibling mutations must be observed");callback([{target:{externalOverlay:true}}]);assert.equal(run().epoch,1);listeners.get("resize")();listeners.get("scroll")();assert.equal(run().epoch,3);vm.runInContext("("+probe.toString()+")(null,true)",context);assert.equal(listeners.size,0);assert.equal(disconnected,1);assert.equal(context.window.__solidityParityOutputWatch,undefined);
});
test('actual probe labels characters relative to readiness after preceding output (injected DOM)',()=>{
 const vm=require('node:vm'),{probe}=require('../parity/output-visibility.cjs'),rect={left:0,top:0,right:100,bottom:100},parent={parentElement:null,getBoundingClientRect:()=>rect,contains:()=>false},node={data:'prefix required',length:15,parentElement:parent},line={},panel={querySelector:()=>null,querySelectorAll:selector=>selector==='.view-line'?[line]:[],getBoundingClientRect:()=>rect,closest:()=>({querySelectorAll:()=>[{getClientRects:()=>[rect],selectedOptions:[{textContent:'Owned'}]}]})};
 const context={innerWidth:100,innerHeight:100,NodeFilter:{SHOW_TEXT:4},getComputedStyle:()=>({visibility:'visible',display:'block',opacity:'1',overflowX:'visible',overflowY:'visible'}),crypto:{randomUUID:()=> 'watch'},performance:{now:()=>1},MutationObserver:class{observe(){}takeRecords(){return [];}disconnect(){}},window:{addEventListener(){},removeEventListener(){}},document:{documentElement:{},querySelector:()=>panel,addEventListener(){},removeEventListener(){},createTreeWalker(){let used=false;return{nextNode(){if(used)return null;used=true;return node;}};},createRange:()=>({setStart(){},setEnd(){},getClientRects:()=>[{left:1,top:1,right:2,bottom:2}]}),elementFromPoint:()=>parent}};
 vm.createContext(context);const result=vm.runInContext('('+probe.toString()+')('+JSON.stringify('required')+')',context);assert.equal(result.start,7);assert.equal(result.characters.map(c=>c.unit).join(''),'required');assert.ok(result.characters.every(c=>c.covered));assert.deepEqual(errors(result,result,'required','Owned'),[]);
 const foreign={nodeName:'A',className:'detected-link',parentElement:null};context.document.elementFromPoint=()=>foreign;const refused=vm.runInContext('('+probe.toString()+')('+JSON.stringify('required')+')',context);const c=refused.characters[0];assert.equal(c.covered,false);assert.equal(c.range.outputOffset,7);assert.equal(c.range.requiredOffset,0);assert.equal(c.range.nodeOffset,7);assert.ok(c.diagnostic.reasons.includes('hit-ownership'));assert.equal(c.diagnostic.points[0][0].hit.tag,'A');assert.notEqual(c.diagnostic.points[0][0].hit.id,c.diagnostic.points[0][0].expected.id);assert.equal(c.diagnostic.points[0].length,5);assert.ok(c.diagnostic.styles.length);
 context.document.elementFromPoint=()=>parent;context.innerWidth=1;const clipped=vm.runInContext('('+probe.toString()+')('+JSON.stringify('required')+')',context);assert.ok(clipped.characters[0].diagnostic.reasons.includes('clip-or-empty-box'));assert.equal(clipped.characters[0].covered,false);
});

// Preparation never accepts a screenshot bracket or resets observer counters.
function preparationFixture(make){
 let clock=0,index=0;const records=[],visible={visible:true,selectedChannel:'Solidity Lean',continuousText:'ready'};
 const options={read:async()=>({...visible}),inspect:async()=>{const s=sample('ready');s.clock=clock;return make(s,index++);},valid:v=>v.visible&&v.selectedChannel==='Solidity Lean'&&v.continuousText==='ready',expected:'ready',channel:'Solidity Lean',deadline:15000,now:()=>clock,delay:async ms=>{clock+=ms;},record:async s=>records.push(s)};
 return{options,records,clock:()=>clock};
}
test('preparation retains changing samples before eventual stable endpoints without epoch reset (injected clock)',async()=>{
 const f=preparationFixture((s,i)=>({...s,epoch:i?9:0}));const result=await require('../parity/output-visibility.cjs').prepare(f.options);assert.equal(result.glyph.epoch,9);assert.equal(f.records.length,3);assert.deepEqual(f.records.map(s=>s.glyph.epoch),[0,9,9]);assert.ok(f.records[1].refusals.includes('capture interval changed'));assert.equal(f.clock(),100);
});
test('persistent churn, overlay ABA, foreign channel and clipped text exhaust original preparation budget (injected clock)',async()=>{
 for(const make of [(s,i)=>({...s,epoch:i}),(s,i)=>({...s,epoch:2*i}),(s)=>({...s,channel:'Foreign'}),(s)=>{s.characters[0].covered=false;return s;}]){
  const f=preparationFixture(make);await assert.rejects(require('../parity/output-visibility.cjs').prepare(f.options),e=>e.code==='TIMEOUT');assert.equal(f.clock(),15000);assert.equal(f.records.length,300);assert.ok(f.records.every(s=>s.refusals.length));
 }
});
test('missing/hidden/foreign visible state cannot prepare even with stable character geometry (injected clock)',async()=>{
 for(const changed of [{visible:false},{selectedChannel:'Foreign'},{continuousText:'stale'}]){const f=preparationFixture(s=>s);f.options.read=async()=>({visible:true,selectedChannel:'Solidity Lean',continuousText:'ready',...changed});await assert.rejects(require('../parity/output-visibility.cjs').prepare(f.options),e=>e.code==='TIMEOUT');assert.equal(f.clock(),15000);}
});
test('capture preparation removes its observer after actual injected inspection error',async()=>{
 const fs=require('node:fs'),os=require('node:os'),path=require('node:path'),directory=fs.mkdtempSync(path.join(os.tmpdir(),'output-prep-error-'));let stops=0;
 const client={async request(method,params){if(method==='Runtime.evaluate'&&params.expression.endsWith('(null,true)')){stops++;return{result:{value:true}};}throw Error('injected renderer inspection failure');}};
 try{await assert.rejects(require('../parity/renderer.cjs').captureOutput(client,directory,{readinessLine:'ready',channel:'Solidity Lean'}),/injected renderer inspection failure/);assert.equal(stops,1);}finally{fs.rmSync(directory,{recursive:true,force:true});}
});
test('a visible read completing at deadline is retained without further inspection (injected clock)',async()=>{
 const f=preparationFixture(s=>s);f.options.read=async()=>{await f.options.delay(15000);return{visible:true};};f.options.inspect=async()=>assert.fail('no postdeadline inspector admission');await assert.rejects(require('../parity/output-visibility.cjs').prepare(f.options),e=>e.code==='TIMEOUT');assert.equal(f.records.length,1);assert.equal(f.records[0].glyph,null);assert.ok(f.records[0].refusals[0].includes('deadline'));
});
test('unconfirmed cleanup cannot extend the original capture deadline or mask primary error (injected timers)',async t=>{
 const fs=require('node:fs'),os=require('node:os'),path=require('node:path'),directory=fs.mkdtempSync(path.join(os.tmpdir(),'output-cleanup-deadline-'));let closed=0,stops=0;
 t.mock.timers.enable({apis:['setTimeout']});const client={close(){closed++;},async request(method,params){if(method==='Runtime.evaluate'&&params.expression.endsWith('(null,true)')){stops++;return new Promise(()=>{});}throw Error('injected primary inspection failure');}};
 const pending=assert.rejects(require('../parity/renderer.cjs').captureOutput(client,directory,{readinessLine:'ready',channel:'Solidity Lean'}),/injected primary inspection failure/);
 try{await new Promise(resolve=>setImmediate(resolve));assert.equal(stops,1);t.mock.timers.tick(15000);await pending;assert.equal(closed,1);const cleanup=JSON.parse(fs.readFileSync(path.join(directory,'output-observer-cleanup.json')));assert.equal(cleanup.confirmed,false);assert.equal(cleanup.connectionRetired,true);}finally{t.mock.timers.reset();fs.rmSync(directory,{recursive:true,force:true});}
});
test('late cleanup success cannot acquire confirmation after original deadline (injected monotonic clock)',async t=>{
 const fs=require('node:fs'),os=require('node:os'),path=require('node:path'),{performance}=require('node:perf_hooks'),directory=fs.mkdtempSync(path.join(os.tmpdir(),'output-cleanup-late-'));let clock=0,closed=0;t.mock.method(performance,'now',()=>clock);
 const client={close(){closed++;},request(method,params){if(method==='Runtime.evaluate'&&params.expression.endsWith('(null,true)'))return Promise.resolve().then(()=>{clock=15001;return{result:{value:true}};});return Promise.reject(Error('injected primary inspection failure'));}};
 try{await assert.rejects(require('../parity/renderer.cjs').captureOutput(client,directory,{readinessLine:'ready',channel:'Solidity Lean'}),/injected primary inspection failure/);const cleanup=JSON.parse(fs.readFileSync(path.join(directory,'output-observer-cleanup.json')));assert.equal(cleanup.confirmed,false);assert.equal(closed,1);}finally{t.mock.restoreAll();fs.rmSync(directory,{recursive:true,force:true});}
});
