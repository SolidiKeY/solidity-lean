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
