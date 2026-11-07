#!/usr/bin/env node
// Synthetic read-only metadata overhead, not compiler, proof, worker scaling or UI performance.
'use strict';
const {performance}=require('node:perf_hooks'),assert=require('node:assert/strict'),lookup=require('../src/lookup-state.cjs');
const range=(line,start,end)=>({start:{line,character:start},end:{line,character:end}});
function fixture(count,depth=0){
  const uri='file:///synthetic.sol',declarations=[],entries=[],symbols=[],bindingInputs=[],lines=Array(depth).fill('{');
  for(let i=0;i<count;i++){const name='x'+i,r=range(i+depth,5,5+name.length);lines.push('uint '+name+';');bindingInputs.push(range(i+depth,0,6+name.length));declarations.push({id:i,name,description:name,location:{uri,range:r},whole:range(i+depth,0,6+name.length),scopes:[]});entries.push({target:i,range:r,context:r,names:[name],scopes:[]});symbols.push({name,detail:'variable',range:range(i+depth,0,6+name.length),selectionRange:r,children:[]});}
  return {text:[...lines,...Array(depth).fill('}')].join('\n')+'\n',state:{uri,version:1,generation:'synthetic',declarations,entries,symbols,bindingInputs,dependencies:{files:{}},outdated:false}};
}
function run(){
 const results=[];
 for(const [count,depth] of [[100,0],[1000,0],[5000,0],[1000,32],[1000,128]]){
  const {text,state}=fixture(count,depth),samples=[];
  for(let trial=-2;trial<7;trial++){
   const begin=performance.now(),next=lookup.migrate(state,text,[{range:range(0,0,0),text:'// incomplete\n'}],2),result=lookup.query(next,'textDocument/definition',{position:{line:count+depth,character:5}}),elapsedMs=performance.now()-begin;
   assert.deepEqual(result,{uri:state.uri,range:range(count+depth,5,5+('x'+(count-1)).length)});assert.equal(next.entries.length,count);
   if(trial>=0)samples.push({trial,elapsedMs,rssBytes:process.memoryUsage().rss});
  }
  const sorted=samples.map(x=>x.elapsedMs).sort((a,b)=>a-b);results.push({records:count,braceDepth:depth,utf16Length:text.length,warmups:2,samples,medianMs:sorted[3],p95Ms:sorted[6]});
 }
 return {schemaVersion:1,node:process.version,scope:'synthetic migration plus one read-only definition query; includes declaration header guards and lexical provenance; excludes snapshot capture, compiler, proof, UI and worker scaling',coldWarmBoundary:'two in-process warmups; no cold compiler or OS cache claim',results};
}
if(require.main===module)process.stdout.write(JSON.stringify(run(),null,2)+'\n');
module.exports={run};
