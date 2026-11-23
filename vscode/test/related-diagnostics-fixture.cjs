// Shared injected fixtures only; never native evidence.
'use strict';
const path=require('node:path'),{pathToFileURL}=require('node:url'),{createHash}=require('node:crypto');
const {source,textForInput,phases,wireSnapshot}=require('../parity/related-diagnostics.cjs');
const digest=s=>createHash('sha256').update(s).digest('hex');
const config={target:'local',runId:'run',sourceHead:'a'.repeat(40),workspace:'/workspace/owned',operationTimeoutMs:60000,suite:'related-diagnostics'};
function fixture(input){
 const uri=pathToFileURL(path.join(config.workspace,'related-diagnostics.sol')).href,owner={processSession:'process-epoch',pid:123,birth:'456'},protocol=[],steps=[],events=[{kind:'process.spawn',data:{...owner,args:[path.resolve(__dirname,'../src/lsp-server.cjs')],cwd:path.resolve(__dirname,'../..')}}];
 for(let i=0;i<phases.length;i++){const phase=phases[i],text=textForInput(phase,input),b={uri,version:i+1,sourceHash:digest(text),session:'document-epoch',trusted:true,closed:false,language:'solidity',scheme:'file'},n=phase==='shifted'?1:0;
  protocol.push({...owner,direction:'client',message:{method:i?'textDocument/didChange':'textDocument/didOpen',params:i?{textDocument:{uri,version:b.version},contentChanges:[{text}]}:{textDocument:{uri,version:b.version,text,synchronizationId:'sync-epoch'}}}});
  const diagnostics=phase==='fixed'?[]:[{severity:1,source:'solc',code:1686,message:'duplicate',range:{start:{line:4+n,character:2},end:{line:4+n,character:27}},relatedInformation:[{message:'other declaration',location:{uri,range:{start:{line:5+n,character:2},end:{line:5+n,character:27}}}}]}];
  const publicationIndex=protocol.length;protocol.push({...owner,direction:'server',message:{method:'textDocument/publishDiagnostics',params:{uri,version:b.version,sourceHash:b.sourceHash,synchronizationId:'sync-epoch',diagnostics}}});
  if(phase==='fixed')protocol.push({...owner,direction:'server',message:{method:'solidityLean/status',params:{uri,version:b.version,sourceHash:b.sourceHash,synchronizationId:'sync-epoch',state:'ready'}}});
  steps.push({phase,status:'observed',before:b,after:structuredClone(b),diagnostics:wireSnapshot(diagnostics),publicationIndex,wireEnd:protocol.length,eventEnd:events.length,process:{...owner},elapsedMs:1});
 }
 return{...(input?{inputProfile:input}:{}),runId:config.runId,target:'local',sourceHead:config.sourceHead,status:'partial',captureStatus:'observed',steps,protocol,events};
}

module.exports={fixture,config};
