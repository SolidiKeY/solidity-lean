// Shared injected envelopes; no native observation or row-judgment evidence.
'use strict';
const {createHash}=require('node:crypto'),{phases}=require('../parity/menu-lifecycle.cjs');
function fixture(target='local'){
 const value={runId:'run',target,phases:[],forbiddenActions:[],events:[]};
 for(const phase of phases){const kind=phase==='tab'?'tab':'editor',visible=['source','restored'].includes(phase)||phase==='untitled'&&target==='dafny',binding={uri:phase==='untitled'?'untitled:1':'file:///'+(phase==='unrelated'?'unrelated.txt':'menus.'+(target==='local'?'sol':'dfy')),version:1,session:phase==='unrelated'?'txt':phase==='untitled'?'untitled':'source',language:phase==='unrelated'?'plaintext':target==='local'?'solidity':'dafny',scheme:phase==='untitled'?'untitled':'file',trusted:true,sourceHash:createHash('sha256').update(phase==='unrelated'?'Menu language isolation.\n':require('../parity/workloads.cjs').workload(target,1)).digest('hex')};
 const before={activeUri:binding.uri,items:visible?[{label:target==='local'?'Solidity Lean':'Dafny'},{label:target==='local'?'Build Compiler Artifact with Import Options':'Build with Custom Arguments'}]:[{label:'Copy'}]};for(const i of before.items)Object.assign(i,{ariaDisabled:null,className:'menuitem',withinViewport:true,bounds:{left:1,top:1,right:100,bottom:20}});value.phases.push({phase,binding,eventStart:0,eventEnd:0,events:[],after:structuredClone(binding),capture:{status:'captured',runId:'run',phase:'menus-'+phase,metadataHash:createHash('sha256').update(JSON.stringify({binding,target,kind,visible})).digest('hex'),capture:{captured:true,screenshot:true,contributionMenu:{binding:structuredClone(binding),before,after:structuredClone(before),submenuVisible:visible,kind}}}});
 }return value;
}
module.exports={fixture};
