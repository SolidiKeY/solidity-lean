'use strict';
const {execFile}=require('node:child_process');
const {readFileSync}=require('node:fs');
const {join}=require('node:path');
const {failure,cancellable}=require('../rpc.cjs');
const {terminateTree}=require('../backend.cjs');
const language=require('../language-services.cjs');
const projects=require('../project.cjs');

// Wire request: solidityLean/showObligation
// {textDocument:{uri,version},position:{line,character}} -> null or
// {text,languageId:'lean',range,label}. text is the existing CLI printer's output,
// never a formula reconstructed in JavaScript. Tests can inject inspect(request).
// Inspect.lean's #wp prints a transformed formula; Testing lists/proves rows.
// Cli.lean inspectRequest calls testFormula and body.show/sourceProblemText.
function inspect({root,source,contract,signature,settings={},signal}) {
  const args=[join(root,'scripts/solidity-lean.mjs'),'inspect',source,'--json','--contract',contract,'--function',signature,'--show','obligation'];
  if(settings.projectRoot)args.push('--project-root',settings.projectRoot);
  for(const p of settings.includePaths||[])args.push('--include-path',p);
  for(const p of settings.remappings||[])args.push('--remapping',p);
  return new Promise((resolve,reject)=>{
    if(signal?.aborted)return reject(failure('Request cancelled',-32800));
    const child=execFile(process.execPath,args,{cwd:root,timeout:settings.timeoutMs||60000,maxBuffer:32*1024*1024},(error,stdout)=>{
      signal?.removeEventListener('abort',abort);
      if(signal?.aborted)return reject(failure('Request cancelled',-32800));
      try {
        const report=JSON.parse(stdout);
        if(error||report.errors?.length)throw new Error(report.errors?.map(e=>e.reason).join('\n')||error?.message||'Inspection failed');
        const rows=report.results?.filter(r=>r.contract===contract&&r.signature===signature);
        if(rows?.length!==1||rows[0].status!=='inspected'||typeof rows[0].text!=='string'||!rows[0].text.trim())throw new Error(rows?.[0]?.reason||'No printed obligation for this function');
        resolve(rows[0].text);
      }catch(e){reject(e);}
    });
    const abort=()=>terminateTree(child);
    signal?.addEventListener('abort',abort,{once:true});
    if(signal?.aborted)abort();
  });
}
function createHandler(service,backend=inspect) {
  return async (params,id)=>{
    const controller=new AbortController(),signal=controller.signal;
    service.requests.set(id,controller);
    try {
      const ref=params?.textDocument,doc=service.docs.get(ref?.uri);
      if(!doc||!Number.isSafeInteger(ref.version)||ref.version!==doc.version)throw failure('Document content changed',-32801);
      const version=doc.version,text=doc.text,generation=service.generation;
      const current=()=>{
        if(signal.aborted)throw failure('Request cancelled',-32800);
        if(!service.current(doc,version,generation)||doc.text!==text)throw failure('Document content changed',-32801);
      };
      current();
      await cancellable(service.analyze(doc),signal);current();
      const index=doc.index;
      const node=index?.nodes.find(n=>n.nodeType==='FunctionDefinition'&&n.name&&language.contains(index.nameRange(n),params.position));
      if(!node)return null;
      const range=index.nameRange(node);
      // Older solc metadata can fall back to the whole declaration. Never
      // attach an obligation hover to its body or parameters.
      if(text.slice(language.offset(text,range.start),language.offset(text,range.end))!==node.name)return null;
      let parent=index.parents.get(node);while(parent&&parent.nodeType!=='ContractDefinition')parent=index.parents.get(parent);
      if(!parent)return null;
      const report=await service.verify(doc.uri,{listing:true,version,contract:parent.name},signal);current();
      const rows=report.results.filter(r=>r.sourceId===node.id&&r.contract===parent.name);
      if(rows.length!==1||typeof rows[0].signature!=='string')throw new Error('No independent obligation for this declaration');
      const compiled=doc.compiled,project=compiled?.project;
      const saved=()=>{
        current();
        if(readFileSync(doc.path,'utf8')!==text)throw failure('Save the Solidity document before inspecting its obligation',-32801);
        for(const other of service.docs.values())if(other.path!==doc.path&&readFileSync(other.path,'utf8')!==other.text)throw failure('Save Solidity buffers before inspecting obligations',-32801);
        if(project&&!projects.current(project,service.projectDocuments()))throw failure('Project changed during inspection',-32801);
      };
      saved();
      const output=await backend({root:service.root,source:doc.path,contract:parent.name,signature:rows[0].signature,settings:service.settings,signal});
      saved();
      if(typeof output!=='string'||!output.trim())throw new Error('Backend returned no obligation');
      return {text:output,languageId:'lean',range,label:parent.name+'.'+rows[0].signature};
    } finally {service.requests.delete(id);}
  };
}
function register(server){server.onRequest('solidityLean/showObligation',createHandler(server.service));}
module.exports={register,createHandler,inspect};
