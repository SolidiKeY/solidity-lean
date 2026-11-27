'use strict';
const {readFileSync}=require('node:fs');
const {failure,cancellable}=require('../rpc.cjs');
const language=require('../language-services.cjs');
const projects=require('../project.cjs');

// Wire request: solidityLean/showObligation
// {textDocument:{uri,version},position:{line,character}} -> null or
// {text,languageId:'lean',range,label}. text must be the complete spec!{f}
// sequent in the existing Lean printer's dl{…} notation, never reconstructed JS.
// Inject with createHandler(service, printObligation), or register(server) with
// service.testing.printObligation. The async backend receives
// {root,source,contract,declarationId,settings,signal} and returns that string.
// It must select the exact declaration (including overloads), honor cancellation,
// and use the existing service's owned-process lifecycle if it launches work.
// Missing production entry point: an Inspect/CLI/Testing API that prints the
// original spec!{f} sequent with the Lean dl printer. Inspect.lean #wp/#step
// transform formulas; Cli.inspectRequest returns bare body.show or KeY
// sourceProblemText; Testing lists/proves rows. CLI trees refuse recursive and
// callback obligations. None is the required general original-sequent endpoint.
async function inspect() {
  throw failure('Obligation display unavailable: the backend has no entry point that prints the original spec!{f} sequent in dl{…} notation',-32004);
}
function createHandler(service,backend=inspect) {
  return async (params,id)=>{
    const controller=new AbortController(),signal=controller.signal;
    service.requests.set(id,controller);
    try {
      const ref=params?.textDocument,doc=service.docs.get(ref?.uri);
      if(!doc||!Number.isSafeInteger(ref.version)||ref.version!==doc.version)throw failure('Document content changed',-32801);
      const version=doc.version,text=doc.text,generation=service.generation,settings=service.settings;
      const current=()=>{
        if(signal.aborted)throw failure('Request cancelled',-32800);
        if(!service.current(doc,version,generation)||doc.text!==text||service.settings!==settings)throw failure('Document content changed',-32801);
      };
      current();
      await cancellable(service.analyze(doc),signal);current();
      const index=doc.index;
      const node=index?.nodes.find(n=>n.nodeType==='FunctionDefinition'&&n.name&&language.contains(index.nameRange(n),params.position));
      if(!node)return null;
      const range=index.nameRange(node);
      if(params.position.line===range.end.line&&params.position.character===range.end.character)return null;
      // Older solc metadata can fall back to the whole declaration. Never
      // attach an obligation hover to its body or parameters.
      if(text.slice(language.offset(text,range.start),language.offset(text,range.end))!==node.name)return null;
      let parent=index.parents.get(node);while(parent&&parent.nodeType!=='ContractDefinition')parent=index.parents.get(parent);
      if(!parent)return null;
      const compiled=doc.compiled,project=compiled?.project;
      const saved=()=>{
        current();
        if(readFileSync(doc.path,'utf8')!==text)throw failure('Save the Solidity document before inspecting its obligation',-32010);
        for(const file of Object.values(project?.files||{}))if(readFileSync(file.path,'utf8')!==file.text)throw failure('Save project buffers before inspecting obligations',-32010);
        if(project&&!projects.current(project,service.projectDocuments()))throw failure('Project changed during inspection',-32801);
      };
      saved();
      const output=await cancellable(backend({root:service.root,source:doc.path,contract:parent.name,declarationId:node.id,settings:service.settings,signal}),signal);
      saved();
      if(typeof output!=='string'||!output.trim())throw new Error('Backend returned no obligation');
      return {text:output,languageId:'lean',range,label:parent.name+'.'+node.name};
    } finally {service.requests.delete(id);}
  };
}
function register(server){server.onRequest('solidityLean/showObligation',createHandler(server.service,server.service.testing?.printObligation));}
module.exports={register,createHandler,inspect};
