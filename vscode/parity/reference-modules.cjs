// Execute only immutable, caller-verified reference modules with explicit injected dependencies.
'use strict';
const path=require('node:path'),vm=require('node:vm');
function createReferenceLoader({references,compiler,modules,read}){
 const cache=new Map();
 function load(relative){
  if(cache.has(relative))return cache.get(relative).exports;
  const ref=references.find(r=>r.name===relative);if(!ref||!relative.endsWith('.ts'))throw Error('Unpinned module request: '+relative);
  const bytes=read(ref),module={exports:{}};cache.set(relative,module);
  try{
  const code=compiler.transpileModule(bytes.toString(),{compilerOptions:{module:compiler.ModuleKind.CommonJS,target:compiler.ScriptTarget.ES2020}}).outputText;
  const requireRef=name=>Object.hasOwn(modules,name)?modules[name]:name.startsWith('.')?load(path.posix.normalize(path.posix.join(path.posix.dirname(relative),name))+'.ts'):(()=>{throw Error('Unexpected module: '+name);})();
  vm.runInNewContext('(function(require,module,exports){'+code+'\n})',{}, {filename:ref.file} )(requireRef,module,module.exports);return module.exports;
  }catch(error){if(cache.get(relative)===module)cache.delete(relative);throw error;}
 }
 return load;
}
module.exports={createReferenceLoader};
