'use strict';
const {fork,spawn}=require('node:child_process');
const {join}=require('node:path');
const {mkdirSync,readFileSync,readdirSync,statSync}=require('node:fs');
const {createHash}=require('node:crypto');
const {failure}=require('./rpc.cjs');
const {trackChild,waitForClose}=require('./child-lifetime.cjs');
const {directFingerprint}=require('./direct-runtime.cjs');
const {nativeFingerprint}=require('./native-plugin.cjs');

const contentDigests=new Map();
function fileDigest(file){
  const s=statSync(file,{bigint:true}),identity=[s.dev,s.ino,s.size,s.mtimeNs,s.ctimeNs].map(String).join(':');
  const old=contentDigests.get(file);if(old?.identity===identity)return old.digest;
  const digest=createHash('sha256').update(readFileSync(file)).digest();
  if(contentDigests.size>32768)contentDigests.clear();contentDigests.set(file,{identity,digest});return digest;
}

/** Relevant sources and artifact identities invalidate caches and live Lean
 * environments together. Proof results are never reused across generations. */
function fingerprint(root,{sourcesOnly=false,buildInputs=false}={}){
  const hash=createHash('sha256');
  const visit=(directory,extensions,artifact=false)=>{
    if(!require('node:fs').existsSync(directory))return;
    for(const entry of readdirSync(directory,{withFileTypes:true}).sort((a,b)=>a.name.localeCompare(b.name))){
      const path=join(directory,entry.name);
      if(entry.isDirectory()){if(!['node_modules','.git','.lake'].includes(entry.name))visit(path,extensions,artifact);}
      else if(extensions.some(e=>entry.name.endsWith(e))){
        hash.update(path);
        if(artifact){const s=statSync(path);hash.update(JSON.stringify([s.size,s.mtimeMs,s.ctimeMs,s.ino]));}
        else hash.update(fileDigest(path));
      }
    }
  };
  for(const file of ['lean-toolchain','lakefile.toml','lake-manifest.json'])hash.update(fileDigest(join(root,file)));
  // Lake records the complete transitive frontend closure. Unrelated model
  // developments cannot affect this verifier. A changed import declaration is
  // itself in this set and invalidates the generation before the next build.
  let modules;
  if(!sourcesOnly&&!buildInputs)try{
    const setup=join(root,'.lake/build/ir/Solidity/Frontend/Testing.setup.json');
    const raw=readFileSync(setup),parsed=JSON.parse(raw);
    if(!parsed.importArts||typeof parsed.importArts!=='object')throw new Error('Invalid setup');
    modules=new Set([...Object.keys(parsed.importArts).filter(n=>n.startsWith('Solidity.')),'Solidity.Frontend.Testing','Solidity.Tools.DirectRuntime']);
    hash.update(raw);
  }catch{}
  if(modules){
    for(const name of [...modules].sort()){
      const path=join(root,name.replaceAll('.','/')+'.lean');hash.update(path);
      try{hash.update(fileDigest(path));}catch{hash.update('missing');}
    }
  }else visit(join(root,'Solidity'),['.lean']);
  visit(join(root,'scripts'),['.mjs']);
  visit(join(root,'vscode/src'),['.cjs']);
  if(!sourcesOnly&&!buildInputs){
    if(modules){
      const directories=new Map();
      for(const name of [...modules].sort()){
        const stem=join(root,'.lake/build/lib/lean',name.replaceAll('.','/')),directory=require('node:path').dirname(stem),base=require('node:path').basename(stem);
        if(!directories.has(directory))try{directories.set(directory,readdirSync(directory).sort());}catch{directories.set(directory,[]);}
        for(const entry of directories.get(directory))if(entry===base+'.olean'||entry.startsWith(base+'.')&&entry.endsWith('.hash')){
          const file=join(directory,entry),s=statSync(file);hash.update(file);hash.update(JSON.stringify([s.size,s.mtimeMs,s.ctimeMs,s.ino]));
        }
      }
    }else visit(join(root,'.lake/build/lib/lean'),['.olean','.hash'],true);
  }
  const solkey=process.env.SOLKEY_ROOT||join(root,'../solkey');
  {
    const gradle=join(solkey,'keyext.solidity.core/build.gradle');hash.update(readFileSync(gradle));
    const name=readFileSync(gradle,'utf8').match(/ext\.soljsonFile\s*=\s*"([^"]+)"/)?.[1];
    if(name){const s=statSync(join(solkey,'keyext.solidity.core/build/soljson',name));hash.update(JSON.stringify([s.size,s.mtimeMs,s.ctimeMs,s.ino]));}
  }
  if(!sourcesOnly){hash.update(nativeFingerprint(root,process.env,{inputsOnly:buildInputs}));hash.update(directFingerprint(root));}
  return hash.digest('hex');
}

class WorkerPool {
  constructor(root,directory,size=1,{startAfter,onSpawn,onRetire}={}){this.root=root;this.directory=directory;this.size=size;this.workers=[];this.queue=[];this.next=0;this.closed=false;this.onSpawn=onSpawn;this.onRetire=onRetire;this.retiring=new Set();this.ready=!startAfter;if(startAfter)Promise.resolve(startAfter).then(()=>{this.ready=true;this.drain();},error=>this.fail(error));}
  run(task,{signal,timeoutMs=60000,onProgress}={}){
    if(this.failure)return Promise.reject(this.failure);
    if(this.closed)return Promise.reject(failure('Worker pool closed'));
    if(signal?.aborted)return Promise.reject(failure('Request cancelled',-32800));
    return new Promise((resolve,reject)=>{
      const entry={task,resolve,reject,signal,onProgress,requestDeadline:Date.now()+timeoutMs};
      entry.abort=()=>this.finish(entry,failure('Request cancelled',-32800),undefined,true);
      entry.timer=setTimeout(()=>this.finish(entry,failure('Verification timed out',-32800),undefined,true),timeoutMs);
      signal?.addEventListener('abort',entry.abort,{once:true});this.queue.push(entry);this.drain();
    });
  }
  spawn(){
    const index=this.next++,directory=join(this.directory,String(index));mkdirSync(directory,{recursive:true});
    const child=fork(join(__dirname,'lsp-worker.cjs'),[],{cwd:this.root,detached:process.platform!=='win32',stdio:['ignore','ignore','pipe','ipc']});
    child.ownedGroup=process.platform!=='win32';
    const worker={child,directory,busy:null,stderr:'',closed:trackChild(child)};this.workers.push(worker);
    worker.closed.then(()=>{worker.exited=true;if(!worker.retiring)this.retire(worker);});
    child.stderr.on('data',chunk=>{worker.stderr=(worker.stderr+chunk).slice(-8000);});
    child.on('message',message=>{
      const entry=worker.busy;if(!entry||message.id!==entry.id)return;
      if(message.progress){entry.onProgress?.(message.progress);return;}
      this.finish(entry,message.error?Object.assign(new Error(message.error.message),{diagnostics:message.error.diagnostics}):null,message.result);
    });
    const crashed=error=>{if(worker.busy)this.finish(worker.busy,error,undefined,true);else this.retire(worker);};
    child.on('error',crashed);child.on('exit',(code,signal)=>crashed(new Error(`Verification worker exited ${code??signal}: ${worker.stderr}`)));
    try{worker.admission=Promise.resolve(this.onSpawn?.(child));}catch(error){worker.admission=Promise.reject(error);}worker.admission.catch(()=>{});
    return worker;
  }
  remove(worker){const i=this.workers.indexOf(worker);if(i>=0)this.workers.splice(i,1);}
  fail(error){this.failure=error;for(const entry of [...this.queue])this.finish(entry,error);}
  retire(worker,{graceful=false}={}){
    if(worker.retirement)return worker.retirement;worker.retiring=true;
    const deadline=Date.now()+1000;let cooperative=graceful&&!worker.exited&&worker.child.connected;
    if(cooperative)try{worker.child.send({action:'shutdown',deadline},error=>{if(error)try{require('./backend.cjs').terminateTree(worker.child);}catch{}});}catch{cooperative=false;}
    const retirement=waitForClose(worker.child,{closed:worker.closed,kill:!cooperative,deadline}).then(()=>{if(cooperative&&worker.child.exitCode!==0)throw new Error('Cooperative worker retirement failed');}).catch(error=>{try{require('./backend.cjs').terminateTree(worker.child);}catch{}throw error;});worker.retirement=retirement;this.retiring.add(retirement);
    retirement.then(()=>{this.retiring.delete(retirement);this.remove(worker);try{this.onRetire?.(worker.child);}catch(error){this.fail(error);}queueMicrotask(()=>this.drain());},error=>{this.retiring.delete(retirement);this.fail(error);});return retirement;
  }
  drain(){
    if(this.closed||this.failure||!this.ready)return;
    while(this.queue.length){
      let worker=this.workers.find(w=>!w.busy&&!w.retiring);
      if(!worker){if(this.workers.length>=this.size)return;try{worker=this.spawn();}catch(error){this.fail(error);return;}}
      const entry=this.queue.shift();if(entry.done)continue;
      entry.id=++this.next;entry.worker=worker;worker.busy=entry;
      worker.admission.then(()=>{if(entry.done||worker.retiring||this.closed)return;worker.child.send({...entry.task,id:entry.id,root:this.root,directory:worker.directory,requestDeadline:entry.requestDeadline},error=>{if(error)this.finish(entry,error,undefined,true);});},error=>this.finish(entry,error,undefined,true));
    }
  }
  finish(entry,error,result,kill=false){
    if(entry.done)return;entry.done=true;clearTimeout(entry.timer);entry.signal?.removeEventListener('abort',entry.abort);
    const index=this.queue.indexOf(entry);if(index>=0)this.queue.splice(index,1);
    if(entry.worker){
      const worker=entry.worker;worker.busy=null;
      if(kill)this.retire(worker);
    }
    if(error)entry.reject(error);else entry.resolve(result);
    this.drain();
  }
  dispose(){
    if(this.disposal)return this.disposal;this.closed=true;
    for(const entry of [...this.queue,...this.workers.map(w=>w.busy).filter(Boolean)])this.finish(entry,failure('Worker pool closed',-32800),undefined,true);
    this.disposal=Promise.all([...this.retiring,...this.workers.map(worker=>this.retire(worker,{graceful:!worker.busy}))]).then(()=>{if(this.failure)throw this.failure;});this.disposal.catch(()=>{});return this.disposal;
  }
}
module.exports={WorkerPool,fingerprint};
