'use strict';
const {fork,spawn}=require('node:child_process');
const {join}=require('node:path');
const {mkdirSync,readFileSync,readdirSync,statSync}=require('node:fs');
const {createHash}=require('node:crypto');
const {terminateTree}=require('./backend.cjs');
const {failure}=require('./rpc.cjs');

/** Relevant sources and artifact identities invalidate caches and live Lean
 * environments together. Proof results are never reused across generations. */
function fingerprint(root){
  const hash=createHash('sha256');
  const visit=(directory,extensions,artifact=false)=>{
    if(!require('node:fs').existsSync(directory))return;
    for(const entry of readdirSync(directory,{withFileTypes:true}).sort((a,b)=>a.name.localeCompare(b.name))){
      const path=join(directory,entry.name);
      if(entry.isDirectory()){if(!['node_modules','.git','.lake'].includes(entry.name))visit(path,extensions,artifact);}
      else if(extensions.some(e=>entry.name.endsWith(e))){
        hash.update(path);
        if(artifact){const s=statSync(path);hash.update(JSON.stringify([s.size,s.mtimeMs,s.ctimeMs,s.ino]));}
        else hash.update(readFileSync(path));
      }
    }
  };
  for(const file of ['lean-toolchain','lakefile.toml','lake-manifest.json'])hash.update(readFileSync(join(root,file)));
  visit(join(root,'Solidity'),['.lean']);visit(join(root,'scripts'),['.mjs']);
  visit(join(root,'vscode/src'),['.cjs']);
  visit(join(root,'.lake/build/lib/lean'),['.olean','.hash'],true);
  const solkey=process.env.SOLKEY_ROOT||join(root,'../solkey');
  {
    const gradle=join(solkey,'keyext.solidity.core/build.gradle');hash.update(readFileSync(gradle));
    const name=readFileSync(gradle,'utf8').match(/ext\.soljsonFile\s*=\s*"([^"]+)"/)?.[1];
    if(name){const s=statSync(join(solkey,'keyext.solidity.core/build/soljson',name));hash.update(JSON.stringify([s.size,s.mtimeMs,s.ctimeMs,s.ino]));}
  }
  return hash.digest('hex');
}

class WorkerPool {
  constructor(root,directory,size=1){this.root=root;this.directory=directory;this.size=size;this.workers=[];this.queue=[];this.next=0;this.closed=false;}
  run(task,{signal,timeoutMs=60000,onProgress}={}){
    if(this.closed)return Promise.reject(failure('Worker pool closed'));
    if(signal?.aborted)return Promise.reject(failure('Request cancelled',-32800));
    return new Promise((resolve,reject)=>{
      const entry={task,resolve,reject,signal,onProgress};
      entry.abort=()=>this.finish(entry,failure('Request cancelled',-32800),undefined,true);
      entry.timer=setTimeout(()=>this.finish(entry,failure('Verification timed out',-32800),undefined,true),timeoutMs);
      signal?.addEventListener('abort',entry.abort,{once:true});this.queue.push(entry);this.drain();
    });
  }
  spawn(){
    const index=this.next++,directory=join(this.directory,String(index));mkdirSync(directory,{recursive:true});
    const child=fork(join(__dirname,'lsp-worker.cjs'),[],{cwd:this.root,detached:process.platform!=='win32',stdio:['ignore','ignore','pipe','ipc']});
    const worker={child,directory,busy:null,stderr:''};this.workers.push(worker);
    child.stderr.on('data',chunk=>{worker.stderr=(worker.stderr+chunk).slice(-8000);});
    child.on('message',message=>{
      const entry=worker.busy;if(!entry||message.id!==entry.id)return;
      if(message.progress){entry.onProgress?.(message.progress);return;}
      this.finish(entry,message.error?Object.assign(new Error(message.error.message),{diagnostics:message.error.diagnostics}):null,message.result);
    });
    const crashed=error=>{if(worker.busy)this.finish(worker.busy,error,undefined,true);else this.remove(worker);};
    child.on('error',crashed);child.on('exit',(code,signal)=>crashed(new Error(`Verification worker exited ${code??signal}: ${worker.stderr}`)));
    return worker;
  }
  remove(worker){const i=this.workers.indexOf(worker);if(i>=0)this.workers.splice(i,1);}
  drain(){
    if(this.closed)return;
    while(this.queue.length){
      let worker=this.workers.find(w=>!w.busy);
      if(!worker){if(this.workers.length>=this.size)return;worker=this.spawn();}
      const entry=this.queue.shift();if(entry.done)continue;
      entry.id=++this.next;entry.worker=worker;worker.busy=entry;
      worker.child.send({...entry.task,id:entry.id,root:this.root,directory:worker.directory},error=>{if(error)this.finish(entry,error,undefined,true);});
    }
  }
  finish(entry,error,result,kill=false){
    if(entry.done)return;entry.done=true;clearTimeout(entry.timer);entry.signal?.removeEventListener('abort',entry.abort);
    const index=this.queue.indexOf(entry);if(index>=0)this.queue.splice(index,1);
    if(entry.worker){
      const worker=entry.worker;worker.busy=null;
      if(kill){this.remove(worker);terminateTree(worker.child);}
    }
    if(error)entry.reject(error);else entry.resolve(result);
    this.drain();
  }
  dispose(){
    if(this.closed)return;this.closed=true;
    for(const entry of [...this.queue,...this.workers.map(w=>w.busy).filter(Boolean)])this.finish(entry,failure('Worker pool closed',-32800),undefined,true);
    for(const worker of [...this.workers]){this.remove(worker);terminateTree(worker.child);}
  }
}
module.exports={WorkerPool,fingerprint};
