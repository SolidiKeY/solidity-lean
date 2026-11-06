// Owns one synchronous verifier worker. Stale results are discarded while a
// short cancelled check drains; long checks still get a bounded hard stop.
export class VerifierWorker {
  constructor(url,progress=()=>{}){this.url=url;this.progress=progress;this.sequence=0;this.pending=new Map();}
  boot(){
    if(this.booting)return this.booting;
    const worker=this.worker=new Worker(this.url);
    worker.onmessage=({data:m})=>{
      if(this.worker!==worker)return;
      if(m.method){this.progress(m);return;}
      const task=this.pending.get(m.id);if(!task)return;
      this.pending.delete(m.id);clearTimeout(task.timer);
      if(task.abandoned)return;
      if(m.error)task.reject(Object.assign(new Error(m.error.message),m.error));else task.resolve(m.result);
    };
    worker.onerror=e=>{if(this.worker===worker)this.dispose(new Error(e.message||'Verifier worker failed'));};
    this.booting=this.request('boot',{},600000);
    return this.booting;
  }
  request(method,params={},timeoutMs=600000){
    if(!this.worker)return Promise.reject(new Error('Verifier worker is not running'));
    const id=++this.sequence;
    return new Promise((resolve,reject)=>{
      const timer=setTimeout(()=>this.dispose(Object.assign(new Error('Browser verification timed out'),{code:'TIMEOUT'})),timeoutMs);
      this.pending.set(id,{method,resolve,reject,timer,abandoned:false});
      try{this.worker.postMessage({id,method,params});}catch(error){this.dispose(error);}
    });
  }
  abandon(reason=Object.assign(new Error('Verification cancelled'),{code:'CANCELLED'}),graceMs=1000){
    for(const task of this.pending.values()){
      if(task.method==='boot'||task.abandoned)continue;
      task.abandoned=true;task.reject(reason);clearTimeout(task.timer);
      task.timer=setTimeout(()=>{
        this.dispose(reason);
        this.progress({method:'restartRequired',message:'Cancelled verification exceeded its grace period.'});
      },graceMs);
    }
  }
  dispose(reason=Object.assign(new Error('Verification cancelled'),{code:'CANCELLED'})){
    this.worker?.terminate();this.worker=undefined;this.booting=undefined;
    for(const task of this.pending.values()){clearTimeout(task.timer);task.reject(reason);}
    this.pending.clear();
  }
}
