// Uses the existing bundled web/browser/worker.mjs protocol unchanged.
export class RuntimeClient {
  constructor(url = '/browser-worker.js') {
    this.worker = new Worker(url); this.pending = new Map(); this.next = 0;
    this.ready = new Promise((resolve,reject)=>{this.resolveReady=resolve;this.rejectReady=reject;});
    this.timer=setTimeout(()=>this.fail(Error('Browser verifier is missing or did not become ready. See Runtime and trust boundary.')),30000);
    this.worker.onmessage=({data})=>{
      if(data.method==='runtime' && data.params.proofReady) { clearTimeout(this.timer); this.resolveReady(); }
      if(data.method==='backendError' || data.method==='runtime' && data.params.error) this.fail(Error(data.params.message || data.params.error));
      if(data.id!==undefined) { const p=this.pending.get(data.id); if(!p)return; this.pending.delete(data.id); clearTimeout(p.timer); data.error?p.reject(Error(data.error.message)):p.resolve(data.result); }
    };
    this.worker.onerror=()=>this.fail(Error('Browser verifier could not load /browser-worker.js and its pinned assets. See Runtime and trust boundary.'));
  }
  fail(error) { clearTimeout(this.timer); this.rejectReady(error); for(const p of this.pending.values()){clearTimeout(p.timer);p.reject(error);} this.pending.clear(); this.worker.terminate(); }
  request(method,params) { return new Promise((resolve,reject)=>{const id=++this.next;const timer=setTimeout(()=>this.fail(Error('Verification timed out')),600000);this.pending.set(id,{resolve,reject,timer});this.worker.postMessage({id,method,params});}); }
  async verify(text,version) { await this.ready; await this.request('open',{name:'Playground.sol',text,version}); return this.request('verify',{name:'Playground.sol',version}); }
  close() { this.fail(Error('Verification cancelled')); }
}
