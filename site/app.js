// The Pages assembly fallback copies only four files. Keep this entry self-contained.
export const escapeHtml = value => String(value).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const MAX = 1024 * 1024;
export async function encodeSource(source) {
  const bytes = new TextEncoder().encode(source);
  if (bytes.length > MAX) throw Error('Source exceeds 1 MiB share limit');
  const data = new Uint8Array(await new Response(new Blob([bytes]).stream().pipeThrough(new CompressionStream('gzip'))).arrayBuffer());
  let binary = ''; for (const byte of data) binary += String.fromCharCode(byte);
  return '#source=' + btoa(binary).replaceAll('+','-').replaceAll('/','_').replace(/=+$/,'');
}
export async function decodeSource(hash) {
  if (!hash.startsWith('#source=')) return null;
  const encoded = hash.slice(8);
  if (encoded.length > MAX * 2 || !/^[A-Za-z0-9_-]+$/.test(encoded)) throw Error('Invalid source link');
  const bytes = Uint8Array.from(atob(encoded.replaceAll('-','+').replaceAll('_','/')), c=>c.charCodeAt(0));
  const reader = new Blob([bytes]).stream().pipeThrough(new DecompressionStream('gzip')).getReader();
  const chunks=[]; let size=0;
  try { for (;;) { const {value,done}=await reader.read(); if(done) break; size+=value.length; if(size>MAX) throw Error('Source link exceeds 1 MiB'); chunks.push(value); } }
  finally { await reader.cancel(); }
  return new TextDecoder('utf-8',{fatal:true}).decode(await new Blob(chunks).arrayBuffer());
}
export function resultHtml(report) {
  const rows = (report.results || []).map((row,i) => {
    const status = row.status === 'proved' ? 'proved' : row.status === 'refuted' ? 'wrong' : 'unknown';
    const model = row.counterexample ? JSON.stringify(row.counterexample,null,2) : '';
    return `<button class="result ${status}" data-result="${i}">${escapeHtml(row.contract || '')}.${escapeHtml(row.signature || row.function || '?')}: ${status}<pre>${escapeHtml(row.reason || '')}${model ? '\nModel values (executable evidence):\n'+escapeHtml(model) : ''}</pre></button>`;
  });
  for (const error of report.errors || []) rows.push(`<p>${escapeHtml(error.reason || error.message || 'Verification error')}</p>`);
  return rows.join('') || '<p>Unknown: no function results returned.</p>';
}
export function highlight(source, range) {
  let block=false;
  return source.split('\n').map((line,i)=>{
    let out='',at=0;
    while(at<line.length) {
      if(block) { const end=line.indexOf('*/',at); const stop=end<0?line.length:end+2; out+=`<span class="comment">${escapeHtml(line.slice(at,stop))}</span>`;at=stop;if(end>=0)block=false;continue; }
      if(line.startsWith('/*',at)) { block=true;continue; }
      if(line.startsWith('//',at)) { out+=`<span class="comment">${escapeHtml(line.slice(at))}</span>`;break; }
      const rest=line.slice(at);
      const string=/^(?:"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*')/.exec(rest);
      const word=/^[A-Za-z_$][A-Za-z0-9_$]*/.exec(rest);
      if(string) {out+=`<span class="string">${escapeHtml(string[0])}</span>`;at+=string[0].length;}
      else if(word) {const text=escapeHtml(word[0]);out+=/^(?:pragma|solidity|contract|function|returns|return|public|external|internal|private|pure|view|uint\d*|int\d*|bool|if|else|require|assert|mapping|while|for)$/.test(word[0])?`<span class="kw">${text}</span>`:text;at+=word[0].length;}
      else {out+=escapeHtml(line[at++]);}
    }
    const marked=range && i>=range.start.line && i<=range.end.line-(range.end.line>range.start.line && range.end.character===0?1:0);
    return `<span class="line${marked?' marked':''}"><span class="no">${i+1}</span>${out || ' '}</span>`;
  }).join('');
}

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

if (typeof document !== 'undefined') {
const $=id=>document.getElementById(id), source=$('source'); let report=null, generation=0,client,selectedRange;
const draw=()=>{$('highlight').innerHTML=highlight(source.value,selectedRange);$('highlight').scrollTop=source.scrollTop;$('highlight').scrollLeft=source.scrollLeft;};
source.addEventListener('input',()=>{generation++;selectedRange=null;client?.close();client=null;report=null;$('results').textContent='Source changed; verify to refresh results.';draw();});
source.addEventListener('scroll',draw);
$('verify').onclick=async()=>{
  const epoch=++generation,text=source.value; client?.close();
  $('status').textContent='Preparing browser compiler and verifier…';$('verify').disabled=true;$('results').replaceChildren();
  try { client=new RuntimeClient(); const result=await client.verify(text,epoch); if(epoch!==generation)return;report=result;$('results').innerHTML=resultHtml(result);$('status').textContent='Verification finished. Executable results are not fresh kernel certificates.'; }
  catch(error){if(epoch===generation)$('status').textContent='Unknown: '+error.message;}
  finally{ $('verify').disabled=false; }
};
$('results').onclick=event=>{const button=event.target.closest('[data-result]');if(!button||!report)return;const range=report.results[Number(button.dataset.result)]?.range;if(!range)return;selectedRange=range;$('highlight').innerHTML=highlight(source.value,range);let start=0;const lines=source.value.split('\n');for(let i=0;i<range.start.line;i++)start+=(lines[i]?.length||0)+1;source.focus();source.setSelectionRange(start+range.start.character,start+range.start.character);source.scrollTop=range.start.line*22.4;$('highlight').scrollTop=source.scrollTop;};
$('share').onclick=async()=>{try{const hash=await encodeSource(source.value);history.replaceState(null,'',hash);$('status').textContent='Source stored in the URL fragment. Copy this address to share.';}catch(error){$('status').textContent=error.message;}};
async function fromHash(){try{const text=await decodeSource(location.hash);if(text!==null){source.value=text;source.dispatchEvent(new Event('input'));}}catch(error){$('status').textContent='Could not read source link: '+error.message;}}
window.addEventListener('hashchange',fromHash);
try { const config=await (await fetch('examples.json')).json();for(const [i,e] of config.playground.entries()){const o=document.createElement('option');o.value=i;o.textContent=e.title;$('example').append(o);} $('example').onchange=()=>{source.value=config.playground[$('example').value].source;source.dispatchEvent(new Event('input'));};source.value=config.playground[0].source;draw();$('status').textContent='Ready to edit. Verification requires the existing browser runtime deployment.';await fromHash(); }catch(error){$('status').textContent='Unable to load examples: '+error.message;}
if('serviceWorker' in navigator)navigator.serviceWorker.register('./app.js',{type:'module'}).catch(()=>{});
}
if (typeof document === 'undefined' && typeof self !== 'undefined' && 'registration' in self) {
const CACHE='solidity-playground-v2';
const ASSETS=['./','index.html','app.js','style.css','examples.json'];
self.addEventListener('install',event=>event.waitUntil(caches.open(CACHE).then(cache=>cache.addAll(ASSETS)).then(()=>self.skipWaiting())));
self.addEventListener('activate',event=>event.waitUntil(self.clients.claim()));
self.addEventListener('fetch',event=>{if(event.request.method==='GET' && new URL(event.request.url).origin===location.origin)event.respondWith(caches.match(event.request).then(hit=>hit||fetch(event.request)));});

}
