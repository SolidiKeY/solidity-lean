import {encodeSource,decodeSource,resultHtml,highlight} from './playground.mjs';
import {RuntimeClient} from './runtime-client.mjs';
const $=id=>document.getElementById(id), source=$('source'); let report=null, generation=0,client;
const draw=()=>{$('highlight').innerHTML=highlight(source.value);$('highlight').scrollTop=source.scrollTop;$('highlight').scrollLeft=source.scrollLeft;};
source.addEventListener('input',()=>{generation++;client?.close();client=null;report=null;$('results').textContent='Source changed; verify to refresh results.';draw();});
source.addEventListener('scroll',draw);
$('verify').onclick=async()=>{
  const epoch=++generation,text=source.value; client?.close(); client=new RuntimeClient();
  $('status').textContent='Preparing browser compiler and verifier…';$('verify').disabled=true;$('results').replaceChildren();
  try { const result=await client.verify(text,epoch); if(epoch!==generation)return;report=result;$('results').innerHTML=resultHtml(result);$('status').textContent='Verification finished. Executable results are not fresh kernel certificates.'; }
  catch(error){if(epoch===generation)$('status').textContent='Unknown: '+error.message;}
  finally{ $('verify').disabled=false; }
};
$('results').onclick=event=>{const button=event.target.closest('[data-result]');if(!button||!report)return;const range=report.results[Number(button.dataset.result)]?.range;if(!range)return;$('highlight').innerHTML=highlight(source.value,range);let start=0;const lines=source.value.split('\n');for(let i=0;i<range.start.line;i++)start+=(lines[i]?.length||0)+1;source.focus();source.setSelectionRange(start+range.start.character,start+range.start.character);source.scrollTop=range.start.line*22.4;$('highlight').scrollTop=source.scrollTop;};
$('share').onclick=async()=>{try{const hash=await encodeSource(source.value);history.replaceState(null,'',hash);$('status').textContent='Source stored in the URL fragment. Copy this address to share.';}catch(error){$('status').textContent=error.message;}};
async function fromHash(){try{const text=await decodeSource(location.hash);if(text!==null){source.value=text;generation++;report=null;$('results').replaceChildren();draw();}}catch(error){$('status').textContent='Could not read source link: '+error.message;}}
window.addEventListener('hashchange',fromHash);
try { const config=await (await fetch('examples.json')).json();for(const [i,e] of config.playground.entries()){const o=document.createElement('option');o.value=i;o.textContent=e.title;$('example').append(o);} $('example').onchange=()=>{source.value=config.playground[$('example').value].source;source.dispatchEvent(new Event('input'));};source.value=config.playground[0].source;draw();$('status').textContent='Ready to edit. Verification requires the existing browser runtime deployment.';await fromHash(); }catch(error){$('status').textContent='Unable to load examples: '+error.message;}
if('serviceWorker' in navigator)navigator.serviceWorker.register('./sw.js').catch(()=>{});
