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
    const token=/\/\*|\*\/|\/\/.*$|"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'|\b(?:pragma|solidity|contract|function|returns|return|public|external|internal|private|pure|view|uint\d*|int\d*|bool|if|else|require|assert|mapping|while|for)\b/g;
    for(const m of line.matchAll(token)) { out+=escapeHtml(line.slice(at,m.index)); const s=m[0]; let cls=block?'comment':s.startsWith('//')||s==='/*'?'comment':s.startsWith('"')||s.startsWith("'")?'string':'kw'; if(s==='/*') block=true; out+=`<span class="${cls}">${escapeHtml(s)}</span>`; if(s==='*/') block=false; at=m.index+s.length; }
    out+=escapeHtml(line.slice(at));
    const marked=range && i>=range.start.line && i<=range.end.line-(range.end.line>range.start.line && range.end.character===0?1:0);
    return `<span class="line${marked?' marked':''}"><span class="no">${i+1}</span>${out || ' '}</span>`;
  }).join('');
}
