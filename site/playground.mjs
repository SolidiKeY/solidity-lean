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
