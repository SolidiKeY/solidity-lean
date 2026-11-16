#!/usr/bin/env node
// Every explicit source attribute is reconciled globally. Compiler-generated
// bridges reached by those imports are additionally inventoried, not a complete
// census of all compiler output. No recorded missing link is exempted.
import {readFileSync,writeFileSync,readdirSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
import {blankLean} from '../check-trust.mjs';
import {extract} from './trust-closure.mjs';
const baselinePath='scripts/trust/trust-implemented-by-baseline.json';
export function sourceAttributes(root='Solidity') {
 const out=[];
 function walk(path){for(const e of readdirSync(path,{withFileTypes:true})){
  const file=path+'/'+e.name;
  if(e.isDirectory())walk(file);
  else if(file.endsWith('.lean')){
   const text=blankLean(readFileSync(file,'utf8'));
   // Conservative token census cannot miss an escape behind another
   // attribute's nested brackets. Unexpected literal tokens fail reconciliation.
   for(const a of text.matchAll(/\b(implemented_by|extern)\b/gu))
    out.push({file,module:file.slice(0,-5).replaceAll('/','.'),line:text.slice(0,a.index).split('\n').length,kind:a[1]});
   // Non-inline attributes must not bypass the source/environment reconciliation.
   if(/\battribute\s*\[[^\]]*\b(?:implemented_by|extern)\b/su.test(text))throw Error(`non-inline escape attribute requires inventory support: ${file}`);
  }
 }}walk(root);return out.sort((a,b)=>a.file.localeCompare(b.file)||a.line-b.line);
}
export function reconcile(rows,source) {
 if(!rows.length||!source.length)throw Error('empty escape-hatch inventory');
 const names=new Set();
 for(const row of rows){
  if(names.has(row.declaration))throw Error('duplicate escape declaration');
  names.add(row.declaration);
  if(!Array.isArray(row.links))throw Error('invalid link evidence');
  row.links.sort();
  // Lean 4.24 elabUnsafe (Lean/Elab/BuiltinNotation.lean) creates safe opaque
  // unsafe_impl_N -> unsafe_N bridges without a source attribute. Inventory
  // them too; this provenance label never excuses a missing logical link.
  const generated=row.declaration.match(/^(.*)\.unsafe_impl_\d+$/u);
  row.compilerGenerated=!!(generated&&row.opaque&&!row.unsafe&&row.implementationUnsafe&&
    new RegExp('^'+generated[1].replace(/[.*+?^${}()|[\]\\]/g,'\\$&')+'\\.unsafe_\\d+$','u').test(row.implementation??''));
 }
 for(const module of new Set([...source.map(s=>s.module),...rows.map(r=>r.module)])){
  for(const kind of ['implemented_by','extern']){
   const expected=source.filter(s=>s.module===module&&s.kind===kind).length;
   const actual=rows.filter(r=>r.module===module&&!r.compilerGenerated&&(kind==='extern'?r.extern:r.implementation!==null)).length;
   if(actual!==expected)throw Error(`source/environment mismatch ${module} ${kind}: ${expected} source, ${actual} compiled`);
  }
 }
 return rows.sort((a,b)=>a.declaration.localeCompare(b.declaration));
}
export function requireLinks(rows){
 const missing=rows.filter(r=>!r.links.length||r.extern);
 if(missing.length)throw Error(`${missing.length} missing kernel equality links:\n`+missing.map(r=>`${r.module}: ${r.declaration} -> ${r.implementation??'extern'}: missing`).join('\n'));
}
function main(){
 const args=process.argv.slice(2);
 if(args.length&&!(args.length===1&&args[0]==='--write'))throw Error('usage: trust-implemented-by.mjs [--write]');
 const source=sourceAttributes();
 const rows=reconcile(extract('scripts/trust/trust-implemented-by.lean','TRUST_IMPLEMENTED_BY_JSON='),source);
 const current={schema:1,source,rows};
 if(args[0]==='--write')writeFileSync(baselinePath,JSON.stringify(current,null,2)+'\n');
 else {
  const b=JSON.parse(readFileSync(baselinePath,'utf8'));
  if(JSON.stringify(current)!==JSON.stringify(b))throw Error('escape-hatch baseline drift; regenerate inventory and review link changes');
 }
 console.log(`source-attributes: ${source.length}; imported-kernel-sites: ${rows.length}; observed-generated: ${rows.filter(r=>r.compilerGenerated).length}; linked: ${rows.filter(r=>r.links.length&&!r.extern).length}; missing: ${rows.filter(r=>!r.links.length||r.extern).length}`);
 requireLinks(rows);
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)try{main();}catch(e){console.error(e.message);process.exitCode=1;}
