import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {resolve,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {blankLean} from './check-trust.mjs';
import {pins} from './check-axiom-pins.mjs';
const STANDARD=new Set(['propext','Classical.choice','Quot.sound']);
export function check(manifest,sources){
  const errors=[];
  for(const [file,want] of Object.entries(manifest.modules)){
    const text=sources[file];
    if(typeof text!=='string'){errors.push(`${file}: missing module`);continue;}
    if(createHash('sha256').update(text).digest('hex')!==want.sha256)errors.push(`${file}: reviewed source mismatch`);
    const clean=blankLean(text);
    if(/\b(sorry|admit|native_decide|implemented_by|axiom|opaque|set_option)\b/.test(clean))errors.push(`${file}: forbidden proof/budget change`);
    const decls=[...clean.matchAll(/^theorem\s+([\w.]+)/gm)].map(x=>x[1]);
    if(JSON.stringify(decls)!==JSON.stringify(want.declarations))errors.push(`${file}: public declarations changed`);
    const found=pins(text),counts=new Map();
    for(const p of found){
      counts.set(p.name,(counts.get(p.name)||0)+1);
      const expected=want.pins[p.name];
      if(!expected||p.target!==p.name.slice(want.namespace.length+1)||JSON.stringify(p.axioms)!==JSON.stringify(expected))errors.push(`${file}: exact pin mismatch ${p.name}`);
      if(!Array.isArray(p.axioms)||p.axioms.some(a=>!STANDARD.has(a)))errors.push(`${file}: unsafe/unknown axioms`);
    }
    for(const n of Object.keys(want.pins))if(counts.get(n)!==1)errors.push(`${file}: missing/duplicate pin ${n}`);
    if(found.length!==Object.keys(want.pins).length)errors.push(`${file}: pin count changed`);
  }
  return errors;
}
export function load(root){
  const manifest=JSON.parse(readFileSync(resolve(root,'tests/p6-memory-interface.json'),'utf8'));
  return {manifest,sources:Object.fromEntries(Object.keys(manifest.modules).map(f=>[f,readFileSync(resolve(root,f),'utf8')]))};
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)){
  const {manifest,sources}=load(resolve(dirname(fileURLToPath(import.meta.url)),'..'));
  const errors=check(manifest,sources);for(const e of errors)console.error(e);
  console.log(`p6-memory: ${Object.keys(sources).length} exact reviewed modules, ${Object.values(manifest.modules).reduce((n,m)=>n+Object.keys(m.pins).length,0)} measured standard-only pins, ${errors.length} errors; structural check complements kernel validation`);
  process.exitCode=errors.length?1:0;
}
