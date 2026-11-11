#!/usr/bin/env node
// Measures kernel declaration dependencies, not import reachability or proof size.
import {readFileSync, writeFileSync, existsSync} from 'node:fs';
import {execFileSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {pathToFileURL} from 'node:url';
import {join} from 'node:path';
import {blankLean} from '../check-trust.mjs';
import {freshArtifactGraph,currentIleanPaths} from './trust-artifacts.mjs';
export {configuredCacheDir} from './trust-artifacts.mjs';
const baselinePath='scripts/trust/trust-closure-baseline.json';
export const sha = s => createHash('sha256').update(s).digest('hex');

// check-trust's lexer intentionally keeps literal contents for safety linting.
// This range parser instead masks literal tokens, preserving offsets/newlines.
// Unsupported interpolated strings fail closed rather than inventing a boundary.
function maskLiterals(source) {
 const out=source.split('');
 const mask=(a,b)=>{for(let k=a;k<b;k++)if(out[k]!=='\n')out[k]='x';};
 for(let i=0;i<source.length;i++) {
  if(source.startsWith('--',i)){const end=source.indexOf('\n',i);i=end<0?source.length:end;continue;}
  if(source.startsWith('/-',i)){
   let nesting=1,j=i+2;
   while(j<source.length&&nesting){if(source.startsWith('/-',j)){nesting++;j+=2;}else if(source.startsWith('-/',j)){nesting--;j+=2;}else j++;}
   if(nesting)throw Error('unterminated comment');i=j-1;continue;
  }
  if(source[i]==='«') {const end=source.indexOf('»',i+1);if(end<0)throw Error('unterminated identifier');mask(i,end+1);i=end;continue;}
  const char=source.slice(i).match(/^'(?:\\.|[^\\'\n])'/u);
  if(char){mask(i,i+char[0].length);i+=char[0].length-1;continue;}
  const raw=source.slice(i).match(/^r(#+)?"/u);
  if(raw){const delim='"'+(raw[1]??'');const end=source.indexOf(delim,i+raw[0].length);if(end<0)throw Error('unterminated raw string');mask(i,end+delim.length);i=end+delim.length-1;continue;}
  if(source[i]!== '"')continue;
  if(source[i-1]==='!')throw Error('interpolated source string needs precise range support');
  let end=i+1;
  for(;end<source.length;end++){if(source[end]==='\\'){end++;continue;}if(source[end]==='"')break;}
  if(end>=source.length)throw Error('unterminated string');
  mask(i,end+1);i=end;
 }
 return out.join('');
}

// Return statement lines only. Ignore := inside binders and let expressions.
export function statementEnd(source, start, end) {
  const lines=source.split('\n');
  if (!Number.isInteger(start)||!Number.isInteger(end)||start<1||end<start||end>lines.length)
    throw Error('missing or invalid declaration source range');
  const text=blankLean(maskLiterals(lines.slice(start-1,end).join('\n')));
  let header=text.trimStart();
  while(header.startsWith('@[')) {
    let nesting=1,j=2;
    for(;j<header.length&&nesting;j++){if(header[j]==='[')nesting++;else if(header[j]===']')nesting--;}
    if(nesting)throw Error('incomplete source attribute');
    header=header.slice(j).trimStart();
  }
  header=header.replace(/^(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*/u,'');
  // A generated projection/recursor can point at its field or inductive source,
  // neither of which contains an independent theorem proof body.
  if(/^(?:inductive|structure|class|deriving)\b/u.test(header)||
    /^(?!(?:theorem|lemma|def|opaque|example|instance|abbrev)\b)[\p{L}_][\p{L}\p{N}_.'?]*\s*(?::|[({\[])/u.test(header))return end;
  // An inline equation on a one-line theorem has the same physical line
  // count regardless of where its proof begins; no multi-line type is truncated.
  if(start===end && /^(?:theorem|lemma)\b/u.test(header) && /(?<!\|)\|(?!\|).*=>/u.test(header))return end;
  let depth=0, lets=0, typeMatch=false;
  const tokens=/\blet\b|\bmatch\b|\bwhere\b|:=|\n[ \t]*\|(?!\|)|[()\[\]{}]/gu;
  for (const m of text.matchAll(tokens)) {
    const t=m[0].trim();
    if ('([{'.includes(t)) depth++;
    else if (')]}'.includes(t)) depth--;
    else if (!depth && t==='let') lets++;
    else if (!depth && t==='match') typeMatch=true;
    else if (!depth && (t===':='||t==='|'||t==='where')) {
      if(t==='|' && typeMatch)continue;
      if (lets && t===':=') {lets--; continue;}
      return start+text.slice(0,m.index).trimEnd().split('\n').length-1;
    }
  }
  // Projection/constructor source ranges already are declarations of fields,
  // with no source proof body. Generated recursors inherit their inductive span.
  const trimmed=text.trimStart();
  if (/^(?:(?:private|protected)\s+)*(?:inductive|structure|class)\b/u.test(trimmed)||
      /^[\p{L}_][\p{L}\p{N}_.'?]*\s*:/u.test(trimmed))return end;
  throw Error('theorem proof boundary not found');
}
function checkedStatementEnd(source,start,end,name) {
 try{return statementEnd(source,start,end);}catch(error){
  throw Error(`${name} (${start}..${end}): ${error.message}`);
 }
}
export function summarize(raw, sourceFor, {sourceCeilings=false, proofRangesFor=()=>new Map()}={}) {
  if(raw.schema!==1||!Array.isArray(raw.roots)||!raw.roots.length||!raw.declarations.length)
    throw Error('empty/invalid closure');
  const modules=new Map(), names=new Set(), fallbacks=[];
  const declarations=raw.declarations.map(row=>{
    if(names.has(row.name)) throw Error('duplicate declaration');
    names.add(row.name);
    const source=sourceFor(row.module);
    const mod=modules.get(row.module)??{module:row.module,declarations:0,lines:new Set(),trustedDefinitionLines:new Set(),ceiling:false};
    mod.declarations++;
    modules.set(row.module,mod);
    if(row.start===null||row.end===null) {
      if(!sourceCeilings)throw Error(`missing source range: ${row.name}`);
      mod.ceiling=true;
      if(!row.theorem && row.sourceOwner && row.sourceOwner!=='[anonymous]') {
        if(!Number.isInteger(row.ownerStart)||!Number.isInteger(row.ownerEnd))
          throw Error(`executable fallback lacks owner provenance: ${row.name}`);
        const ownerEnd=checkedStatementEnd(source,row.ownerStart,row.ownerEnd,row.sourceOwner);
        if(ownerEnd<row.ownerEnd)throw Error(`executable fallback inside a proof needs precise attribution: ${row.name}`);
        for(let line=row.ownerStart;line<=row.ownerEnd;line++)mod.trustedDefinitionLines.add(line);
      }
      fallbacks.push({name:row.name,module:row.module,sourceOwner:row.sourceOwner??null,
        ownerStart:row.ownerStart??null,ownerEnd:row.ownerEnd??null,
        reason:'generated declaration without a precise source range'});
      return row;
    }
    if(row.statementOnly && !row.theorem)throw Error(`non-proof declaration needs precise source ownership: ${row.name}`);
    const end=(row.statementOnly??row.theorem)?checkedStatementEnd(source,row.start,row.end,row.name):row.end;
    if(!Number.isInteger(row.start)||!Number.isInteger(end)||row.start<1||end<row.start||end>source.split('\n').length)
      throw Error(`invalid source range: ${row.name}`);
    for(let line=row.start;line<=end;line++){mod.lines.add(line);if(!row.theorem)mod.trustedDefinitionLines.add(line);}
    return {...row,end};
  }).sort((a,b)=>a.name.localeCompare(b.name));
  for(const root of raw.roots)if(!names.has(root))throw Error(`root missing from closure: ${root}`);
  const ceilings=[];
  for(const mod of modules.values()) {
    if(!mod.ceiling)continue;
    if(!Array.isArray(raw.ceilingProofs))throw Error('source ceiling lacks complete proof inventory');
    const source=sourceFor(mod.module), lines=source.split('\n'), cleanSource=blankLean(source);
    const physicalLines=lines.length-(lines.at(-1)===''?1:0);
    const excluded=new Set(), exclusions=[], generatedProofs=[];
    const index=proofRangesFor(mod.module);
    for(const proof of raw.ceilingProofs.filter(p=>p.module===mod.module)) {
      const prefix='_private.'+mod.module+'.';
      let visible=proof.name;
      if(visible.startsWith(prefix)){const rest=visible.slice(prefix.length);visible=rest.slice(rest.indexOf('.')+1);}
      const span=proof.start!==null&&proof.end!==null?proof:index.get(visible);
      if(!span){
        // A generated proof has no independent source body. A written theorem
        // or proof definition must have a kernel range or compiled source span.
        const suffixes=visible.split('.').map((_,i)=>visible.split('.').slice(i).join('.'));
        const escaped=s=>s.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
        if(suffixes.some(n=>new RegExp('\\b(?:theorem|lemma|def|opaque)\\s+'+escaped(n)+'(?=\\s|[:({])','u').test(cleanSource)))
          throw Error(`written proof lacks a source exclusion span: ${proof.name}`);
        generatedProofs.push(proof.name);continue;
      }
      const end=checkedStatementEnd(source,span.start,span.end,proof.name);
      for(let line=end+1;line<=span.end;line++)excluded.add(line);
      exclusions.push({name:proof.name,start:span.start,statementEnd:end,end:span.end});
    }
    const candidateProofLines=excluded.size, retainedTrustedDefinitionLines=[];
    for(const line of mod.trustedDefinitionLines)if(excluded.delete(line))retainedTrustedDefinitionLines.push(line);
    mod.lines=new Set();
    for(let line=1;line<=physicalLines;line++)if(!excluded.has(line))mod.lines.add(line);
    ceilings.push({module:mod.module,physicalLines,candidateProofLines,excludedProofLines:excluded.size,
      retainedTrustedDefinitionLines:retainedTrustedDefinitionLines.sort((a,b)=>a-b),
      proofExclusions:exclusions.sort((a,b)=>a.name.localeCompare(b.name)),
      generatedProofsWithoutIndependentSource:generatedProofs.sort()});
  }
  const counts=[...modules.values()].map(m=>({module:m.module,declarations:m.declarations,
    lines:m.lines.size,sourceCeiling:m.ceiling})).sort((a,b)=>a.module.localeCompare(b.module));
  return {schema:1,roots:[...raw.roots].sort(),declarations,modules:counts,
    sourceLineMetric:sourceCeilings?'H420 conservative upper bound: unresolved modules minus theorem proof bodies':'declaration source spans',
    fallbacks:fallbacks.sort((a,b)=>a.name.localeCompare(b.name)),ceilings:ceilings.sort((a,b)=>a.module.localeCompare(b.module)),
    totalDeclarations:declarations.length,totalLines:counts.reduce((n,m)=>n+m.lines,0)};
}
export function compare(current, baseline) {
  for(const n of baseline.roots)if(!current.roots.includes(n))throw Error(`lost public root: ${n}`);
  const old=new Set(baseline.declarations.map(d=>typeof d==='string'?d:d.name));
  for(const d of current.declarations){const name=typeof d==='string'?d:d.name;
    if(!old.has(name))throw Error(`unrecorded closure growth: ${name}`);}
  const mods=new Map(baseline.modules.map(m=>[m.module,m]));
  for(const m of current.modules)if(!mods.has(m.module)||m.lines>mods.get(m.module).lines)
    throw Error(`unrecorded source-line growth: ${m.module}`);
  for(const n of current.roots)if(!baseline.roots.includes(n))throw Error(`unrecorded public root: ${n}`);
}
export function extract(script, marker) {
  // lake env lean alone can inspect stale objects after a same-line twin change.
  const targets=[...readFileSync(script,'utf8').matchAll(/^import (Solidity(?:\.[A-Za-z0-9_]+)*)$/gm)].map(m=>m[1]);
  if(!targets.length)throw Error('extractor has no tracked Solidity import target');
  execFileSync('lake',['build',...targets],{stdio:['ignore','inherit','inherit'],timeout:3600000,
    env:{...process.env,LEAN_NUM_THREADS:'1'}});
  let output;
  try {output=execFileSync('lake',['lean',script,'--','--tstack=131072'],
    {encoding:'utf8',timeout:300000,maxBuffer:64*1024*1024,env:{...process.env,LEAN_NUM_THREADS:'1'}});}
  catch(error){if(error.stdout)process.stderr.write(error.stdout);if(error.stderr)process.stderr.write(error.stderr);throw error;}
  const rows=output.split('\n').filter(l=>l.startsWith(marker));
  if(rows.length!==1)throw Error('missing or duplicate extractor result');
  return JSON.parse(rows[0].slice(marker.length));
}
export function validateRevision(next, previousText) {
  const previous=JSON.parse(previousText);
  let growth=false;
  try {compare(next,previous);} catch(e) {
    if(e.message.startsWith('lost public root'))throw e;
    growth=true;
  }
  if(growth && (next.change?.previousSha256!==sha(previousText)||
      !next.change?.reason?.trim()||next.change.reason===previous.change?.reason))
    throw Error('baseline growth requires a fresh reason and exact predecessor checksum');
}
// CI must supply the event's actual predecessor, not the updated remote tip.
// Locally retain branch merge-base selection, but never compare HEAD to itself.
export function historyBase({env=process.env,git=(...args)=>execFileSync('git',args,
    {encoding:'utf8',stdio:['ignore','pipe','pipe']}).trim()}={}) {
  const explicit=env.TRUST_BASE_REF;
  if(['push','pull_request','pull_request_target'].includes(env.GITHUB_EVENT_NAME)&&!explicit)
    throw Error('CI closure history needs TRUST_BASE_REF from push.before or pull_request.base.sha');
  if(explicit && /^0+$/u.test(explicit))throw Error('closure predecessor is unavailable (zero event SHA)');
  const head=git('rev-parse','HEAD');
  let base=explicit?git('rev-parse','--verify',`${explicit}^{commit}`):git('merge-base','HEAD','origin/master');
  if(base===head) {
    if(explicit)throw Error('closure history cannot compare HEAD with itself');
    const parents=git('rev-list','--first-parent','--max-count=2','HEAD').split('\n');
    base=parents.length>1?parents[1]:null;
  }
  if(base)git('merge-base','--is-ancestor',base,'HEAD');
  return base;
}
export function checkHistory(baseline,{env=process.env,git=(...args)=>execFileSync('git',args,
    {encoding:'utf8',stdio:['ignore','pipe','pipe']}).trim()}={}) {
  const base=historyBase({env,git});
  // Validate every changed snapshot after the event anchor, including initial
  // adoption and multi-commit PRs. A final HEAD snapshot is never its own anchor.
  let previous=base && git('ls-tree',base,'--',baselinePath)?
    execFileSync('git',['show',`${base}:${baselinePath}`],{encoding:'utf8'}):null;
  const range=base?`${base}..HEAD`:'HEAD';
  const revisions=git('rev-list','--reverse','--topo-order',range,'--',baselinePath).split('\n').filter(Boolean);
  for(const revision of revisions) {
    if(!git('ls-tree',revision,'--',baselinePath))throw Error('baseline history deleted its source');
    const text=execFileSync('git',['show',`${revision}:${baselinePath}`],{encoding:'utf8'});
    if(text===previous)continue;
    const next=JSON.parse(text);
    if(previous===null) {
      if(next.change?.previousSha256!==null || !next.change?.reason?.trim())
        throw Error('initial baseline must have a reason and null predecessor');
    } else validateRevision(next,previous);
    previous=text;
  }
  if(previous!==null)validateRevision(baseline,previous);
  else if(baseline.change?.previousSha256!==null)
    throw Error('initial baseline must have a null predecessor');
}
// The selected OLean graph and its cache mapping identify the source index.
// Neither a physical .ilean nor its physical .trace is a freshness witness.
export function sourceIndex(toolchain,m,{indexPaths=new Map()}={}) {
    const rel=m.replaceAll('.','/')+'.ilean';
    const path=indexPaths.get(m)??`${toolchain}/lib/lean/${rel}`;
    if((m==='Solidity'||m.startsWith('Solidity.'))&&!indexPaths.has(m))throw Error(`current source index not resolved: ${m}`);
    if(!existsSync(path))throw Error(`current compiled source index unavailable: ${m}`);
    const index=JSON.parse(readFileSync(path,'utf8')), spans=new Map();
    for(const ref of Object.values(index.references??{}))for(const u of ref.usages??[]) {
      if(u.length<9||typeof u[4]!=='string')continue;
      const span={start:u[5]+1,end:u[7]+(u[8]===0?0:1)};
      const old=spans.get(u[4]);
      if(old&&(old.start!==span.start||old.end!==span.end))throw Error(`ambiguous source span: ${u[4]}`);
      spans.set(u[4],span);
    }
    return spans;
}
export function committedBaseline() {
 const git=(...args)=>execFileSync('git',args,{encoding:'utf8',stdio:['ignore','pipe','pipe']}).trim();
 const base=process.env.TRUST_BASE_REF?git('rev-parse','--verify',`${process.env.TRUST_BASE_REF}^{commit}`):git('merge-base','HEAD','origin/master');
 for(const rev of ['HEAD',base])if(git('ls-tree',rev,'--',baselinePath))
   return execFileSync('git',['show',`${rev}:${baselinePath}`],{encoding:'utf8'});
 return null;
}
function main() {
  const allArgs=process.argv.slice(2), sourceCeilings=allArgs.includes('--source-ceilings');
  const args=allArgs.filter(a=>a!=='--source-ceilings'), writing=args[0]==='--write';
  if(args.length && (!writing||args.length!==3||args[1]!=='--reason'||!args[2].trim()))
    throw Error('usage: trust-closure.mjs [--source-ceilings] [--write --reason REASON]');
  const baseline=writing?null:JSON.parse(readFileSync(baselinePath,'utf8'));
  if(baseline) {
    if(!baseline.change?.reason?.trim())throw Error('baseline needs a recorded reason');
    checkHistory(baseline);
  }
  const toolchain=execFileSync('lean',['--print-prefix'],{encoding:'utf8'}).trim();
  const sourceCache=new Map();
  const metadata=extract('scripts/trust/trust-closure.lean','TRUST_CLOSURE_JSON=');
  const modules=[...new Set(metadata.declarations.map(d=>d.module).filter(m=>m==='Solidity'||m?.startsWith('Solidity.')))];
  const graph=freshArtifactGraph('Solidity.Theorems');
  const indexPaths=currentIleanPaths(graph.imports,modules);
  const current=summarize(metadata,m=>{
    const rel=m.replaceAll('.','/')+'.lean';
    const path=existsSync(rel)?rel:`${toolchain}/src/lean/${rel}`;
    if(!existsSync(path))throw Error(`source unavailable: ${m}`);
    if(!sourceCache.has(m))sourceCache.set(m,readFileSync(path,'utf8'));
    return sourceCache.get(m);
  },{sourceCeilings,proofRangesFor:m=>{
    return sourceIndex(toolchain,m,{indexPaths});
  }});
  if(writing){
    const old=committedBaseline();
    if(old)for(const n of JSON.parse(old).roots)if(!current.roots.includes(n))throw Error(`cannot delete root: ${n}`);
    writeFileSync(baselinePath,JSON.stringify({...current,declarations:current.declarations.map(d=>d.name),change:{reason:args[2],previousSha256:old?sha(old):null}},null,2)+'\n');
  } else {
    compare(current,baseline);
  }
  console.log(JSON.stringify({roots:current.roots.length,declarations:current.totalDeclarations,lines:current.totalLines,modules:current.modules,sourceLineMetric:current.sourceLineMetric,fallbacks:current.fallbacks,ceilings:current.ceilings.map(c=>({module:c.module,physicalLines:c.physicalLines,excludedProofLines:c.excludedProofLines,generatedProofs:c.generatedProofsWithoutIndependentSource.length}))}));
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)try{main();}catch(e){console.error(e.message);process.exitCode=1;}
