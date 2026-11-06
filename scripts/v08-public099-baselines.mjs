#!/usr/bin/env node
// Complete Git-object finding reconstruction, checked against current RAW gates.
// No checkout/cache copies, no baseline writes, no Lean. Historical lists are
// reconstructed observations, not claims of historical shell invocation.
import {readFileSync,writeFileSync,existsSync} from 'node:fs';
import {execFileSync,spawnSync} from 'node:child_process';
import {resolve,dirname,posix,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {collect,pins,compare} from './check-axiom-pins.mjs';
const root=resolve(dirname(fileURLToPath(import.meta.url)),'..'),out=resolve(process.argv[2]);
const publicBase='099bfbe185731c354b12a40f28ccf5d98534c779',frozen='fb379ae20f10e2c92113453ddd9d40d8f2efbe09';
const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8',maxBuffer:64*1024*1024});
const sha=x=>createHash('sha256').update(x).digest('hex');
const sorted=x=>[...x].sort();
const equal=(a,b)=>JSON.stringify(sorted(a))===JSON.stringify(sorted(b));
function assert(ok,why){if(!ok)throw new Error(why)}
const scriptHashes={};
for(const file of ['scripts/check-doc-paths.sh','scripts/check-axiom-pins.mjs','scripts/check-trust.mjs']){
 const data=readFileSync(join(root,file));scriptHashes[file]=sha(data);
 for(const rev of [publicBase,frozen])assert(sha(git('show',rev+':'+file))===sha(data),'historical checker changed: '+file);
}
function paths(rev){return git(...(rev==='INDEX'?['ls-files']:['ls-tree','-r','--name-only',rev])).trim().split('\n')}
function docFindings(rev){
 const files=paths(rev),all=new Set(files),lean=files.filter(x=>x.endsWith('.lean'));
 const args=['grep','-n','-o','-E',...(rev==='INDEX'?['--cached']:[]),'-e','`[A-Za-z][A-Za-z0-9_/.-]*\\.lean`',...(rev==='INDEX'?[]:[rev]),'--'];
 const p=spawnSync('git',args,{cwd:root,encoding:'utf8',maxBuffer:64*1024*1024});assert([0,1].includes(p.status),'git reference scan failed: '+p.status+' '+p.stderr);
 const refs=new Map();
 for(let line of p.stdout.split('\n')){
  if(rev!=='INDEX'&&line.startsWith(rev+':'))line=line.slice(rev.length+1);
  const match=line.match(/^([^:]+):\d+:`([^`]+)`$/u);if(match)refs.set(match[1]+'\t'+match[2],[match[1],match[2]]);
 }
 const findings=[];
 for(const [source,ref] of [...refs.values()].sort((a,b)=>(a[0]+'\t'+a[1]).localeCompare(b[0]+'\t'+b[1]))){
  if(/^(SolKey\/|EvmYul\/|Decode\/)|PartNN/u.test(ref))continue;
  const candidates=[posix.normalize(posix.join(posix.dirname(source),ref)),'Solidity/'+ref,ref];
  if(candidates.some(p=>all.has(p)))continue;
  // Production grep treats dots as regex wildcards; preserve that behavior.
  const regex=new RegExp('(^|/)'+ref+'$');const hits=lean.filter(x=>regex.test(x)).length;
  if(hits===0)findings.push('missing:   '+source+' cites `'+ref+'`');
  else if(hits>1)findings.push('ambiguous: '+source+' cites `'+ref+'` ('+hits+' files share that name)');
 }
 return sorted(findings);
}
function pinFindings(rev){
 let found;
 if(rev==='INDEX')found=collect(root);
 else{
  found=new Map();
  const files=paths(rev).filter(p=>p.endsWith('.lean')&&/^(Solidity|Bridge|tests)\//u.test(p)&&!p.startsWith('Solidity/Scratch/'));
  for(const file of files)for(const pin of pins(git('show',rev+':'+file)))found.set(file+':'+pin.name,{...pin,file});
 }
 const recorded=rev==='INDEX'?JSON.parse(readFileSync(join(root,'scripts/g07-axiom-pins.json'),'utf8')):JSON.parse(git('show',rev+':scripts/g07-axiom-pins.json'));
 const result=compare(found,recorded);return {found:found.size,errors:sorted(result.errors),notes:sorted(result.notes)};
}
const raw={};
for(const [name,command,args] of [['docs','bash',['scripts/check-doc-paths.sh','--strict']],['pins',process.execPath,['scripts/check-axiom-pins.mjs']]]){
 const p=spawnSync(command,args,{cwd:root,encoding:'utf8',maxBuffer:64*1024*1024});assert(p.status!==null,'raw checker stopped');
 writeFileSync(join(out,'raw-'+name+'.log'),p.stdout+p.stderr);raw[name]={exit:p.status,sha256:sha(p.stdout+p.stderr)};
}
const current={docs:docFindings('INDEX'),pins:pinFindings('INDEX')};
const rawDocs=readFileSync(join(out,'raw-docs.log'),'utf8').split('\n').filter(x=>/^(missing:|ambiguous:)/u.test(x));
const rawPins=readFileSync(join(out,'raw-pins.log'),'utf8').split('\n');
assert(equal(current.docs,rawDocs),'reconstructed current docs differ from raw production output');
assert(equal(current.pins.errors,rawPins.filter(x=>x.startsWith('ERROR  ')).map(x=>x.slice(7))),'current pin errors differ');
assert(equal(current.pins.notes,rawPins.filter(x=>x.startsWith('NOTE   ')).map(x=>x.slice(7))),'current pin notes differ');
const historical={};for(const rev of [publicBase,frozen])historical[rev]={docs:docFindings(rev),pins:pinFindings(rev)};
const pub=historical[publicBase],old=historical[frozen];
const publicEquality=equal(current.docs,pub.docs)&&equal(current.pins.errors,pub.pins.errors)&&equal(current.pins.notes,pub.pins.notes);
const difference=(a,b)=>a.filter(x=>!b.includes(x));
const report={raw,current,historical,scriptHashes,publicBase,frozen,publicEquality,
 frozenDelta:{docsAdded:difference(current.docs,old.docs),docsRemoved:difference(old.docs,current.docs),pinErrorsAdded:difference(current.pins.errors,old.pins.errors),pinNotesAdded:difference(current.pins.notes,old.pins.notes),pinNotesRemoved:difference(old.pins.notes,current.pins.notes)},
 historicalMethod:'complete Git-object findings using byte-identical production scanner/pin functions; current reconstruction independently equals RAW outputs; not historical raw shell invocations'};
writeFileSync(join(out,'baseline-comparison.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({raw,publicEquality,currentDocs:current.docs.length,publicDocs:pub.docs.length,frozenDocs:old.docs.length,currentPinNotes:current.pins.notes.length,publicPinNotes:pub.pins.notes.length,frozenPinNotes:old.pins.notes.length}));
process.exit(publicEquality?0:1);
