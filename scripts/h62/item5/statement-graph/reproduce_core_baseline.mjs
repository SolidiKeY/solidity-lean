#!/usr/bin/env node
// Guard the authorized107-edge baseline from absorbing later imports or losing attribution.
// This reproduces source imports/history at one Git tree; it is not Lean elaboration.
import {readFileSync,existsSync} from 'node:fs';
import {resolve} from 'node:path';
import {execFileSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import vm from 'node:vm';
import {parseImports,CURRENT_BASELINE_SHA256} from '../../../core-import-closure.mjs';
const REF='fea090bf9fec1a372ad32952a5e72eb4d7015888';
const OLD_SHA='d202b21ddde800b40237b9c4a95482c17b8d5ea8d2c78c1b42e4bad7344ac80b';
const git=(...args)=>execFileSync('git',['--no-replace-objects',...args],{encoding:'utf8',maxBuffer:32*1024*1024,stdio:['ignore','pipe','pipe']});
const sha=s=>createHash('sha256').update(s).digest('hex');
if(process.env.GIT_GRAFT_FILE!==undefined||process.env.GIT_SHALLOW_FILE!==undefined||
   git('rev-parse','--is-shallow-repository').trim()!=='false'||
   existsSync(resolve(git('rev-parse','--git-path','info/grafts').trim())))throw Error('custom/shallow/grafted history refused for attribution');
const oldRaw=readFileSync('scripts/core-import-baseline.json');
if(sha(oldRaw)!==OLD_SHA)throw Error('original95baseline changed');
const old=JSON.parse(oldRaw),oldKeys=new Set(old.map(JSON.stringify));
const checker=git('show',REF+':scripts/check-layers.mjs');
const policy=vm.runInNewContext(checker.slice(checker.indexOf('const CORE ='),checker.indexOf('const PARSER_ADAPTER'))+';({CORE,ELABORATOR})');
const core=m=>policy.CORE.some(r=>r.test(m))&&!policy.ELABORATOR.some(r=>r.test(m));
const paths=git('ls-tree','-r','--name-only',REF,'--','Solidity').trim().split('\n').filter(p=>p.endsWith('.lean')&&!p.startsWith('Solidity/Scratch/'));
const edges=[];
for(const path of paths){const from=path.slice(0,-5).replaceAll('/','.');if(!core(from))continue;
 for(const to of parseImports(git('show',REF+':'+path)))if((to==='Solidity'||to.startsWith('Solidity.'))&&!core(to))edges.push([from,to]);}
const all=[...new Set(edges.map(JSON.stringify))].sort().map(JSON.parse);
const additions=all.filter(e=>!oldKeys.has(JSON.stringify(e))).map(([source,target])=>{
 const file=source.replaceAll('.','/')+'.lean',text=git('show',REF+':'+file);
 const lines=text.split('\n').flatMap((line,i)=>line.startsWith('import ')&&line.split(/\s+/).slice(1).includes(target)?[i+1]:[]);
 if(lines.length!==1)throw Error('ambiguous import attribution');
 const blame=git('blame','--line-porcelain','-L',`${lines[0]},${lines[0]}`,REF,'--',file).split('\n');
 const commit=blame[0].split(' ')[0],originFile=blame.find(s=>s.startsWith('filename ')).slice(9);
 const parents=git('rev-list','--parents','-n','1',commit).trim().split(' ').slice(1);
 for(const parent of parents){let previous='';try{previous=git('show',parent+':'+originFile);}catch(error){if(git('ls-tree',parent,'--',originFile).trim())throw error;}
  if(parseImports(previous).includes(target))throw Error('blame is not introducing commit');}
 const initial=git('show','1d99e32a08271752468b027a5495233c77a66f91:'+file);
 return {source,target,file,line:lines[0],fileSha256:sha(text),introducingCommit:commit,
  introducingSubject:git('show','-s','--format=%s',commit).trim(),originFile,
  absentFromAllIntroducingParents:true,presentAtInitialPinParent:parseImports(initial).includes(target)};
});
if(all.length!==107||additions.length!==12||old.some(e=>!all.some(x=>JSON.stringify(x)===JSON.stringify(e))))throw Error('authorized107/12census mismatch');
const output=JSON.stringify({schema:1,sourceCommit:REF,previousBaselineSha256:OLD_SHA,
 authorization:'OT-W0-TOOLING coordinator follow-up, 2026-11-07',edges:all,additions},null,2)+'\n';
if(sha(output)!==CURRENT_BASELINE_SHA256)throw Error('reproduced107baseline SHA256 mismatch');
process.stdout.write(output);
