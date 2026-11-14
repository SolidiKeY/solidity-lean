#!/usr/bin/env node
/** Build the existing pure generated-C closure with exact toolchain/source pins. */
import {existsSync,mkdirSync} from 'node:fs';
import {resolve,dirname,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {execFileSync} from 'node:child_process';
const root=resolve(dirname(fileURLToPath(import.meta.url)),'..');
const commit='797c613eb9b6d4ec95db23e3e00af9ac6657f24b';
const run=(command,args,options={})=>execFileSync(command,args,{cwd:root,stdio:'inherit',...options});
try {
  if(process.argv.length>2) throw new Error('verify-build takes no arguments; set VERIFY_LEAN_SOURCE to reuse a pinned checkout');
  const prefix=execFileSync('lean',['--print-prefix'],{encoding:'utf8'}).trim();
  const actual=execFileSync(join(prefix,'bin/lean'),['--githash'],{encoding:'utf8'}).trim();
  if(actual!==commit) throw new Error('verify requires the repository-pinned Lean toolchain');
  const source=resolve(process.env.VERIFY_LEAN_SOURCE??join(root,'.lake/verify/lean-source'));
  if(!existsSync(source)) {
    mkdirSync(source,{recursive:true});
    run('git',['init',source]);
    run('git',['-C',source,'fetch','--depth','1','https://github.com/leanprover/lean4.git',commit]);
    run('git',['-C',source,'checkout','--detach','FETCH_HEAD']);
  }
  const head=execFileSync('git',['-C',source,'rev-parse','HEAD'],{encoding:'utf8'}).trim();
  if(execFileSync('git',['-C',source,'status','--porcelain'],{encoding:'utf8'}).trim()) throw new Error('pinned Lean source checkout has local changes');
  if(head!==commit) throw new Error('VERIFY_LEAN_SOURCE is not the pinned Lean source revision');
  run('python3',['scripts/build-direct-native.py',prefix,source,join(root,'.lake/direct-native')],
    {env:{...process.env,LEAN_NUM_THREADS:'1'}});
} catch(error) {console.error('verify-build: '+error.message);process.exitCode=2;}
