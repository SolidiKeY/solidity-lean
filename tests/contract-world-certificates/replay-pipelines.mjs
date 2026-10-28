import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {createHash} from 'node:crypto';
import {execFileSync} from 'node:child_process';
const root=process.cwd();
const compiler='/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js';
const compilerSha='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390';
const source=join(root,'tests/solc/ContractWorld.sol');
const controls=join(root,'Solidity/Examples/Tactics/ContractWorldSource.lean');
const sha=p=>createHash('sha256').update(readFileSync(p)).digest('hex');
const report={source:'tests/solc/ContractWorld.sol',sourceSha256:sha(source),controlsSha256:sha(controls),compilerSha256:sha(compiler),scope:'Kernel-checked typed-source observations for both analysis pipelines; no EVM/compiler-equivalence claim.',pipelines:[]};
for(const pipeline of ['legacy','viaIR']) {
 const directory=join(root,'.lake/world-certificate-pipelines',pipeline);mkdirSync(directory,{recursive:true});
 const fixture=join(directory,'ContractWorld.ast.json'),wrapper=join(directory,'Controls.lean');
 writeFileSync(wrapper,readFileSync(controls,'utf8').replaceAll('../../../tests/solc/ContractWorld.ast.json','ContractWorld.ast.json'));
 const args=['scripts/solc-ast.mjs','--source',source,'--out',fixture,'--wrapper',wrapper,'--world-metadata','--compiler-file',compiler,'--compiler-sha256',compilerSha,...pipeline==='viaIR'?['--via-ir']:[]];
 const generation=execFileSync(process.execPath,args,{cwd:root,encoding:'utf8',timeout:120000});
 const start=Date.now();
 let output,status='passed';
 try {output=execFileSync('lake',['env','lean','--tstack=131072','-j1',wrapper],{cwd:root,encoding:'utf8',timeout:120000});}
 catch(error){status='blocked-or-failed';output=String(error.stdout||'')+String(error.stderr||'');}
 const elapsedMs=Date.now()-start;
 const log='/workspace/.setup/logs/world-pipeline-'+pipeline+'.log';writeFileSync(log,generation+'\n'+output);
 report.pipelines.push({pipeline,status,elapsedMs,fixtureSha256:sha(fixture),wrapperSha256:sha(wrapper),generationArguments:args,leanArguments:['env','lean','--tstack=131072','-j1',wrapper],log});
 console.log(pipeline,status,elapsedMs+'ms');
 if(status!=='passed') break;
}
writeFileSync('/workspace/.setup/logs/world-pipelines.json',JSON.stringify(report,null,2)+'\n');
if(report.pipelines.length!==2||report.pipelines.some(p=>p.status!=='passed')) process.exitCode=1;
