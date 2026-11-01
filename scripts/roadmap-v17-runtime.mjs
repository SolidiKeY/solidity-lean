#!/usr/bin/env node
// V17 consumer only: the published compiler checker and differential engine own semantics.
import {readFileSync,writeFileSync,readdirSync,lstatSync,realpathSync,readlinkSync,mkdirSync} from 'node:fs';
import {resolve,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {execFileSync} from 'node:child_process';
import {compiler,main as generated} from './evm-reference/generated.mjs';
import {COMPILER_SHA} from './solidity-upstream.mjs';
const ROOT=resolve(dirname(fileURLToPath(import.meta.url)),'..');
export const VERSION='0.8.38+commit.1835d247.Emscripten.clang';
export const CACHE=resolve(ROOT,'.lake/soljson/soljson-v0.8.38+commit.1835d247.js');
const hash=b=>createHash('sha256').update(b).digest('hex');
const sha=p=>hash(readFileSync(p));
const equal=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
function require(ok,message){if(!ok)throw Error(message);}
export function checkCompiler(identity){
 require(identity.sha256===COMPILER_SHA,'wrong approved compiler hash');
 require(identity.version===VERSION,'wrong full compiler version');
 require(identity.bytes===10798266,'wrong approved compiler length');
}
export function sameInputs(before,after){require(equal(before,after),'stale or changed execution inputs');}
export function checkoutStatus(status,actualConfig,expectedConfig){
 require(status===''||status==='?? roadmap-v17-runtime.lakefile.toml','dirty runtime source');
 if(status!=='')require(actualConfig===expectedConfig,'changed serial runtime configuration');
}
export function snapshot(){
 require(lstatSync(CACHE).isFile(),'approved hidden cache is not a regular file');
 const identity={path:CACHE,bytes:lstatSync(CACHE).size,sha256:sha(CACHE),version:VERSION};
 checkCompiler(identity);compiler(CACHE); // Published checker obtains the ACTUAL cwrap version.
 const runtime=resolve(ROOT,'scripts/evm-reference'),files={};
 function walk(dir){for(const name of readdirSync(dir).sort()){
  const path=resolve(dir,name),stat=lstatSync(path);
  if(stat.isSymbolicLink()){const target=realpathSync(path);require(target.startsWith(runtime+'/node_modules/')&&lstatSync(target).isFile(),'external/nonfile runtime symlink');files[path.slice(ROOT.length+1)]={link:readlinkSync(path),target:target.slice(ROOT.length+1),sha256:sha(target)};continue;}
  if(stat.isDirectory())walk(path);else{require(stat.isFile(),'nonregular runtime input');files[path.slice(ROOT.length+1)]=sha(path);}
 }}
 walk(resolve(runtime,'node_modules'));
 const lock=JSON.parse(readFileSync(resolve(runtime,'package-lock.json')));
 for(const [name,pkg] of Object.entries(lock.packages))if(name){
  const actual=JSON.parse(readFileSync(resolve(runtime,name,'package.json')));
  require(actual.version===pkg.version,'installed locked package mismatch: '+name);
 }
 for(const name of ['package.json','package-lock.json','generated.mjs','replay.mjs'])files['scripts/evm-reference/'+name]=sha(resolve(runtime,name));
 for(const name of ['SolCases.lean','Solidity/Tools/SolCases.lean','scripts/solidity-upstream.mjs','scripts/roadmap-v17-runtime.mjs','scripts/roadmap-v17-compare.mjs','lean-toolchain','lakefile.toml','.lake/build/bin/solcases'])files[name]=sha(resolve(ROOT,name));
 const git=args=>execFileSync('git',args,{cwd:ROOT,encoding:'utf8'}).trim();
 const status=git(['status','--porcelain','--untracked-files=all']);
 const config=resolve(ROOT,'roadmap-v17-runtime.lakefile.toml');
 const expectedConfig=readFileSync(resolve(ROOT,'lakefile.toml'),'utf8').replaceAll('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]');
 checkoutStatus(status,status===''?null:readFileSync(config,'utf8'),expectedConfig);
 if(status!=='')files['roadmap-v17-runtime.lakefile.toml']=sha(config);
 return {schema:1,revision:git(['rev-parse','HEAD']),tree:git(['rev-parse','HEAD^{tree}']),compiler:identity,
  node:{path:realpathSync(process.execPath),version:process.version,sha256:sha(process.execPath)},files,
  leanVersion:execFileSync('lean',['--version'],{encoding:'utf8'}).trim(),lakeVersion:execFileSync('lake',['--version'],{encoding:'utf8'}).trim()};
}
export function reportBinding(report,inputs){
 const m=report.metadata;
 require(m.checkoutCommit===inputs.revision,'stale report revision');
 require(m.compiler===inputs.compiler.version&&m.compilerSha256===inputs.compiler.sha256,'wrong report compiler');
 require(m.leanVersion===inputs.leanVersion&&m.lakeVersion===inputs.lakeVersion,'wrong report toolchain');
 require(m.enumerated===160&&m.selected===160&&m.seed===0&&report.records.length===160,'partial original matrix');
 require(equal(report.summary,{agree:640,mismatch:0,blocked:0}),'nonpassing original matrix');
 for(const [key,name] of Object.entries({runnerSha256:'scripts/evm-reference/generated.mjs',replaySha256:'scripts/evm-reference/replay.mjs',lockSha256:'scripts/evm-reference/package-lock.json',generatorBinarySha256:'.lake/build/bin/solcases',driverSha256:'SolCases.lean',generatorSha256:'Solidity/Tools/SolCases.lean'}))require(m[key]===inputs.files[name],'stale report input: '+name);
 require(m.gitDiffSha256===hash(''),'dirty report');
 const settings=[{viaIR:false,optimizer:false},{viaIR:false,optimizer:true},{viaIR:true,optimizer:false},{viaIR:true,optimizer:true}];
 for(const [i,row] of report.records.entries()){
  require(row.record.schema===1&&row.record.index===i&&row.record.seed===0&&Number.isInteger(row.record.kind)&&row.record.kind>=0&&row.record.kind<10,'changed ordered record');
  require(row.variants.length===4,'missing settings');
  for(const [j,actual] of row.variants.entries()){
  for(const code of ['creation','runtime']){require(typeof actual[code+'Code']==='string'&&/^(?:[0-9a-f]{2})+$/.test(actual[code+'Code']),'noncanonical executable bytes');require(hash(Buffer.from(actual[code+'Code'],'hex'))===actual[code+'Sha256'],'corrupt executable observation');}
  require(actual.deployment.runtimeCodeSha256===actual.runtimeSha256,'wrong deployed runtime');
  require(equal(actual.variant,settings[j])&&actual.index===i&&actual.seed===0&&actual.sourceSha256===hash(row.record.source)&&actual.status==='agree'&&equal(actual.expected,row.record.expected),'changed ordered observation identity');
  }
 }

}
export function verifyOutputs(log,out){
 const lines=log.split('\n').filter(line=>line.startsWith('V17_RUNTIME_OUTPUTS '));
 require(lines.length===1,'missing/duplicate native output manifest');
 const manifest=JSON.parse(lines[0].slice('V17_RUNTIME_OUTPUTS '.length));
 const expected=['inputs-after.json','inputs-before.json','report.json','runtime-outcome.json'];
 require(manifest.schema===1&&equal(Object.keys(manifest.files).sort(),expected)&&equal(readdirSync(out).sort(),expected),'missing/extra runtime outputs');
 for(const name of expected)require(lstatSync(out+'/'+name).isFile()&&sha(out+'/'+name)===manifest.files[name],'corrupt native runtime output');
 const outcome=JSON.parse(readFileSync(out+'/runtime-outcome.json'));
 require(outcome.commandExit===0&&outcome.validationExit===0&&outcome.postInputExit===0&&outcome.phaseErrors.length===0,'failed runtime phase');
 require(outcome.reportSha256===manifest.files['report.json'],'unmatched producer report');
 sameInputs(JSON.parse(readFileSync(out+'/inputs-before.json')),JSON.parse(readFileSync(out+'/inputs-after.json')));
 return manifest;
}
async function run(out){
 require(out.startsWith('/workspace/scratch/')&&realpathSync(dirname(out))===dirname(out),'noncanonical/nonexternal runtime output');
 mkdirSync(out); // Refuse ALL existing directories, including sealed evidence.
 const before=snapshot();writeFileSync(out+'/inputs-before.json',JSON.stringify(before,null,2)+'\n');
 let commandExit=null,validationExit=0,postInputExit=0,error=null,reportSha256=null;const phaseErrors=[];
 try{
  commandExit=await generated(['--compiler',CACHE,'--seed','0','--out',out+'/report.json']);
  reportSha256=sha(out+'/report.json');require(commandExit===0,'published differential failed');
  const raw=readFileSync(out+'/report.json'),report=JSON.parse(raw);reportBinding(report,before);
  const enumeration=execFileSync(resolve(ROOT,'.lake/build/bin/solcases'),['0'],{cwd:ROOT,timeout:60000,maxBuffer:16*1024*1024,encoding:'utf8'}).trim().split('\n').map(JSON.parse);
  require(equal(enumeration,report.records.map(r=>r.record)),'changed complete ordered generator replay');
  require(execFileSync(process.execPath,[resolve(ROOT,'scripts/roadmap-v17-compare.mjs')],{input:raw,timeout:60000,maxBuffer:16*1024*1024,encoding:'utf8'})==='V17_COMPARE_PASS\n','observation validation failed');
 }catch(e){validationExit=1;error=String(e);phaseErrors.push({phase:'producer-or-validation',error});}
 finally{
  try{if(reportSha256!==null)require(sha(out+'/report.json')===reportSha256,'changed producer report');const after=snapshot();writeFileSync(out+'/inputs-after.json',JSON.stringify(after,null,2)+'\n');sameInputs(before,after);}catch(e){postInputExit=1;error=String(e);phaseErrors.push({phase:'post-inputs',error});}
  writeFileSync(out+'/runtime-outcome.json',JSON.stringify({commandExit,validationExit,postInputExit,error,phaseErrors,reportSha256,semanticPremisesDischarged:false,releaseClosed:false},null,2)+'\n');
 }
 const manifest={schema:1,files:{}};
 for(const name of readdirSync(out).sort()){require(lstatSync(out+'/'+name).isFile(),'nonfile runtime output');manifest.files[name]=sha(out+'/'+name);}
 console.log('V17_RUNTIME_OUTPUTS '+JSON.stringify(manifest));
 return commandExit===0&&validationExit===0&&postInputExit===0?0:1;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)){
 try{if(process.argv[2]==='snapshot')console.log(JSON.stringify(snapshot(),null,2));
 else if(process.argv[2]==='run'&&process.argv.length===4)process.exitCode=await run(resolve(process.argv[3]));else throw Error('expected snapshot | run EXTERNAL_EXISTING_DIRECTORY');}
 catch(e){console.error(String(e));process.exitCode=2;}
}
