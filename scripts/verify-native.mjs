/** Compiled-only adapter. There is deliberately no interpreted fallback. */
import {readFileSync, writeFileSync, mkdirSync} from 'node:fs';
import {resolve, join, dirname, basename} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
import {performance} from 'node:perf_hooks';
import {solidityFiles, runTool, runSolidityTests} from './test-solidity.mjs';
import {compileSnapshot} from './verify-source.mjs';
import {sourceHash, sourceLocations, sourceWitness} from './source-locations.mjs';
const root=resolve(dirname(fileURLToPath(import.meta.url)), '..');
const sha=path=>createHash('sha256').update(readFileSync(path)).digest('hex');

export function nativeBuild(directory) {
  const manifestPath=join(directory,'build.json');
  const manifest=JSON.parse(readFileSync(manifestPath,'utf8'));
  const executable=join(directory,'direct-check');
  if (manifest.version!==2 || manifest.platform!==process.platform || manifest.arch!==process.arch.replace('x64','x86_64')
      || manifest.toolchain!==readFileSync(join(root,'lean-toolchain'),'utf8').trim()
      || manifest.leanCommit!=='797c613eb9b6d4ec95db23e3e00af9ac6657f24b'
      || !Array.isArray(manifest.sourceFiles) || !manifest.sourceFiles.length)
    throw new Error('native build identity mismatch; rebuild with scripts/verify-build');
  if (sha(executable)!==manifest.executable) throw new Error('native executable changed; rebuild with scripts/verify-build');
  if (sha(join(root,'web/browser/direct-bridge.c'))!==manifest.bridgeSha256
      || sha(join(root,'scripts/direct-runtime-closure.py'))!==manifest.closureScriptSha256)
    throw new Error('native bridge or closure builder changed; rebuild with scripts/verify-build');
  for(const relative of ['scripts/verify-build.py','scripts/direct-runtime-closure.py','web/browser/direct-bridge.c','lean-toolchain','lakefile.toml']) {
    const path=join(root,relative);
    if(manifest.buildInputs?.[path]!==sha(path)) throw new Error('native build input changed: '+relative);
  }
  const key=basename(resolve(directory)), module='VerifyInput'+key;
  const inputDirectory=join(root,'.lake/verify/inputs',key);
  if(!/^[a-f0-9]{64}$/.test(key) || manifest.rootModule!==module) throw new Error('native cache belongs to a different input');
  for(const [record,name] of [[manifest.generatedInput,module+'.lean'],[manifest.generatedFixture,'source.ast.json']]) {
    if(!record || record.path!==join(inputDirectory,name) || sha(record.path)!==record.sha256)
      throw new Error('compiled source input changed or belongs to a different cache');
  }
  const closure=new Set();
  function visit(module) {
    if(closure.has(module)) return;
    closure.add(module);
    const source=readFileSync(join(root,module.replaceAll('.','/')+'.lean'),'utf8');
    for(const line of source.split('\n')) {
      const imported=/^import\s+([^\n]+)/.exec(line)?.[1]?.split('--')[0]??'';
      for(const name of imported.trim().split(/\s+/)) if(name.startsWith('Solidity.')) visit(name);
    }
  }
  visit('Solidity.Tools.FastMode.Engine');
  const seen=new Set();
  for (const entry of manifest.sourceFiles) {
    if (!/^Solidity(?:\.[A-Za-z_][A-Za-z_0-9]*)+$/.test(entry.module) || seen.has(entry.module))
      throw new Error('invalid native source manifest');
    seen.add(entry.module);
    if (sha(join(root,entry.module.replaceAll('.','/')+'.lean'))!==entry.sourceSha256)
      throw new Error(`native source changed: ${entry.module}; rebuild with scripts/verify-build`);
  }
  if(seen.size!==closure.size || [...closure].some(name=>!seen.has(name))) throw new Error('native source manifest does not cover current import closure');
  return {executable, manifestSha256:sha(manifestPath), executableSha256:manifest.executable};
}

export function decodeNative(text, requests) {
  const lines=text.trim().split(/\r?\n/).map(line=>JSON.parse(line));
  if (lines[0]?.ready!==true || lines.length!==requests.length+1) throw new Error('native protocol: missing or extra responses');
  return requests.map((request,i)=>{
    const response=lines[i+1];
    if (response.gap) throw new Error(`native input unsupported: ${response.gap}`);
    if (!Array.isArray(response.results) || response.results.length!==1) throw new Error('native protocol: expected one selected obligation');
    const row=response.results[0];
    if (row.sourceId!==request.sourceId || row.function!==request.function || row.reading!==(request.reading??'solc') || row.verification!=='native'
        || !['proved','refuted','pending','unsupported','skipped'].includes(row.status))
      throw new Error('native protocol: wrong obligation, mode or verdict');
    if(row.status==='refuted' && (!row.counterexample || row.counterexample.certified!==false)) throw new Error('native protocol: refutation lacks an uncertified witness');
    return {...row, verification:'native'};
  });
}

export function runNative(requests, {directory,timeoutMs=300000}={}) {
  const before=nativeBuild(directory);
  const child=spawnSync(before.executable,[],{input:requests.map(r=>JSON.stringify(r)).join('\n')+'\n',
    encoding:'utf8',timeout:timeoutMs,maxBuffer:64*1024*1024});
  if (child.error) throw child.error;
  if (child.status!==0) throw new Error(`native runtime failed: ${child.signal??child.status}: ${child.stderr}`);
  const after=nativeBuild(directory);
  if (JSON.stringify(before)!==JSON.stringify(after)) throw new Error('native build changed during verification');
  return decodeNative(child.stdout,requests);
}

function inputArtifact(fixtureBytes,contract,options) {
  if(!/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(contract)) throw new Error('unsupported contract name: '+contract);
  const self=options.selfAddress===undefined?'':` self ${BigInt(options.selfAddress)}`;
  const key=sourceHash(Buffer.concat([fixtureBytes,Buffer.from(JSON.stringify({contract,self,format:3}))]));
  const module='VerifyInput'+key;
  const directory=join(root,'.lake/verify/inputs',key);
  mkdirSync(directory,{recursive:true});
  let hash=0xcbf29ce484222325n;
  for(const byte of fixtureBytes) hash=BigInt.asUintN(64,(hash^BigInt(byte))*0x100000001b3n);
  const namespace=`SolTests.«${contract}»`;
  const input=join(directory,module+'.lean');
  writeFileSync(join(directory,'source.ast.json'),fixtureBytes);
  writeFileSync(input,`import Solidity.Tools.FastMode.Engine
solc_import "source.ast.json" hash 0x${hash.toString(16)} as ${namespace} testing
solc_scoped_problems ${namespace} decl${self}
#fast_export ${namespace}
`);
  const output=join(root,'.lake/verify/native',key);
  try {nativeBuild(output);}
  catch(error) {
    if(options.build===false) throw error;
    runTool(process.execPath,['scripts/verify-build.mjs',input,output],options.timeoutMs??300000);
    nativeBuild(output);
  }
  return output;
}

export function fastReport(paths, options={}) {
  const files=solidityFiles(paths);
  if(!files.length) throw new Error('no Solidity files selected');
  const report={results:[],errors:[]};
  const summary=error=>error.message.split('\n').find(line=>/error:|ValueError:|verify-build:/.test(line))??error.message.split('\n')[0];
  for (const source of files) {
    let snapshot;
    try {
      snapshot=compileSnapshot(source,options);
      const {sourceBytes,sourceSha256,fixtureBytes,compiled,compilationSha256}=snapshot;
      const primary=compiled.sourceUnits?.find(u=>u.name===compiled.header.mainSource);
      const ast=compiled.ast??primary?.ast;
      const partial={results:[],errors:[]};
      const location=sourceLocations(ast,sourceBytes);
      const listing=runSolidityTests([source],{...options,list:true,counterexamples:false});
      partial.errors.push(...listing.errors);
      const groups=new Map();
      for(const expected of listing.results) {
        if(expected.sourceHash!==sourceSha256) throw new Error('discovery source differs from native input');
        if(expected.status!=='ready') {partial.results.push({...expected,verification:'native',compilationSha256});continue;}
        const group=groups.get(expected.contract)??[];group.push(expected);groups.set(expected.contract,group);
      }
      for(const [contract,expectedRows] of groups) {
        const started=performance.now();
        try {
          const directory=inputArtifact(fixtureBytes,contract,options);
          const requests=expectedRows.map(expected=>({sourceId:expected.sourceId,function:expected.function,
            reading:expected.tag==='specified'?'solc':expected.reading}));
          const actualRows=runNative(requests,{...options,directory});
          const nativeBatchMs=performance.now()-started;
          for(let i=0;i<actualRows.length;i++) {
            const expected=expectedRows[i],actual=actualRows[i];
            let row={...expected,...actual,sourceSha256,sourceHash:sourceSha256,compilationSha256,
              requestSha256:sourceHash(Buffer.concat([fixtureBytes,Buffer.from(JSON.stringify(requests[i]))])),
              range:location(contract,actual),...snapshot.locate({...actual,contract}),sourceLineKind:'declaration',elapsedMs:expectedRows.length===1?nativeBatchMs:null,
              nativeBatchMs,nativeBatchSize:expectedRows.length,
              timingScope:'shared native input preparation, provenance, process and checking; compiler/discovery excluded'};
            if(row.counterexample) row={...row,counterexample:snapshot.witness(row)};
            partial.results.push(row);
          }
        } catch(error) {
          for(const expected of expectedRows) partial.results.push({...expected,status:'error',verification:'native',reason:summary(error),compilationSha256,elapsedMs:null});
          partial.errors.push({source,contract,reason:summary(error),diagnostic:error.message});
        }
      }
      snapshot.assertUnchanged();
      report.results.push(...partial.results);report.errors.push(...partial.errors);
    } catch(error) {report.errors.push({source,reason:error.message});}
    finally {snapshot?.close();}
  }
  return report;
}
