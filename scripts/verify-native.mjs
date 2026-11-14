/** Compiled-only adapter. There is deliberately no interpreted fallback. */
import {readFileSync, mkdtempSync, rmSync} from 'node:fs';
import {resolve, join, dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {tmpdir} from 'node:os';
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
import {solidityFiles, runTool, runSolidityTests} from './test-solidity.mjs';
import {sourceHash, sourceLocations, sourceWitness} from './source-locations.mjs';
const root=resolve(dirname(fileURLToPath(import.meta.url)), '..');
const sha=path=>createHash('sha256').update(readFileSync(path)).digest('hex');

export function nativeBuild(directory=join(root,'.lake/direct-native')) {
  const manifestPath=join(directory,'build.json');
  const manifest=JSON.parse(readFileSync(manifestPath,'utf8'));
  const executable=join(directory,'direct-check');
  if (manifest.version!==1 || manifest.platform!==process.platform || manifest.arch!==process.arch.replace('x64','x86_64')
      || manifest.toolchain!==readFileSync(join(root,'lean-toolchain'),'utf8').trim()
      || manifest.leanCommit!=='797c613eb9b6d4ec95db23e3e00af9ac6657f24b'
      || !Array.isArray(manifest.sourceFiles) || !manifest.sourceFiles.length)
    throw new Error('native build identity mismatch; rebuild with scripts/verify-build');
  if (sha(executable)!==manifest.executable) throw new Error('native executable changed; rebuild with scripts/verify-build');
  if (sha(join(root,'web/browser/direct-bridge.c'))!==manifest.bridgeSha256
      || sha(join(root,'scripts/direct-runtime-closure.py'))!==manifest.closureScriptSha256)
    throw new Error('native bridge or closure builder changed; rebuild with scripts/verify-build');
  for(const relative of ['scripts/build-direct-native.py','scripts/direct-runtime-closure.py','web/browser/direct-bridge.c','lean-toolchain','lakefile.toml']) {
    const path=join(root,relative);
    if(manifest.buildInputs?.[path]!==sha(path)) throw new Error('native build input changed: '+relative);
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
  visit('Solidity.Tools.DirectRuntime');
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
    if (row.sourceId!==request.sourceId || row.function!==request.function || row.reading!=='solc' || row.verification!=='direct'
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

export function fastReport(paths, options={}) {
  if (options.selfAddress!==undefined) throw new Error('fast mode does not yet support --self-address');
  const files=solidityFiles(paths);
  if(!files.length) throw new Error('no Solidity files selected');
  const report={results:[],errors:[]};
  try {nativeBuild(options.directory);}
  catch(error) {
    if(options.build===false || options.directory) throw error;
    runTool(process.execPath,['scripts/verify-build.mjs'],options.timeoutMs??300000);
    nativeBuild();
  }
  for (const source of files) {
    const scratch=mkdtempSync(join(tmpdir(),'verify-'));
    try {
      const sourceBytes=readFileSync(source), sourceSha256=sourceHash(sourceBytes);
      const args=['--source',source,'--out',join(scratch,'source.ast.json'),'--no-wrapper'];
      for (const key of ['solkey','soljson']) if(options[key]) args.push('--'+key,options[key]);
      runTool(process.execPath,['scripts/solc-ast.mjs',...args],options.timeoutMs??300000);
      const compiled=JSON.parse(readFileSync(join(scratch,'source.ast.json'),'utf8'));
      const ast=compiled.ast??compiled.sourceUnits?.find(u=>u.name===compiled.header.mainSource)?.ast;
      const compiledHash=compiled.header.sourceSha256??compiled.sourceUnits?.find(u=>u.name===compiled.header.mainSource)?.sourceSha256;
      if(compiledHash!==sourceSha256) throw new Error('source changed during compilation');
      if(compiled.sourceUnits?.length>1) throw new Error('native runtime does not yet support multi-source compilation units');
      const location=sourceLocations(ast,sourceBytes);
      const listing=runSolidityTests([source],{...options,list:true,counterexamples:false});
      report.errors.push(...listing.errors);
      for(const expected of listing.results) {
        if(expected.sourceHash!==sourceSha256) throw new Error('discovery source differs from native input');
        if(expected.status!=='ready') {
          report.results.push({...expected,verification:'native'});continue;
        }
        const contract=ast.nodes.find(n=>n.nodeType==='ContractDefinition' && n.name===expected.contract);
        const node=contract?.nodes.find(n=>n.nodeType==='FunctionDefinition' && n.id===expected.sourceId);
        if(!node || node.kind!=='function' || contract.baseContracts?.length) {
          report.results.push({...expected,status:'unsupported',verification:'native',reason:'native runtime does not yet support this inherited or deployment obligation'});
          continue;
        }
        const request={contract,sourceId:node.id,function:node.name};
        try {
          const [actual]=runNative([request],options);
          let row={...expected,...actual,function:expected.function,signature:expected.signature,
            sourceSha256,sourceHash:sourceSha256,requestSha256:sourceHash(Buffer.from(JSON.stringify(request))),
            range:location(expected.contract,actual)};
          if(row.counterexample) row={...row,counterexample:sourceWitness(ast,expected.contract,row)};
          report.results.push(row);
        } catch(error) {
          report.results.push({...expected,status:'error',verification:'native',reason:error.message});
          report.errors.push({source,contract:expected.contract,function:expected.function,reason:error.message});
        }
      }
      if (sourceHash(readFileSync(source))!==sourceSha256) throw new Error('source changed during verification');
    } catch(error) {report.errors.push({source,reason:error.message});}
    finally {rmSync(scratch,{recursive:true,force:true});}
  }
  return report;
}
