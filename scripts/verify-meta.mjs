/** Extended readings use a required, fingerprinted compiled frontend plugin. */
import {readFileSync,writeFileSync,mkdirSync,mkdtempSync,rmSync,existsSync,realpathSync,readdirSync,statSync,renameSync} from 'node:fs';
import {resolve,dirname,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {tmpdir} from 'node:os';
import {createHash,randomBytes} from 'node:crypto';
import {execFileSync} from 'node:child_process';
import {runTool} from './test-solidity.mjs';
const root=resolve(dirname(fileURLToPath(import.meta.url)),'..');
const moduleName='Solidity.Tools.FastMode.Meta';
const directory=join(root,'.lake/verify/meta');
const sha=path=>createHash('sha256').update(readFileSync(path)).digest('hex');
const commit='797c613eb9b6d4ec95db23e3e00af9ac6657f24b';
const prefix=()=>execFileSync('lean',['--print-prefix'],{encoding:'utf8'}).trim();

export function metaBuild() {
  const path=join(directory,'build.json'),manifest=JSON.parse(readFileSync(path,'utf8'));
  if(manifest.version!==1 || manifest.root!==moduleName || manifest.leanCommit!==commit
      || manifest.platform!==process.platform || manifest.arch!==process.arch)
    throw new Error('extended native build identity mismatch');
  const runtime=realpathSync(prefix());
  if(manifest.sdk!==runtime || execFileSync(join(runtime,'bin/lean'),['--githash'],{encoding:'utf8'}).trim()!==commit)throw new Error('extended native runtime mismatch');
  for(const name of ['LEAN_CC','LEAN_SYSROOT','CPATH','C_INCLUDE_PATH','CPLUS_INCLUDE_PATH','LIBRARY_PATH','COMPILER_PATH','LD_PRELOAD','LD_LIBRARY_PATH'])if(process.env[name])throw new Error('unpinned native runtime override: '+name);
  const sdkFiles=['lean','lake','leanc','clang','ld.lld','llvm-ar'].map(name=>join(runtime,'bin',name));
  for(const [directory,accept] of [['include',name=>name.endsWith('.h')],['lib',name=>/\.(?:a|so|dylib)$|\.so\./.test(name)]])
    for(const relative of readdirSync(join(runtime,directory),{recursive:true})) {
      const path=join(runtime,directory,relative);if(accept(relative)&&statSync(path).isFile())sdkFiles.push(path);
    }
  const expectedSdk=new Set(sdkFiles.map(file=>realpathSync(file)));
  if(!manifest.sdkFiles || expectedSdk.size!==Object.keys(manifest.sdkFiles).length
      || Object.keys(manifest.sdkFiles).some(file=>!expectedSdk.has(file)))throw new Error('extended native SDK manifest incomplete');
  for(const [file,hash] of Object.entries(manifest.sdkFiles))if(sha(file)!==hash)throw new Error('extended native SDK changed: '+file);
  const closure=new Set();
  function visit(name) {
    if(closure.has(name))return;closure.add(name);
    const source=readFileSync(join(root,name.replaceAll('.','/')+'.lean'),'utf8');
    for(const line of source.split('\n')) {
      const imports=/^(?:public\s+)?import\s+(.*)/.exec(line)?.[1]?.split('--')[0]??'';
      for(const dependency of imports.trim().split(/\s+/))if(dependency.startsWith('Solidity.'))visit(dependency);
    }
  }
  visit(moduleName);
  if(!Array.isArray(manifest.modules) || manifest.modules.length!==closure.size
      || new Set(manifest.modules.map(m=>m.module)).size!==closure.size
      || manifest.modules.some(m=>!closure.has(m.module)))throw new Error('extended native import closure mismatch');
  for(const name of closure)for(const file of [name.replaceAll('.','/')+'.lean','.lake/build/ir/'+name.replaceAll('.','/')+'.c']) {
    const path=join(root,file);if(manifest.files?.[path]!==sha(path))throw new Error('extended native source changed: '+name);
  }
  for(const relative of ['lean-toolchain','lakefile.toml','scripts/verify-meta-build.py','scripts/verify_artifacts.py']) {
    const path=join(root,relative);if(manifest.files?.[path]!==sha(path))throw new Error('extended native build input changed');
  }
  if(manifest.plugin!==join(directory,manifest.pluginSha256,'libSolidity_Tools_FastMode_Meta.so')
      || !/^[a-f0-9]{64}$/.test(manifest.pluginSha256) || sha(manifest.plugin)!==manifest.pluginSha256)
    throw new Error('extended native plugin changed');
  for(const [file,hash] of Object.entries(manifest.files))if(sha(file)!==hash)throw new Error('extended native artifact changed: '+file);
  return {plugin:manifest.plugin,identity:sha(path),files:manifest.files};
}

function ensureBuild(options) {
  const sdk=realpathSync(prefix());
  if(execFileSync(join(sdk,'bin/lean'),['--githash'],{encoding:'utf8'}).trim()!==commit)
    throw new Error('extended native requires the pinned Lean toolchain');
  try {return {build:metaBuild(),sdk};} catch(error) {if(options.build===false)throw error;}
  runTool('python3',['scripts/verify-meta-build.py',sdk,directory],options.timeoutMs??300000);
  return {build:metaBuild(),sdk};
}

export function decodeMeta(text,diagnostics,requests,nonce) {
  if(!/^[a-f0-9]{32}$/.test(nonce??''))throw new Error('missing native execution challenge');
  if(!diagnostics.split(/\r?\n/).includes('FAST_META_C '+nonce+' command'))throw new Error('compiled extended command did not execute');
  const rows=JSON.parse(text);
  if(!Array.isArray(rows) || rows.length!==requests.length)throw new Error('extended native response count mismatch');
  return rows.map((row,i)=>{
    const request=requests[i];
    if(!row || typeof row!=='object' || row.sourceId!==request.sourceId || row.function!==request.function || row.reading!=='solc'
        || row.verification!=='native' || !['proved','pending','unsupported','error'].includes(row.status))
      throw new Error('extended native response identity mismatch: '+JSON.stringify(row));
    if(row.status!=='error' && (!['rec_auto','rec_auto_c','sol_prove'].includes(row.nativeStrategy)
        || !diagnostics.split(/\r?\n/).includes('FAST_META_C '+nonce+' '+row.nativeStrategy)))
      throw new Error('compiled extended tactic walk did not execute');
    const nativeCProbes=['command','rec_auto','rec_auto_c','sol_prove','closing']
      .filter(label=>diagnostics.split(/\r?\n/).includes('FAST_META_C '+nonce+' '+label));
    return {...row,nativeCProbes,nativeProbeScope:'process shared across selected requests'};
  });
}

export function runExtended(fixtureBytes,contract,requests,options={}) {
  if(!/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(contract))throw new Error('invalid extended contract name');
  const {build,sdk}=ensureBuild(options),scratch=mkdtempSync(join(tmpdir(),'verify-meta-'));
  const priorNonce=process.env.VERIFY_META_NATIVE_NONCE,nonce=randomBytes(16).toString('hex');
  try {
    writeFileSync(join(scratch,'source.ast.json'),fixtureBytes);
    let hash=0xcbf29ce484222325n;
    for(const byte of fixtureBytes)hash=BigInt.asUintN(64,(hash^BigInt(byte))*0x100000001b3n);
    const namespace=`SolTests.«${contract}»`,output=join(scratch,'results.json'),source=join(scratch,'Input.lean');
    const self=options.selfAddress===undefined?'':` self ${BigInt(options.selfAddress)}`;
    writeFileSync(source,`import ${moduleName}
solc_import "source.ast.json" hash 0x${hash.toString(16)} as ${namespace} testing
solc_scoped_problems ${namespace} decl${self}
#fast_meta ${namespace} ids ${JSON.stringify(JSON.stringify(requests.map(r=>r.sourceId)))} to ${JSON.stringify(output)}
`);
    const setup=JSON.parse(runTool(join(sdk,'bin/lake'),['--quiet',...(options.build===false?['--no-build']:[]),'setup-file',source],options.timeoutMs??300000));
    const validateImports=()=>{
      for(const artifacts of Object.values(setup.importArts))for(const file of artifacts)
        if(build.files[realpathSync(file)]!==sha(file))throw new Error('runtime import differs from compiled extended build: '+file);
    };
    validateImports();
    const setupPath=join(scratch,'setup.json');writeFileSync(setupPath,JSON.stringify(setup));
    process.env.VERIFY_META_NATIVE_NONCE=nonce;
    const diagnostics=runTool(join(sdk,'bin/lean'),['--setup='+setupPath,'--plugin='+build.plugin,'-j1','--tstack=131072',source],options.timeoutMs??300000);
    const after=metaBuild();validateImports();
    if(build.identity!==after.identity)throw new Error('extended native build changed during verification');
    return decodeMeta(readFileSync(output,'utf8'),diagnostics,requests,nonce);
  } finally {
    if(priorNonce===undefined)delete process.env.VERIFY_META_NATIVE_NONCE;else process.env.VERIFY_META_NATIVE_NONCE=priorNonce;
    rmSync(scratch,{recursive:true,force:true});
  }
}

// Reading discovery is ordinary Lean preparation, never native verdict execution.
const readingsDirectory=join(root,'.lake/verify/readings');
const readingsManifest=join(readingsDirectory,'build.json');
function discoverySources(sdk) {
  const paths=readdirSync(join(root,'Solidity'),{recursive:true})
    .filter(name=>name.endsWith('.lean')).map(name=>join(root,'Solidity',name));
  paths.push(join(root,'lean-toolchain'),join(root,'lakefile.toml'),fileURLToPath(import.meta.url),
    join(sdk,'bin/lean'),join(sdk,'bin/lake'));
  return Object.fromEntries(paths.sort().map(path=>[path,sha(path)]));
}
const sameSnapshot=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
function discoveryReady(sdk,sources) {
  const manifest=JSON.parse(readFileSync(readingsManifest,'utf8'));
  if(manifest.version!==1 || manifest.purpose!=='readings-only' || manifest.root!==root
      || manifest.module!==moduleName || manifest.sdk!==sdk || manifest.leanCommit!==commit
      || !sameSnapshot(manifest.sources,sources) || !manifest.files || !Object.keys(manifest.files).length)
    throw new Error('reading discovery cache is unavailable or stale');
  for(const [file,hash] of Object.entries(manifest.files))
    if(sha(file)!==hash)throw new Error('reading discovery artifact changed: '+file);
  return manifest;
}
export function decodeReadings(text,requests) {
  const rows=JSON.parse(text);
  if(!Array.isArray(rows)||rows.length!==requests.length||rows.some((row,i)=>
      !row || typeof row!=='object' || Object.keys(row).sort().join(',')!=='reading,sourceId'
      || !Number.isSafeInteger(row.sourceId) || row.sourceId!==requests[i].sourceId || !['clean','solc'].includes(row.reading)))
    throw new Error('per-obligation reading discovery identity mismatch');
  return rows;
}
export function runReadings(fixtureBytes,contract,requests,options={}) {
  if(!/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(contract))throw new Error('invalid discovery contract name');
  const sdk=realpathSync(prefix());
  if(execFileSync(join(sdk,'bin/lean'),['--githash'],{encoding:'utf8'}).trim()!==commit)
    throw new Error('reading discovery requires the pinned Lean toolchain');
  const sources=discoverySources(sdk);
  let ready,legacy;
  try {ready=discoveryReady(sdk,sources);} catch(error) {
    if(options.build===false) {
      if(existsSync(readingsManifest))throw error;
      // A previously pinned native build can attest existing artifacts without building.
      legacy=metaBuild();
    } else runTool(join(sdk,'bin/lake'),['build',moduleName],options.timeoutMs??300000);
  }
  if(!sameSnapshot(sources,discoverySources(sdk)))throw new Error('reading discovery sources changed during preparation');
  const scratch=mkdtempSync(join(tmpdir(),'verify-readings-'));
  try {
    writeFileSync(join(scratch,'source.ast.json'),fixtureBytes);
    let hash=0xcbf29ce484222325n;
    for(const byte of fixtureBytes)hash=BigInt.asUintN(64,(hash^BigInt(byte))*0x100000001b3n);
    const namespace=`SolTests.«${contract}»`,output=join(scratch,'readings.json'),source=join(scratch,'Input.lean');
    const self=options.selfAddress===undefined?'':` self ${BigInt(options.selfAddress)}`;
    writeFileSync(source,`import ${moduleName}
solc_import "source.ast.json" hash 0x${hash.toString(16)} as ${namespace} testing
solc_scoped_problems ${namespace} decl${self}
#fast_readings ${namespace} ids ${JSON.stringify(JSON.stringify(requests.map(r=>r.sourceId)))} to ${JSON.stringify(output)}
`);
    const setup=JSON.parse(runTool(join(sdk,'bin/lake'),['--quiet',...(options.build===false?['--no-build']:[]),'setup-file',source],options.timeoutMs??300000));
    if(!setup.importArts?.[moduleName]?.length)throw new Error('reading discovery root artifact missing');
    const snapshot=()=>Object.fromEntries([...new Set(Object.values(setup.importArts).flat().map(file=>realpathSync(file)))]
      .sort().map(file=>[file,sha(file)]));
    const files=snapshot();
    if(ready && !sameSnapshot(ready.files,files))throw new Error('reading discovery runtime imports differ from cache');
    if(legacy)for(const [file,hash] of Object.entries(files))
      if(legacy.files[file]!==hash)throw new Error('reading discovery import differs from existing build: '+file);
    const setupPath=join(scratch,'setup.json');writeFileSync(setupPath,JSON.stringify(setup));
    runTool(join(sdk,'bin/lean'),['--setup='+setupPath,'-j1','--tstack=131072',source],options.timeoutMs??300000);
    if(!sameSnapshot(sources,discoverySources(sdk)) || !sameSnapshot(files,snapshot()))
      throw new Error('reading discovery inputs changed during execution');
    const rows=decodeReadings(readFileSync(output,'utf8'),requests);
    if(!ready) {
      mkdirSync(readingsDirectory,{recursive:true});
      writeFileSync(readingsManifest+'.tmp',JSON.stringify({version:1,purpose:'readings-only',
        root,module:moduleName,sdk,leanCommit:commit,sources,files},null,2)+'\n');
      renameSync(readingsManifest+'.tmp',readingsManifest);
    }
    return rows;
  } finally {rmSync(scratch,{recursive:true,force:true});}
}
