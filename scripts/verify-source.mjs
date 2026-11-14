/** Freeze complete compiler inputs around both modes; never compare just the main file. */
import {readFileSync,existsSync,mkdtempSync,rmSync} from 'node:fs';
import {resolve,dirname,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {tmpdir} from 'node:os';
import {runTool,runSolidityTests,solidityFiles} from './test-solidity.mjs';
import {sourceHash,sourceLocations,sourceWitness} from './source-locations.mjs';
const root=resolve(dirname(fileURLToPath(import.meta.url)),'..');

export function freezeSources(compiled,source,options={}) {
  const entries=[[source,compiled.header.sourceSha256??compiled.sourceUnits?.find(u=>u.name===compiled.header.mainSource)?.sourceSha256]];
  for(const unit of compiled.sourceUnits??[]) {
    const base=options.projectRoot??dirname(resolve(source));
    const candidates=[resolve(base,unit.name),...(options.includePaths??[]).map(p=>resolve(base,p,unit.name))];
    const path=candidates.find(p=>existsSync(p));
    if(!path) throw new Error('dependency disappeared: '+unit.name);
    entries.push([path,unit.sourceSha256]);
  }
  const check=()=>{
    for(const [path,expected] of entries) if(sourceHash(readFileSync(path))!==expected)
      throw new Error('source changed during verification: '+path);
  };
  check();return check;
}

/** Resolve inherited/imported witness presentation by exact declaration ID.
 * Ambiguous or absent declarations preserve the original witness unchanged. */
export function sourceCounterexample(ast,row) {
  if(!Number.isSafeInteger(row.sourceId) || row.sourceId<=0) return row.counterexample;
  const owners=(ast.nodes??[]).flatMap(owner=>owner.nodeType==='ContractDefinition'
    ? (owner.nodes??[]).filter(n=>n.nodeType==='FunctionDefinition' && n.id===row.sourceId).map(()=>owner) : []);
  return owners.length===1 ? sourceWitness({nodes:[owners[0]]},owners[0].name,row) : row.counterexample;
}

export function compileSnapshot(source,options={}) {
  const scratch=mkdtempSync(join(tmpdir(),'verify-source-'));
  try {
    const sourceBytes=readFileSync(source), sourceSha256=sourceHash(sourceBytes);
    const solkey=resolve(options.solkey??process.env.SOLKEY_ROOT??join(root,'../solkey'));
    const gradle=join(solkey,'keyext.solidity.core/build.gradle');
    const configurationHash=sourceHash(readFileSync(gradle));
    const args=['scripts/solc-ast.mjs','--source',source,'--out',join(scratch,'source.ast.json'),'--no-wrapper'];
    for(const key of ['solkey','soljson']) if(options[key]) args.push('--'+key,resolve(options[key]));
    if(options.projectRoot) args.push('--project-root',resolve(options.projectRoot));
    for(const p of options.includePaths??[]) args.push('--include-path',p);
    for(const p of options.remappings??[]) args.push('--remapping',p);
    runTool(process.execPath,args,options.timeoutMs??300000);
    const fixtureBytes=readFileSync(join(scratch,'source.ast.json')), compiled=JSON.parse(fixtureBytes);
    const compiler=join(resolve(options.soljson??join(solkey,'keyext.solidity.core/build/soljson')),compiled.header.compilerFile);
    const checkSources=freezeSources(compiled,source,options);
    const assertUnchanged=()=>{
      checkSources();
      if(sourceHash(readFileSync(source))!==sourceSha256 || sourceHash(readFileSync(gradle))!==configurationHash
          || sourceHash(readFileSync(compiler))!==compiled.header.compilerSha256)
        throw new Error('compiler or source inputs changed during verification');
    };
    assertUnchanged();
    const units=compiled.sourceUnits??[{ast:compiled.ast,name:null}];
    const pathFor=unit=>{
      if(!unit.name) return source;
      const base=options.projectRoot??dirname(resolve(source));
      return [resolve(base,unit.name),...(options.includePaths??[]).map(p=>resolve(base,p,unit.name))].find(p=>existsSync(p));
    };
    const locate=row=>{
      for(const unit of units) for(const owner of unit.ast?.nodes??[]) {
        if(owner.nodeType!=='ContractDefinition') continue;
        if(!owner.nodes?.some(n=>n.nodeType==='FunctionDefinition' && n.id===row.sourceId)
            && !(row.sourceId===-1 && row.function==='constructor' && owner.name===row.contract)) continue;
        const path=pathFor(unit);
        const range=sourceLocations(unit.ast,readFileSync(path))(owner.name,row);
        if(range) return {diagnosticSource:path,range,sourceLineKind:'declaration'};
      }
      return {};
    };
    const aggregate={nodes:units.flatMap(unit=>unit.ast?.nodes??[])};
    const witness=row=>sourceCounterexample(aggregate,row);
    return {sourceBytes,sourceSha256,fixtureBytes,compiled,compilationSha256:sourceHash(fixtureBytes),
      assertUnchanged,locate,witness,close:()=>rmSync(scratch,{recursive:true,force:true})};
  } catch(error) {rmSync(scratch,{recursive:true,force:true});throw error;}
}

export function sourceReport(paths,options={}) {
  const files=solidityFiles(paths);
  if(!files.length) throw new Error('no Solidity files selected');
  const report={results:[],errors:[]};
  for(const source of files) {
    let snapshot;
    try {
      snapshot=compileSnapshot(source,options);
      const actual=runSolidityTests([source],options);
      snapshot.assertUnchanged();
      if(actual.results.some(row=>row.sourceHash!==snapshot.sourceSha256)) throw new Error('backend source identity differs from frozen input');
      report.results.push(...actual.results.map(row=>({...row,...snapshot.locate(row),...(row.counterexample?{counterexample:snapshot.witness(row)}:{}),compilationSha256:snapshot.compilationSha256})));
      report.errors.push(...actual.errors);
    } catch(error) {report.errors.push({source,stage:'input',reason:error.message,...(error.tool?{tool:error.tool}:{})});}
    finally {snapshot?.close();}
  }
  return report;
}
