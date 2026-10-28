#!/usr/bin/env node
/**
 * Compilation-unit provenance. Preserve each original compiler AST and its
 * per-file digest/modes; compiler IDs, not source spelling, resolve imports.
 * This records external analysis, not compiler correctness or authentication.
 */
import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
import {fileURLToPath} from 'node:url';

const sha = bytes => createHash('sha256').update(bytes).digest('hex');
export const COMPILERS = [
  {version:'0.8.34+commit.80d5c536.Emscripten.clang',
   file:'soljson-v0.8.34+commit.80d5c536.js',
   sha256:'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8'},
  {version:'0.8.38+commit.1835d247.Emscripten.clang',
   file:'soljson-v0.8.38+commit.1835d247.js',
   sha256:'6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390'},
];

/** Keep strings and ordinary comments out of NatSpec detection. solc drops
loop NatSpec, so this check runs on source text before that information is lost. */
export function hasUnitSpecifications(source) {
  for (let i=0;i<source.length;) {
    if (source[i]==='"' || source[i]==="'") {
      const quote=source[i++];
      while (i<source.length) {
        if (source[i]==='\\') {i+=2;continue;}
        if (source[i++]===quote) break;
      }
    } else if (source.startsWith('//',i)) {
      const end=source.indexOf('\n',i), stop=end<0?source.length:end;
      if (source[i+2]==='/' && source.slice(i,stop).includes('@custom:key')) return true;
      i=stop;
    } else if (source.startsWith('/*',i)) {
      const end=source.indexOf('*/',i+2), stop=end<0?source.length:end+2;
      if (source[i+2]==='*' && source.slice(i,stop).includes('@custom:key')) return true;
      i=stop;
    } else i++;
  }
  return false;
}

/** All src offsets are bytes in their own compiler source, including Unicode. */
export function normaliseUnit(ast, source, sourceId) {
  const bytes=Buffer.from(source);
  const visit=value=>{
    if (Array.isArray(value)) return value.map(visit);
    if (!value || typeof value!=='object') return value;
    const result=Object.fromEntries(Object.entries(value).map(([key,item])=>[
      key,['referencedDeclaration','scope','superFunction'].includes(key) &&
      Number.isInteger(item) && item>=2**31 ? item-2**32 : visit(item)]));
    if (typeof value.nodeType==='string') {
      const parts=/^(\d+):(\d+):(\d+)$/.exec(value.src ?? '');
      if (!parts || Number(parts[3])!==sourceId ||
          Number(parts[1])+Number(parts[2])>bytes.length)
        throw new Error('foreign or malformed source location');
      result.line=bytes.subarray(0,Number(parts[1])).toString('utf8').split('\n').length;
    }
    return result;
  };
  return visit(ast);
}

export function compilationUnitFixture({output,sources,mainSource,settings,pin,solkeyCommit=''}) {
  if (!COMPILERS.some(p=>p.version===pin?.version && p.file===pin?.file && p.sha256===pin?.sha256))
    throw new Error('unsupported exact compiler pin');
  if ((output.errors??[]).some(e=>e.severity==='error'))
    throw new Error('compilation-unit analysis failed');
  const names=Object.keys(sources);
  if (names.length<2 || !names.includes(mainSource) || names.some(n=>!n))
    throw new Error('compilation unit requires multiple sources and an existing main source');
  if (JSON.stringify(Object.keys(output.sources??{}).sort())!==JSON.stringify([...names].sort()))
    throw new Error('compiler source set differs from admitted inputs');
  const ids=new Set(), declarations=new Set();
  const sourceUnits=names.map(name=>{
    const input=sources[name], unit=output.sources[name];
    if (Object.keys(input).some(k=>k!=='content') || typeof input.content!=='string')
      throw new Error('only explicit UTF-8 source content is admitted');
    if (hasUnitSpecifications(input.content))
      throw new Error('solidity.compilationUnitSpecifications: source specifications require file-local lexical resolution');
    if (!Number.isSafeInteger(unit.id) || unit.id<0 || ids.has(unit.id))
      throw new Error('missing or duplicate compiler source identity');
    ids.add(unit.id);
    if (unit.ast?.nodeType!=='SourceUnit' || unit.ast.absolutePath!==name ||
        !Number.isSafeInteger(unit.ast.id) || unit.ast.id<0 || declarations.has(unit.ast.id))
      throw new Error('missing, foreign or duplicate source-unit AST identity');
    declarations.add(unit.ast.id);
    return {name,id:unit.id,sourceSha256:sha(Buffer.from(input.content)),
      acceptedPragmas:unit.ast.nodes.filter(n=>n.nodeType==='PragmaDirective').map(n=>n.literals),
      ast:normaliseUnit(unit.ast,input.content,unit.id)};
  });
  const byName=new Map(sourceUnits.map(u=>[u.name,u]));
  const visit=node=>{
    if (!node || typeof node!=='object') return;
    if (node.nodeType==='ImportDirective') {
      const target=byName.get(node.absolutePath);
      if (!target || !Number.isSafeInteger(node.sourceUnit) || node.sourceUnit<0 ||
          target.ast.id!==node.sourceUnit)
        throw new Error('missing or foreign resolved import target');
    }
    for (const item of Object.values(node)) {
      if (Array.isArray(item)) item.forEach(visit); else visit(item);
    }
  };
  sourceUnits.forEach(u=>visit(u.ast));
  return {header:{solcVersion:pin.version,solkeyCommit,provenanceVersion:2,
    compilerFile:pin.file,compilerSha256:pin.sha256,validationStage:'analysis',
    settings,mainSource},sourceUnits};
}

function main(args) {
  const options={};
  for(let i=0;i<args.length;i+=2) {
    if (!['--input','--compiler','--main-source','--out'].includes(args[i]) || !args[i+1])
      throw new Error('usage: solc-unit.mjs --input standard.json --compiler soljson.js --main-source NAME --out fixture.json');
    if (options[args[i]]) throw new Error('duplicate option: '+args[i]);
    options[args[i]]=args[i+1];
  }
  if (Object.keys(options).length!==4) throw new Error('all four options are required');
  const compiler=resolve(options['--compiler']);
  const digest=sha(readFileSync(compiler));
  const expected=COMPILERS.find(p=>p.sha256===digest);
  if (!expected) throw new Error('unsupported exact compiler pin');
  const solc=createRequire(import.meta.url)(compiler);
  const version=solc.cwrap('solidity_version','string',[])();
  const pin=COMPILERS.find(p=>p.sha256===digest && p.version===version);
  if (!pin) throw new Error('unsupported exact compiler pin');
  const input=JSON.parse(new TextDecoder('utf-8',{fatal:true,ignoreBOM:true}).decode(readFileSync(options['--input'])));
  if (input.language!=='Solidity' || Object.keys(input).some(k=>!['language','sources','settings'].includes(k)))
    throw new Error('only Solidity standard JSON is admitted');
  const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
  const output=JSON.parse(compile(JSON.stringify(input),0,0));
  const fixture=compilationUnitFixture({output,sources:input.sources,settings:input.settings,
    mainSource:options['--main-source'],pin});
  writeFileSync(options['--out'],JSON.stringify(fixture,null,2)+'\n');
}

if (process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url))
  try {main(process.argv.slice(2));} catch(e) {console.error(e.message);process.exitCode=1;}
