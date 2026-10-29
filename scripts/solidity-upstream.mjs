#!/usr/bin/env node
import {creationTryContext} from './creation-try-adapter.mjs';
import {directSelfTryContext} from './self-try-adapter.mjs';
/** Pinned upstream corpus, exact compiler diagnostics and typed runtime replay.
 * See docs/solidity-upstream-tests.md. No npm or Lake dependency is added.
 */
import {readFileSync, writeFileSync, mkdirSync, mkdtempSync, readdirSync, existsSync, statSync, renameSync, rmSync} from 'node:fs';
import {resolve, dirname, join, relative} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {execFileSync, spawnSync} from 'node:child_process';
import {runTool} from './test-solidity.mjs';
import {compilerCode} from './solc-code.mjs';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const SNAPSHOT = join(ROOT, 'tests/upstream');
export const PIN = '1835d247de183f23e7b0e2bc4a50732af525b77c';
export const COMPILER_SHA = '6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390';
const VERSION = '0.8.38+commit.1835d247.Emscripten.clang';
const EVM = ['homestead','tangerineWhistle','spuriousDragon','byzantium','constantinople',
  'petersburg','istanbul','berlin','london','paris','shanghai','cancun','prague','osaka'];
const sha = bytes => createHash('sha256').update(bytes).digest('hex');
const json = path => JSON.parse(readFileSync(path, 'utf8'));
const save = (path, data) => {mkdirSync(dirname(path), {recursive:true}); writeFileSync(path, JSON.stringify(data, null, 2)+'\n');};

export function verifySnapshot(destination = join(ROOT, '.lake/upstream/solidity')) {
  const manifest = json(join(SNAPSHOT, 'snapshot.json'));
  if (manifest.version !== 1 || manifest.commit !== PIN || manifest.tag !== 'v0.8.38')
    throw new Error('unexpected upstream snapshot pin');
  const archive = join(SNAPSHOT, manifest.archive);
  if (sha(readFileSync(archive)) !== manifest.archiveSha256) throw new Error('snapshot archive hash mismatch');
  const names = new Set();
  for (const f of manifest.files) {
    if (f.path.startsWith('/') || f.path.split('/').some(p => p === '..') || names.has(f.path))
      throw new Error('unsafe or duplicate snapshot path: '+f.path);
    names.add(f.path);
  }
  const check = directory => {
    for (const f of manifest.files) {
      const bytes = readFileSync(join(directory, f.path));
      if (bytes.length !== f.bytes || sha(bytes) !== f.sha256) throw new Error('snapshot file drift: '+f.path);
    }
  };
  // Never rewrite a populated snapshot while another runner may be reading it.
  // Every invocation still hashes every pinned file, including a reused tree.
  if (!existsSync(destination) || readdirSync(destination).length === 0) {
    mkdirSync(dirname(destination), {recursive:true});
    const staging=mkdtempSync(join(dirname(destination), '.snapshot-'));
    try {
      execFileSync('tar', ['--no-same-owner', '--no-same-permissions', '-xzf', archive, '-C', staging]);
      check(staging);
      try {renameSync(staging,destination);}
      catch(e) {
        if (!['EEXIST','ENOTEMPTY'].includes(e.code)) throw e;
        // Another verified publisher won. Validate its complete bytes below.
      }
    } finally {rmSync(staging,{recursive:true,force:true});}
  }
  check(destination);
  return {manifest, directory:destination};
}

/** Match TestCaseReader's byte-preserving source/settings/expectation sections. */
export function parseFixture(text) {
  const sources = new Map(), settings = {};
  let name = '', source = '', mode = 'source';
  const expectations = [];
  for (const line of text.split('\n').slice(0, text.endsWith('\n') ? -1 : undefined)) {
    if (mode === 'expectations') {
      if (line === '//') expectations.push('');
      else if (line.startsWith('// ')) expectations.push(line.slice(3));
      else if (line.trim()) throw new Error('unsupported expectation line: '+line);
    } else if (line.startsWith('// ----')) mode = 'expectations';
    else if (line.startsWith('// ====')) mode = 'settings';
    else if (mode === 'settings') {
      const match = /^\/\/ ([^:]+):\s*(.*)$/.exec(line);
      if (!match) throw new Error('unsupported setting line: '+line);
      if (Object.hasOwn(settings, match[1])) throw new Error('duplicate setting: '+match[1]);
      settings[match[1]] = match[2];
    } else {
      const match = /^==== Source:\s*(.*?)\s*====$/.exec(line);
      if (match) {
        if (name || source) {
          if (sources.has(name)) throw new Error('duplicate source: '+name);
          sources.set(name, source);
        }
        name = match[1]; source = '';
      } else if (line.startsWith('==== ExternalSource:')) throw new Error('external-source fixture needs upstream filesystem callback');
      else source += line+'\n';
    }
  }
  if (sources.has(name)) throw new Error('duplicate source: '+name);
  sources.set(name, source);
  return {sources, settings, expectations, mainSource:name};
}

export function withPreamble(source, v1 = false) {
  return 'pragma solidity >=0.0;\n' +
    (source.includes('SPDX-License-Identifier:') ? '' : '// SPDX-License-Identifier: GPL-3.0\n') +
    (v1 && !source.includes('pragma experimental ABIEncoderV2;') && !source.includes('pragma abicoder') ? 'pragma abicoder v1;\n' : '') + source;
}

export function evmCompatible(constraint, evm = 'osaka') {
  if (!constraint) return true;
  const match = /^(>=|<=|>|<|=)?\s*(\w+)$/.exec(constraint);
  if (!match || !EVM.includes(match[2])) throw new Error('unsupported EVM constraint: '+constraint);
  const a = EVM.indexOf(evm), b = EVM.indexOf(match[2]);
  return {'>=':a>=b,'<=':a<=b,'>':a>b,'<':a<b,'=':a===b}[match[1] ?? '='];
}

/** SemanticTest defaults to both source evaluation orders. Generated SSA/EVM
 * code is outside this interpreter adapter's scope in every configuration. */
export function runtimePipelines(settings) {
  const mode=settings.compileViaYul ?? 'also';
  if (mode === 'false') return ['legacy'];
  if (mode === 'true') return ['viaIR'];
  if (mode === 'also') return ['legacy','viaIR'];
  throw new Error('unsupported runtime pipeline setting: '+mode);
}

export function diagnosticLines(errors, offsets) {
  return errors.filter(e => !e.message.startsWith('This is a pre-release compiler version')).map(e => {
    const loc = e.sourceLocation;
    const offset = offsets.get(loc?.file) ?? 0;
    const source = loc?.file ? loc.file+':' : '';
    const location = loc && loc.start >= 0 ? `(${source}${loc.start-offset}-${loc.end-offset}): ` : '';
    let message = e.message;
    if (message.startsWith('Source file requires different compiler version (current compiler is'))
      message = 'Source file requires different compiler version (current compiler is ....';
    return `${e.type}${e.errorCode ? ' '+e.errorCode : ''}: ${location}${message.replaceAll('\n', '\\n')}`;
  });
}

const scalarType = type => /^(u?int(?:\d+)?|bool|address(?: payable)?)$/.test(type);
function integer(text) {
  if (!/^-?(?:0|[1-9]\d*)$|^0x[0-9a-fA-F]+$/.test(text)) throw new Error('unsupported ABI word: '+text);
  return text.startsWith('-0x') ? -BigInt(text.slice(1)) : BigInt(text);
}
function scalarArg(token, type) {
  if (type === 'bool') {
    if (['true','1','0x01','0x1'].includes(token)) return 'true';
    if (['false','0','0x00','0x0'].includes(token)) return 'false';
    throw new Error('malformed ABI Boolean input requires ABI decoder replay');
  }
  let n = integer(token);
  if (type.startsWith('int') && n >= 2n**255n && n < 2n**256n) n -= 2n**256n;
  const signed = type.startsWith('int');
  const bits = type.startsWith('address') ? 160 : Number(type.match(/\d+/)?.[0] ?? 256);
  if (n < (signed ? -(2n**BigInt(bits-1)) : 0n) || n >= 2n**BigInt(signed ? bits-1 : bits))
    throw new Error('noncanonical ABI input requires ABI decoder replay');
  return n.toString();
}

/** Native TestFileParser parameters: numeric/Boolean words, aligned words,
 * literal hex bytes and strings padded on the right to one word. */
function stripFixtureComments(line) {
  let quoted=false,escaped=false,result='';
  for(let i=0;i<line.length;i++) {
    const c=line[i];
    if(!quoted && c==='#') {
      const end=line.indexOf('#',i+1);
      if(end<0) throw new Error('unterminated fixture comment');
      const tail=line.slice(end+1).trimStart();
      if(tail && !tail.startsWith('->')) throw new Error('fixture comment outside argument/expectation boundary');
      result+=' ';i=end;continue;
    }
    result+=c;
    if(escaped) escaped=false;
    else if(quoted && c==='\\') escaped=true;
    else if(c==='"') quoted=!quoted;
  }
  return result;
}
function parameterTokens(text) {
  let quoted=false,escaped=false,start=0;const tokens=[];
  for(let i=0;i<text.length;i++) {
    const c=text[i];
    if(escaped) escaped=false;
    else if(quoted && c==='\\') escaped=true;
    else if(c==='"') quoted=!quoted;
    else if(!quoted && c===',') {tokens.push(text.slice(start,i).trim());start=i+1;}
  }
  if(quoted) throw new Error('unterminated ABI parameter string');
  tokens.push(text.slice(start).trim());return tokens;
}
export function revertBytes(text) {
  if (!text.trim()) throw new Error('missing revert-data expectation');
  return parameterTokens(text).flatMap(token => {
    const hex=/^hex"([0-9a-fA-F]*)"$/.exec(token);
    if(hex) {
      if(hex[1].length%2) throw new Error('odd-length revert hex string');
      return [...Buffer.from(hex[1],'hex')];
    }
    if(token.startsWith('"') && token.endsWith('"')) {
      const body=token.slice(1,-1),bytes=[];
      for(let i=0;i<body.length;) {
        if(body[i]==='"') throw new Error('invalid ABI string quote');
        if(body[i]!=='\\') {
          const ch=String.fromCodePoint(body.codePointAt(i));bytes.push(...Buffer.from(ch));i+=ch.length;continue;
        }
        const c=body[++i];i++;
        if(c==='x') {
          const match=/^[0-9a-fA-F]{1,2}/.exec(body.slice(i));
          if(!match || (match[0].length===1 && i+1!==body.length)) throw new Error('unsupported ABI string hex escape');
          bytes.push(parseInt(match[0],16));i+=match[0].length;
        } else if(Object.hasOwn({'\\':92,n:10,r:13,t:9,'0':0},c)) bytes.push({'\\':92,n:10,r:13,t:9,'0':0}[c]);
        else throw new Error('unsupported ABI string escape');
      }
      if(bytes.length>32) throw new Error('ABI string parameter exceeds one word');
      return [...bytes,...Array(32-bytes.length).fill(0)];
    }
    let align='right';const aligned=/^(left|right)\(([^()]*)\)$/.exec(token);
    if(aligned) {align=aligned[1];token=aligned[2].trim();}
    let bytes;
    if(token==='true'||token==='false') bytes=[token==='true'?1:0];
    else if(/^0x[0-9a-fA-F]+$/.test(token)) {
      let hex=token.slice(2);if(hex.length%2)hex='0'+hex;
      bytes=[...Buffer.from(hex,'hex')];
    } else {
      if(!/^-?(?:0|[1-9]\d*)$/.test(token)) throw new Error('revert-data token not adapted: '+token);
      const value=integer(token);
      if(value<-(2n**255n)||value>=2n**256n) throw new Error('revert-data word outside ABI range');
      let hex=BigInt.asUintN(256,value).toString(16);if(hex.length%2)hex='0'+hex;
      bytes=[...Buffer.from(hex,'hex')];
    }
    if(bytes.length>32) throw new Error('revert-data word outside ABI range');
    const padding=Array(32-bytes.length).fill(0);
    return align==='left'?[...bytes,...padding]:[...padding,...bytes];
  });
}

/** Refuse every unimplemented observation; never silently drop a gas/log/vector line. */
function scalarSemanticVectors(fixture, abi) {
  const vectors = [];
  for (let line of fixture.expectations) {
    line = stripFixtureComments(line).trim();
    if (!line) continue;
    const match = /^(constructor\([^)]*\)|[A-Za-z_$][\w$]*\([^)]*\))\s*(?::\s*(.*?))?\s*->\s*(.*?)$/.exec(line);
    if (!match) throw new Error('unsupported runtime expectation: '+line);
    const ctor = match[1].startsWith('constructor(');
    if (ctor && vectors.length) throw new Error('redeployment vector needs a fresh EVM deployment');
    const declaration = abi.find(item => ctor ? item.type === 'constructor' :
      item.type === 'function' && `${item.name}(${item.inputs.map(p=>p.type).join(',')})` === match[1]);
    if (!declaration) throw new Error('non-ABI call needs raw calldata replay: '+match[1]);
    if (![...(declaration.inputs ?? []),...(declaration.outputs ?? [])].every(p=>scalarType(p.type)))
      throw new Error('dynamic/aggregate/bytes/function ABI vector not adapted');
    const tokens = match[2]?.trim() ? match[2].split(',').map(x=>x.trim()) : [];
    if (tokens.length !== declaration.inputs.length) throw new Error('noncanonical ABI argument count');
    const args = tokens.map((token,i)=>scalarArg(token, declaration.inputs[i].type));
    const expected = match[3].trim();
    const failureData = /^FAILURE,\s*(.*)$/.exec(expected);
    const failure = expected === 'FAILURE' || !!failureData;
    if (expected.startsWith('FAILURE ') && !failure)
      throw new Error('revert-data expectation not adapted');
    const values = failure || !expected ? [] : expected.split(',').map(token => {
      token=token.trim();
      const value = token === 'true' ? 1n : token === 'false' ? 0n : integer(token);
      return BigInt.asUintN(256, value).toString();
    });
    if (!failure && values.length !== (declaration.outputs ?? []).length)
      throw new Error('noncanonical ABI return count');
    vectors.push({signature:ctor ? 'constructor' : match[1], args, failure, expected:values,
      ...(failureData ? {revertBytes:revertBytes(failureData[1])} : {})});
  }
  if (!vectors.length) throw new Error('no runtime vectors');
  return vectors;
}

/** ABI names retain tuple structure; internal enum identities need a separate
 * cardinality adapter even when solc exposes their underlying uint8 ABI. */
export function abiType(p) {
  return p.type.startsWith('tuple') ? '('+(p.components ?? []).map(abiType).join(',')+')'+p.type.slice(5) : p.type;
}
function checkAbiMetadata(p) {
  if (/^enum\s/.test(p.internalType ?? '')) throw new Error('nominal enum ABI range not adapted');
  for (const c of p.components ?? []) checkAbiMetadata(c);
}
export function semanticVectors(fixture, abi) {
  // Validate nominal metadata before either path can erase it.
  for (const p of abi.flatMap(d=>[...(d.inputs ?? []),...(d.outputs ?? [])])) checkAbiMetadata(p);
  try { return scalarSemanticVectors(fixture,abi); } catch (scalarError) {
    const sources=[...(fixture.sources?.values() ?? [])].join('\n');
    const canonicalOnly = fixture.settings?.ABIEncoderV1Only === 'true' || fixture.abiCoderV1 === true ||
      /pragma\s+abicoder\s+v1\s*;/.test(sources.replace(/\/\*[\s\S]*?\*\/|\/\/[^\n]*/g,' '));
    const vectors=[];
    for (let line of fixture.expectations) {
      line=stripFixtureComments(line).trim(); if (!line) continue;
      const start=/^([A-Za-z_$][\w$]*)\(/.exec(line);
      if (!start) throw scalarError;
      let depth=0,end=-1;
      for (let i=start[1].length;i<line.length;i++) {
        if(line[i]==='(') depth++;
        if(line[i]===')' && --depth===0) {end=i+1;break;}
      }
      if(end<0) throw scalarError;
      const signature=line.slice(0,end),ctor=start[1]==='constructor';
      const rest=/^\s*(?::\s*(.*?))?\s*->\s*(.*?)$/.exec(line.slice(end));
      if(!rest) throw scalarError;
      if(ctor && vectors.length) throw new Error('redeployment vector needs a fresh EVM deployment');
      const d=abi.find(d=>ctor ? d.type==='constructor' : d.type==='function' &&
        `${d.name}(${(d.inputs ?? []).map(abiType).join(',')})`===signature);
      if(!d) throw scalarError;
      const expected=rest[2].trim(),failure=expected==='FAILURE'||expected.startsWith('FAILURE,');
      const payload=failure ? (expected==='FAILURE' ? '' : expected.slice(8).trim()) : expected;
      vectors.push({signature:ctor?'constructor':signature,
        calldata:rest[1]?.trim()?revertBytes(rest[1]):[],
        ...(canonicalOnly ? {canonicalOnly:true} : {}),
        inputTypes:(d.inputs ?? []).map(abiType),outputTypes:(d.outputs ?? []).map(abiType),
        failure,expectedBytes:payload?revertBytes(payload):[]});
    }
    if(!vectors.length) throw scalarError;
    return vectors;
  }
}

function compiler(path) {
  if (sha(readFileSync(path)) !== COMPILER_SHA) throw new Error('wrong Solidity 0.8.38 compiler SHA-256');
  const solc = createRequire(import.meta.url)(resolve(path));
  if (solc.cwrap('solidity_version','string',[])() !== VERSION) throw new Error('wrong compiler version');
  const compile = solc.cwrap('solidity_compile','string',['string','number','number']);
  return input => JSON.parse(compile(JSON.stringify(input),0,0));
}

function prepare(entry, directory, compile, work) {
  const path = entry.path;
  const syntax = path.startsWith('test/libsolidity/syntaxTests/');
  const semantic = path.startsWith('test/libsolidity/semanticTests/');
  const stage = syntax ? 'compiler-diagnostics' : semantic ? 'lean-runtime' : 'upstream-harness';
  if (!syntax && !semantic) return {path,stage,status:'blocked',reason:'upstream suite has no adapter in this Lean repository'};
  const bytes = readFileSync(join(directory,path));
  let text;
  try {text = new TextDecoder('utf-8',{fatal:true,ignoreBOM:true}).decode(bytes);}
  catch {return {path,stage,status:'blocked',reason:'invalid UTF-8 fixture needs the native byte-oriented compiler harness'};}
  let fixture;
  try {fixture = parseFixture(text);}
  catch(e) {return {path,stage,status:'blocked',reason:e.message};}
  const allowed = syntax ? ['EVMVersion','compileViaYul','stopAfter','optimize-yul','experimental'] :
    ['EVMVersion','compileViaYul','compileViaSSACFG','ABIEncoderV1Only'];
  for (const key of Object.keys(fixture.settings)) {
    if (!allowed.includes(key) || key === 'experimental' || (key === 'stopAfter' && fixture.settings[key] === 'parsing'))
      return {path,stage,status:'blocked',reason:'unadapted fixture setting: '+key+'='+fixture.settings[key]};
  }
  try {
    if (!evmCompatible(fixture.settings.EVMVersion))
      return {path,stage,status:'blocked',reason:'upstream EVM constraint excludes osaka: '+fixture.settings.EVMVersion};
  } catch(e) {return {path,stage,status:'blocked',reason:e.message};}
  const viaIR = fixture.settings.compileViaYul === 'true';
  if (fixture.settings.compileViaYul && !['true','false','also'].includes(fixture.settings.compileViaYul))
    return {path,stage,status:'blocked',reason:'unsupported pipeline setting: '+fixture.settings.compileViaYul};
  const offsets = new Map();
  const sources = Object.fromEntries([...fixture.sources].map(([name,source])=>{
    const content = withPreamble(source, semantic && fixture.settings.ABIEncoderV1Only === 'true');
    offsets.set(name, Buffer.byteLength(content)-Buffer.byteLength(source));
    return [name,{content}];
  }));
  const settings = {viaIR,evmVersion:'osaka',optimizer:{enabled:syntax && fixture.settings['optimize-yul'] !== 'false',runs:200},
    libraries:{},remappings:[],outputSelection:{'*':{'':['ast']}}};
  if (syntax && fixture.settings.stopAfter !== 'analysis') settings.outputSelection['*']['*']=['evm.bytecode.object'];
  if (semantic) settings.outputSelection['*']['*']=['abi'];
  if (syntax) settings.metadata = {appendCBOR:false,bytecodeHash:'none'};
  let out;
  try {out=compile({language:'Solidity',sources,settings});}
  catch(e) {return {path,stage,status:'blocked',reason:'compiler execution error: '+e.message};}
  if (syntax) {
    const actual = diagnosticLines(out.errors ?? [], offsets);
    const expected = fixture.expectations.filter(line=>line.trim()).map(line=>line.trimStart());
    const working = JSON.stringify(actual) === JSON.stringify(expected);
    return {path,stage,status:working ? 'working' : 'broken',reason:working ? 'exact upstream diagnostics match (pinned solc reference)' : 'compiler diagnostic expectation mismatch',
      ...(working ? {diagnostics:actual.length} : {expected,actual})};
  }
  const errors = (out.errors ?? []).filter(e=>e.severity === 'error');
  if (errors.length) return {path,stage,status:'blocked',reason:'semantic fixture needs an unadapted compiler configuration',diagnostics:errors.map(e=>e.formattedMessage)};
  if (fixture.sources.size !== 1) return {path,stage:'lean-import',status:'blocked',reason:'multi-source frontend import requires compilation-unit provenance'};
  const ast = out.sources?.[fixture.mainSource]?.ast;
  const candidates = ast?.nodes.filter(n=>n.nodeType === 'ContractDefinition' && n.contractKind === 'contract' && !n.abstract) ?? [];
  const contract = candidates.at(-1);
  if (!contract) return {path,stage,status:'blocked',reason:'no concrete deployment contract'};
  let blocked, vectors;
  try {vectors=semanticVectors({...fixture,abiCoderV1:ast.nodes.some(n=>n.nodeType==='PragmaDirective' &&
    n.literals?.[0]==='abicoder' && n.literals?.[1]==='v1')},out.contracts[fixture.mainSource][contract.name].abi);}
  catch(e) {blocked=e.message;}
  // Context and cross-contract behavior require the upstream EVM host. Refuse
  // rather than choose arbitrary values for its transaction/block environment.
  const hostBehavior = node => {
    if (!node || typeof node !== 'object') return false;
    if (node.nodeType === 'Identifier' && node.name === 'this') return true;
    if (node.nodeType === 'MemberAccess' && node.expression?.nodeType === 'Identifier' &&
        ['msg','block','tx'].includes(node.expression.name)) return true;
    if (node.nodeType === 'NewExpression' && node.typeName?.typeDescriptions?.typeString?.startsWith('contract ')) return true;
    if (node.nodeType === 'FunctionCall' && /\bexternal\b/.test(node.expression?.typeDescriptions?.typeString ?? '')) return true;
    if (node.nodeType === 'FunctionCall' && /^t_function_(?:barecall|send|transfer|delegatecall|baredelegatecall|staticcall|barestaticcall)/.test(
      node.expression?.typeDescriptions?.typeIdentifier ?? '')) return true;
    return Object.values(node).some(value=>Array.isArray(value) ? value.some(hostBehavior) : hostBehavior(value));
  };
  const hasAssembly = node => node && typeof node === 'object' &&
    (node.nodeType === 'InlineAssembly' || Object.values(node).some(v=>Array.isArray(v)?v.some(hasAssembly):hasAssembly(v)));
  if (vectors?.some(v=>v.calldata) && hasAssembly(ast))
    blocked='raw ABI replay with physical calldata/memory assembly not adapted';
  const context = hostBehavior(ast);
  const hostContext = context ? (directSelfTryContext(ast, contract) ?? creationTryContext(ast, contract)) : null;
  if (context && !hostContext) blocked='transaction/block/self-address or cross-contract host behavior not adapted';
  // Import success alone cannot discharge a vector we cannot execute.
  if (blocked) return {path,stage,status:'blocked',reason:blocked};
  const pipelines=runtimePipelines(fixture.settings);
  const source = sources[fixture.mainSource].content;
  const normalise = value => {
    if (Array.isArray(value)) return value.map(normalise);
    if (!value || typeof value !== 'object') return value;
    const result = {};
    for (const [key,item] of Object.entries(value)) {
      result[key] = ['referencedDeclaration','scope','superFunction'].includes(key) && Number.isInteger(item) && item >= 2**31 ? item-2**32 : normalise(item);
    }
    if (typeof value.src === 'string') result.line=Buffer.from(source).subarray(0,Number(value.src.split(':')[0])).toString().split('\n').length;
    return result;
  };
  const recordedSettings = {...settings,outputSelection:{'*':{'':['ast']}}};
  const data = {header:{solcVersion:VERSION,sourceSha256:sha(Buffer.from(source)),solkeyCommit:'',source:path,
    provenanceVersion:1,compilerFile:'soljson-v0.8.38+commit.1835d247.js',compilerSha256:COMPILER_SHA,
    validationStage:'analysis',settings:recordedSettings,
    acceptedPragmas:ast.nodes.filter(n=>n.nodeType === 'PragmaDirective').map(n=>n.literals)}, ast:normalise(ast)};
  const jobs=[];
  for (const pipeline of pipelines) {
    const variant=structuredClone(data);
    variant.header.settings.viaIR=pipeline === 'viaIR';
    if (variant.header.settings.viaIR !== settings.viaIR) {
      const other=compile({language:'Solidity',sources,settings:{...settings,viaIR:variant.header.settings.viaIR}});
      const errors=(other.errors ?? []).filter(e=>e.severity==='error');
      if (errors.length) return {path,stage,status:'blocked',reason:'alternate source mode needs unadapted compiler settings',diagnostics:errors.map(e=>e.formattedMessage)};
      variant.ast=normalise(other.sources[fixture.mainSource].ast);
    }
    try {
      const code=compilerCode(compile,sources,{...settings,viaIR:pipeline==='viaIR'},
        variant.ast,{compilerSha256:COMPILER_SHA,sourceSha256:variant.header.sourceSha256});
      if (code) variant.compilerCode=code;
    } catch(e) {return {path,stage,status:'blocked',reason:'static compiler-code materialization failed: '+e.message};}
    const fixturePath=join(work,sha(path+'#'+pipeline).slice(0,24)+'.ast.json');
    save(fixturePath,variant);
    jobs.push({path,pipeline,requiredPipelines:pipelines,contract:contract.name,fixture:fixturePath,vectors,...(hostContext ? {hostContext,...(hostContext.kind === 'creation-try-source' ? {requiresCreationContext:true} : {requiresSelfContext:true})} : {})});
  }
  return {jobs};
}

export function partition(results) {
  const groups = {working:[],broken:[],blocked:[]};
  for (const row of results) {
    if (!Object.hasOwn(groups,row.status)) throw new Error('unclassified result: '+row.path);
    groups[row.status].push(row);
  }
  return groups;
}

export function combineVariants(path, required, variants) {
  const complete=required.every(pipeline=>variants.some(row=>row.pipeline===pipeline));
  const broken=variants.find(row=>row.status==='broken');
  const blocked=variants.find(row=>row.status==='blocked');
  const status=broken ? 'broken' : complete && !blocked && variants.every(row=>row.status==='working') ? 'working' : 'blocked';
  return {path,stage:'lean-runtime',status,
    reason:broken?.reason ?? blocked?.reason ?? (status==='working' ? 'functional runtime vectors match in every required source evaluation mode' : 'required evaluation mode did not complete'),
    requiredPipelines:required,variants};
}

function modelDigest() {
  const files=[];
  function walk(dir) {for (const name of readdirSync(dir)) {
    const path=join(dir,name);
    if (statSync(path).isDirectory()) walk(path); else if (path.endsWith('.lean')) files.push(path);
  }}
  walk(join(ROOT,'Solidity'));
  return sha(Buffer.concat(files.sort().flatMap(path=>[Buffer.from(relative(ROOT,path)+'\0'),readFileSync(path)])));
}

function writeReports(output, metadata, results, total, files) {
  const sorted=[...results.values()].sort((a,b)=>a.path.localeCompare(b.path));
  const groups=partition(sorted);
  const stages={};
  for (const row of sorted) {stages[row.stage] ??= {working:0,broken:0,blocked:0}; stages[row.stage][row.status]++;}
  const summary={...metadata,totalFixtureFiles:total,completedFixtureFiles:sorted.length,complete:sorted.length===total,
    counts:Object.fromEntries(Object.entries(groups).map(([k,v])=>[k,v.length])),stages};
  save(join(output,'summary.json'),summary);
  save(join(output,'results.json'),{metadata,results:sorted});
  for (const [name,rows] of Object.entries(groups)) {
    save(join(output,name+'.json'),rows);
    writeFileSync(join(output,name+'.txt'),rows.map(r=>`${r.path}\t${r.stage}\t${r.reason}`).join('\n')+'\n');
  }
  // Include native suites and extensionless command-line assets in a separate
  // exhaustive ledger. A C++ source can contain many tests; it is not one case.
  save(join(output,'file-coverage.json'),files.map(file=>{
    const row=results.get(file.path);
    return {path:file.path,sha256:file.sha256,bytes:file.bytes,
      role:row ? 'fixture-or-reference' : /\.(cpp|sh|py|js)$/.test(file.path) || file.path.includes('/cmdlineTests/') ? 'native-suite-or-harness' : 'support-file',
      status:row?.status ?? 'blocked',
      reason:row?.reason ?? 'preserved; native upstream harness/build or resource consumer has not been ported'};
  }));
  return summary;
}

async function main(args) {
  const command=args.shift();
  if (command === 'verify') {
    const {manifest}=verifySnapshot();
    console.log(`Verified ${manifest.files.length} files at ${manifest.commit}`);return;
  }
  if (command !== 'run') throw new Error('usage: solidity-upstream.mjs verify | run --compiler FILE [--out DIR] [--filter TEXT] [--resume] [--timeout-ms N] [--batch-size N]');
  const options={out:join(SNAPSHOT,'results'),timeoutMs:120000,batchSize:16};
  for (let i=0;i<args.length;i++) {
    if (args[i] === '--resume') options.resume=true;
    else {
      const keys={'--compiler':'compiler','--out':'out','--filter':'filter','--timeout-ms':'timeoutMs','--batch-size':'batchSize'};
      const key=keys[args[i]];
      if (!key || !args[i+1]) throw new Error('unknown/missing option: '+args[i]);
      options[key]=['timeoutMs','batchSize'].includes(key) ? Number(args[++i]) : args[++i];
    }
  }
  if (!options.compiler) throw new Error('--compiler is required');
  for (const key of ['timeoutMs','batchSize']) if (!Number.isSafeInteger(options[key]) || options[key]<=0) throw new Error('invalid '+key);
  const compile=compiler(options.compiler);
  const {manifest,directory}=verifySnapshot();
  const files=manifest.files.filter(f=>/\.(sol|yul|json|stack|ssa|asm|asmjson)$/.test(f.path) && (!options.filter || f.path.includes(options.filter)));
  if (!files.length) throw new Error('no upstream fixture files selected');
  const work=mkdtempSync(join(ROOT,'.lake/upstream/work-'));
  const metadata={version:1,commit:PIN,compiler:VERSION,compilerSha256:COMPILER_SHA,
    archiveSha256:manifest.archiveSha256,runnerSha256:sha(readFileSync(fileURLToPath(import.meta.url))),
    compilerCodeAdapterSha256:sha(readFileSync(join(ROOT,'scripts/solc-code.mjs'))),
    selfTryAdapterSha256:sha(readFileSync(join(ROOT,'scripts/self-try-adapter.mjs'))),
    creationTryAdapterSha256:sha(readFileSync(join(ROOT,'scripts/creation-try-adapter.mjs'))),
    modelSha256:modelDigest(),evmVersion:'osaka',loopFuel:1000,
    scope:'Pinned-solc reference diagnostics; typed Lean observations for supported scalar/canonical-prefix ABI vectors, v2 primitive entry checks and retained failure bytes in required legacy/viaIR source modes. Generated EVM/SSA, gas, logs and the native C++ harness are not tested.',
    snapshotFiles:manifest.files.length,filter:options.filter ?? null,timeoutMs:options.timeoutMs,batchSize:options.batchSize};
  const results=new Map();
  const variants=new Map();
  const output=resolve(options.out);mkdirSync(output,{recursive:true});
  if (options.resume && existsSync(join(output,'results.json'))) {
    const previous=json(join(output,'results.json'));
    if (JSON.stringify(previous.metadata) !== JSON.stringify(metadata)) throw new Error('resume provenance differs; use a new output directory');
    for (const row of previous.results) {
      results.set(row.path,row);
      if (row.variants) variants.set(row.path,row.variants);
    }
  }
  // Finish the one-time build before interpreting a failure as a corpus result.
  runTool('lake',['build','Solidity.Tools.Upstream'],Math.max(options.timeoutMs,300000));
  const jobs=[];
  for (const [i,entry] of files.entries()) {
    const previous=results.get(entry.path);
    if (previous && (!previous.requiredPipelines || previous.requiredPipelines.every(pipeline=>
      previous.variants?.some(row=>row.pipeline===pipeline)))) continue;
    let row;
    try {row=prepare(entry,directory,compile,work);}
    catch(e) {row={path:entry.path,stage:'adapter',status:'blocked',reason:e.message};}
    if (row.jobs) jobs.push(...row.jobs.filter(job=>
      !variants.get(job.path)?.some(row=>row.pipeline===job.pipeline)));
    else results.set(row.path,row);
    if (i%100===0) {writeReports(output,metadata,results,files.length,manifest.files);console.log(`Prepared ${i+1}/${files.length}; ${jobs.length} Lean replay jobs`);}
  }
  writeReports(output,metadata,results,files.length,manifest.files);
  for (let first=0;first<jobs.length;first+=options.batchSize) {
    const batch=jobs.slice(first,first+options.batchSize);
    const input=join(work,'batch.json'), checkpoint=join(work,'checkpoint.json'), wrapper=join(work,'Batch.lean');
    save(input,batch);save(checkpoint,[]);
    writeFileSync(wrapper,`import Solidity.Tools.Upstream\n#upstream_batch ${JSON.stringify(input)} to ${JSON.stringify(checkpoint)}\n`);
    let failure;
    try {runTool('lake',['--quiet','--no-build','lean',wrapper,'--','--tstack=131072'],options.timeoutMs);}
    catch(e) {failure=e;}
    const retained=json(checkpoint);
    for (const job of batch) {
      const found=retained.find(r=>r.path===job.path && r.pipeline===job.pipeline);
      const rows=variants.get(job.path) ?? [];
      rows.push(found ?? {path:job.path,pipeline:job.pipeline,status:'blocked',
        reason:'Lean process ended before checkpoint',tool:failure?.tool,diagnostic:failure?.message?.slice(-3000)});
      variants.set(job.path,rows);
      results.set(job.path,combineVariants(job.path,job.requiredPipelines,rows));
    }
    const summary=writeReports(output,metadata,results,files.length,manifest.files);
    console.log(`Lean ${Math.min(first+batch.length,jobs.length)}/${jobs.length}; ${JSON.stringify(summary.counts)}`);
  }
  const summary=writeReports(output,metadata,results,files.length,manifest.files);
  console.log(JSON.stringify(summary,null,2));
  process.exitCode=summary.counts.broken || summary.counts.blocked ? 1 : 0;
}

if (process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url))
  main(process.argv.slice(2)).catch(e=>{console.error(e.stack);process.exitCode=2;});
