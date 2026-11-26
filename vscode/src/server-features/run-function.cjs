'use strict';
const fs = require('node:fs');
const path = require('node:path');
const {spawn} = require('node:child_process');
const {pathToFileURL} = require('node:url');
const projects = require('../project.cjs');
const {terminateTree} = require('../backend.cjs');
const {trackChild, waitForClose} = require('../child-lifetime.cjs');
const {byteRange} = require('../language-services.cjs');
const fail = (message, code = -32602) => Object.assign(new Error(message), {code});

// Wire contract, v1: discover {textDocument:{uri,version}} -> {functions:[
// {id,contract,signature,parameters:[{name,type}],range}],sourceHash}.
// Run adds {sourceHash,functionId,args:[ABI JSON values]}; integers are decimal
// strings (never JS numbers). Reply: {status,returns,code,logs,storageWrites,
// text?,limitations?}. null means unavailable, [] means observed empty.
// A replacement injected runBackend(request,{signal}) must preserve this shape.
// This is concrete typed-model execution, not kernel proof or bytecode replay.
function argument(type, text) {
  if(type==='address payable')type='address';
  const array = /^(.*)\[(\d*)\]$/.exec(type);
  if(array){
    const values = typeof text === 'string' ? (()=>{try{return JSON.parse(text);}catch{throw fail('Expected a JSON array');}})() : text;
    if(!Array.isArray(values) || array[2] && values.length!==Number(array[2]))throw fail(`Expected ${type} JSON array`);
    return values.map(value=>argument(array[1],value));
  }
  if(type==='string'){
    if(typeof text!=='string')throw fail('Expected a string');return text;
  }
  const bytes=/^bytes(\d*)$/.exec(type);
  if(bytes){
    const size=bytes[1]?Number(bytes[1]):null;
    if(size!==null && (size<1 || size>32) || typeof text!=='string' || !/^0x(?:[\da-fA-F]{2})*$/.test(text) || size!==null && text.length!==2+size*2)throw fail(`Expected ${type} as 0x-prefixed bytes`);
    return text;
  }
  if (type === 'bool') {
    if (text !== 'true' && text !== 'false' && typeof text!=='boolean') throw fail('Expected true or false');
    return text === 'true' || text === true;
  }
  const match = /^(u?int)(\d*)$/.exec(type);
  if (match || type === 'address') {
    const bits = type === 'address' ? 160 : Number(match[2] || 256);
    if (bits < 8 || bits > 256 || bits % 8) throw fail('Invalid ABI integer width');
    if (typeof text !== 'string' || !(type==='address' && /^0x[\da-fA-F]{40}$/.test(text)) && !/^-?\d+$/.test(text)) throw fail('Expected a decimal integer (quote integers in JSON arrays)');
    const n = BigInt(text), signed = match?.[1] === 'int';
    const limit = 1n << BigInt(bits - (signed ? 1 : 0));
    if (n < (signed ? -limit : 0n) || n >= limit) throw fail(`Value outside ${type}`);
    return n.toString();
  }
  throw fail(`Unsupported ABI input type ${type}`);
}
function supported(type) {
  if(type==='address payable')type='address';
  const array=/^(.*)\[\d*\]$/.exec(type);
  return array ? supported(array[1]) : /^(bool|string|bytes(?:[1-9]|[12]\d|3[0-2])?|address|u?int(?:\d+)?)$/.test(type);
}
function functions(compiled, text) {
  if(!compiled)throw fail('Fix compiler errors before running a function');
  const ast = compiled.primaryAst || compiled.fixture?.ast || compiled.rawAst;
  return (ast?.nodes || []).filter(c => c.nodeType === 'ContractDefinition').flatMap(c =>
    (c.nodes || []).filter(f => f.nodeType === 'FunctionDefinition' && f.kind === 'function' && f.implemented !== false).map(f => {
      const parameters = f.parameters.parameters.map(p => ({name:p.name, type:p.typeDescriptions.typeString.replace(/ (storage|memory|calldata)( ref| pointer)?$/, '')}));
      return {id:`${c.id}:${f.id}`, contract:c.name, signature:`${f.name}(${parameters.map(p => p.type).join(',')})`, parameters, range:byteRange(text,f.src)};
    }));
}
function outcome(report) {
  if (report.errors?.length) throw fail(report.errors.map(e => e.reason).join('\n'));
  if (report.results?.length !== 1) throw fail('Concrete runner must return exactly one result');
  const row = report.results[0];
  if (!['ok','revert','panic','diverge'].includes(row.status)) throw fail(row.reason || row.text || `Runner returned ${row.status}`);
  const text = row.text || '';
  return {status:row.status, returns:text.split('\n').filter(l => l.startsWith('returns ')),
    code:null,
    logs:null, storageWrites:null, text,
    limitations:['Numeric panic/revert codes are unavailable from the typed-model report.', 'Emitted logs and written EVM slots are unavailable from Solidity.Frontend.Cli/runReport; storage text is final typed storage, not a write trace.', 'Fresh model state; constructor not executed.']};
}

// Reuse the existing runSolidityTests action=run entry point in a bounded child.
// Mirror the existing project snapshot so dirty buffers and imports stay exact.
async function runBackend(request, {signal, service}) {
  if(request.args.some((_,i)=>! /^(bool|u?int\d*|address(?: payable)?)$/.test(request.function.parameters[i].type)))throw fail('Solidity.Frontend.Cli/runRequest currently accepts only bool and integer-valued arguments; this ABI type needs a backend extension');
  const directory = fs.mkdtempSync(path.join(service.directory,'run-'));
  let child, closed, timer, registration;
  const cancel = () => {if(child)terminateTree(child);};
  try {
    for (const [name,source] of Object.entries(request.project.sources)) {
      const target = path.resolve(directory,name);
      if (path.relative(directory,target).startsWith('..') || path.isAbsolute(name)) throw fail('Snapshot source outside execution directory');
      fs.mkdirSync(path.dirname(target),{recursive:true}); fs.writeFileSync(target,source.content);
    }
    if (signal.aborted) throw fail('Run cancelled',-32800);
    child = spawn(process.execPath,[__filename,'--runner'],{cwd:service.root,detached:process.platform !== 'win32',stdio:['pipe','pipe','pipe'],windowsHide:true,env:{...process.env,LEAN_NUM_THREADS:'1'}});
    child.ownedGroup = process.platform !== 'win32';
    child.processBirth = require('../process-state.cjs').processState(child.pid)?.birth;
    closed = trackChild(child);
    signal.addEventListener('abort',cancel,{once:true});
    let stdout = '', stderr = '', overflow = false, expired = false;
    const result = new Promise((resolve,reject) => {
      child.on('error',reject); child.stdin.on('error',reject);
      child.stdout.on('data',bytes => {stdout += bytes; if (Buffer.byteLength(stdout)>8*1024*1024){overflow=true;cancel();}});
      child.stderr.on('data',bytes => {stderr=(stderr+bytes).slice(-4000);});
      child.on('close',code => {
        if(signal.aborted)return reject(fail('Run cancelled',-32800));
        if(expired||overflow)return reject(fail(expired?'Run timed out':'Run output limit exceeded'));
        if(code!==0)return reject(fail(`Concrete runner failed: ${stderr}`));
        try{resolve(outcome(JSON.parse(stdout)));}catch(error){reject(error);}
      });
    });
    // Avoid an unhandled rejection while ownership registration is pending.
    result.catch(()=>{});
    timer=setTimeout(()=>{expired=true;cancel();},service.settings.timeoutMs || 60000);
    registration=true; await service.registerOwned('proof',child);
    if(signal.aborted)throw fail('Run cancelled',-32800);
    child.stdin.end(JSON.stringify({root:service.root,source:path.join(directory,request.project.mainSource),
      options:{action:'run',contract:request.function.contract,function:request.function.signature,args:request.args,state:{},
        projectRoot:directory,remappings:request.project.remappings,timeoutMs:service.settings.timeoutMs || 60000}}));
    return await result;
  } finally {
    clearTimeout(timer); signal.removeEventListener('abort',cancel);
    if(child){cancel();await waitForClose(child,{closed,kill:true});if(registration)service.releaseOwned('proof',child);}
    fs.rmSync(directory,{recursive:true,force:true});
  }
}
function register(server, injected = runBackend) {
  const service=server.service, active=new Set(),pending=new Set(); let disposed=false, running=false;
  const handle = async (execute,params,id) => {
    const controller=new AbortController(); active.add(controller); service.requests.set(id,controller); let ownsRun=false;
    try {
      if(disposed)throw fail('Feature stopped',-32800);
      const doc=service.docs.get(params?.textDocument?.uri),version=params?.textDocument?.version;
      if(!doc || !Number.isInteger(version) || version!==doc.version)throw fail('Document changed',-32801);
      const text=doc.text, generation=service.generation;
      const current=() => {
        if(controller.signal.aborted)throw fail('Run cancelled',-32800);
        if(!service.current(doc,version,generation)||doc.text!==text)throw fail('Document changed',-32801);
      };
      await service.language('textDocument/documentSymbol',params,controller.signal); current();
      const project=projects.snapshot(doc.path,text,service.settings,service.projectDocuments());
      const rows=functions(doc.compiled,text),sourceHash=projects.hash(text);
      if(!execute)return {functions:rows,sourceHash};
      if(running)throw fail('Another concrete run is active; retry when it finishes');
      running=true;ownsRun=true;
      if(doc.compiled.proofGap)throw fail(doc.compiled.proofGap);
      if(params.sourceHash!==sourceHash)throw fail('Document changed',-32801);
      const fn=rows.find(f=>f.id===params.functionId);
      if(!fn || !Array.isArray(params.args) || params.args.length!==fn.parameters.length)throw fail('Invalid function or argument count');
      const args=fn.parameters.map((p,i)=>argument(p.type,params.args[i]));
      const result=await injected({version:1,sourceHash,project,function:fn,args},{signal:controller.signal,service});
      current(); if(!projects.current(project,service.projectDocuments(),true))throw fail('Project changed',-32801);
      return result;
    } finally {if(ownsRun)running=false;active.delete(controller);service.requests.delete(id);}
  };
  const handler=execute=>(params,id)=>{const task=handle(execute,params,id);pending.add(task);task.then(()=>pending.delete(task),()=>pending.delete(task));return task;};
  server.onRequest('solidityLean/runFunctions',handler(false));
  server.onRequest('solidityLean/runFunction',handler(true));
  return {async dispose(){disposed=true;for(const controller of active)controller.abort();await Promise.allSettled([...pending]);}};
}
module.exports={register,argument,supported,functions,outcome,runBackend};
if(require.main===module && process.argv[2]==='--runner') {
  let input='';process.stdin.setEncoding('utf8');process.stdin.on('data',chunk=>{input+=chunk;});
  process.stdin.on('end',async()=>{try{const request=JSON.parse(input);
    const {runSolidityTests}=await import(pathToFileURL(path.join(request.root,'scripts/test-solidity.mjs')).href);
    process.stdout.write(JSON.stringify(runSolidityTests([request.source],request.options)));
  }catch(error){process.stderr.write(error.message);process.exitCode=1;}});
}
