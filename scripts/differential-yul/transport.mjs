/** Adapter for the reviewed StatefulImport.driver protocol. No semantic fallback.
 * The executable is supplied explicitly after the producer is integrated. */
import {execFile} from 'node:child_process';
import {promisify} from 'node:util';
import {mkdtemp, writeFile, rm} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
const exec = promisify(execFile);
const word = x => typeof x === 'string' && /^(0|[1-9][0-9]*)$/.test(x) && BigInt(x) < 2n**256n;

/** Ignore comments when selecting the unique deployed object. The checked Lean
 * importer still validates the entire original IR and the explicit object path.
 * Reject unfamiliar nesting/ambiguous names instead of selecting constructor code. */
export function runtimePath(ir) {
  if (typeof ir !== 'string') throw Error('IR must be text');
  const tokens = ir.match(/\/\*[\s\S]*?\*\/|\/\/[^\n]*|"(?:\\.|[^"\\])*"|[A-Za-z_$][\w$]*|[{}]|[^\s]/g) ?? [];
  const clean = tokens.filter(t => !t.startsWith('//') && !t.startsWith('/*'));
  let depth = 0;
  const found = [];
  for (let i = 0; i < clean.length; i++) {
    if (clean[i] === 'object' && clean[i+1]?.startsWith('"') && clean[i+2] === '{') {
      const name = clean[i+1].slice(1,-1);
      if (name.endsWith('_deployed')) {
        if (depth !== 1 || !/^[A-Za-z_$][\w$]*_deployed$/.test(name)) throw Error('unsupported runtime object path');
        found.push(name);
      }
    }
    if (clean[i] === '{') depth++;
    if (clean[i] === '}') depth--;
    if (depth < 0) throw Error('unbalanced IR');
  }
  if (depth !== 0 || found.length !== 1) throw Error('expected one direct deployed runtime object');
  return found[0];
}

export function decode(stdout) {
  const value = JSON.parse(stdout);
  if (value?.status === 'error' && typeof value.error === 'string' && value.error.length)
    return {status:'blocked',reason:value.error};
  if (value?.status !== 'ok' || typeof value.reverted !== 'boolean' ||
      typeof value.returnData !== 'string' || !/^(?:[0-9a-f]{2})*$/.test(value.returnData) ||
      !Array.isArray(value.storage) || value.storage.length !== 2 ||
      value.storage.some((pair,i) => !Array.isArray(pair) || pair.length !== 2 || pair[0] !== String(i) || !word(pair[1])))
    throw Error('malformed stateful driver response');
  return {status:'ok', observation:{failed:value.reverted, returnData:'0x'+value.returnData,
    slots:['0','1'],storage:value.storage.map(pair=>pair[1])}};
}

export function transport({executable, prefix = [], fuel = 10000, outputLimit = 4096,
    timeout = 60000, invoke = exec}) {
  if (typeof executable !== 'string' || !executable.length || !Array.isArray(prefix) || prefix.some(x=>typeof x!=='string') ||
      [fuel,outputLimit,timeout].some(x=>!Number.isSafeInteger(x)||x<1)) throw Error('invalid transport configuration');
  prefix = [...prefix];
  return async request => {
    if (!/^0x(?:[0-9a-f]{2})*$/.test(request.calldata ?? '') ||
        JSON.stringify(request.slots) !== '["0","1"]' ||
        !Array.isArray(request.initialStorage) || request.initialStorage.length !== 2 || !request.initialStorage.every(word))
      throw Error('invalid stateful execution request');
    const path = runtimePath(request.ir);
    const dir = await mkdtemp(join(tmpdir(),'differential-yul-'));
    try {
      const file = join(dir,'runtime.yul');
      await writeFile(file,request.ir,{flag:'wx'});
      const args = [...prefix,file,path,String(fuel),String(outputLimit),request.calldata.slice(2),
        request.initialStorage.map((v,i)=>i+'='+v).join(',')];
      let result;
      try { result = await invoke(executable,args,{timeout,maxBuffer:Math.max(65536,outputLimit*2+4096),env:{...process.env,LEAN_NUM_THREADS:'1'}}); }
      catch (error) {
        // A nonzero process exit can report a refusal, but never success.
        if (error.code === 1 && !error.killed && !error.signal) {
          try { const refused = decode(error.stdout); if (refused.status === 'blocked') return refused; } catch {}
        }
        return {status:'blocked',reason:'driver process failed: '+String(error.message ?? error)};
      }
      return decode(result.stdout);
    } finally { await rm(dir,{recursive:true,force:true}); }
  };
}
