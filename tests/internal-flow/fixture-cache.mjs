#!/usr/bin/env node
// Compiled fixture reuse in the ONE existing Lake tree. Not a full-source gate.
import {readFileSync,writeFileSync,mkdirSync,existsSync,readdirSync,realpathSync,statSync,openSync,writeSync,fsyncSync,closeSync} from "node:fs";
import {resolve,basename} from "node:path";
import {createHash,randomUUID} from "node:crypto";
import {spawn} from "node:child_process";
import {pathToFileURL} from "node:url";
import {freshObjectDigest,withObjectDigests} from "./exact-byte-digest.mjs";
const pinsFile="tests/internal-flow/fixture-axiom-pins.json";
const registry=JSON.parse(readFileSync(pinsFile,"utf8"));
const hash=p=>createHash("sha256").update(readFileSync(p)).digest("hex");
export function scanFixtureImports(text) {
  let clean="", depth=0, quoted=false;
  for(let i=0;i<text.length;i++) {
    const pair=text.slice(i,i+2),c=text[i];
    if(depth) {
      if(pair==="/-") {depth++;i++;}
      else if(pair==="-/") {depth--;i++;}
      else if(c==="\n") clean+="\n";
    } else if(quoted) {
      if(c==="\\") i++;
      else if(c==='"') quoted=false;
      else if(c==="\n") clean+="\n";
    } else if(pair==="/-") {depth=1;i++;}
    else if(pair==="--") {while(i<text.length && text[i]!=="\n") i++;clean+="\n";}
    else if(c==='"') quoted=true;
    else clean+=c;
  }
  if(depth || quoted) throw new Error("unclosed source comment/string");
  return [...clean.matchAll(/^\s*import\s+([^\n]+)/gm)].flatMap(m=>m[1].trim().split(/\s+/));
}

// Cache only the PURE parse of freshly-read exact text, never file bytes,
// hashes, keys, mtimes or toolchain snapshots. Each traversal consumes its root
// pending array, so every caller receives a fresh mutable copy.
const importMemo = new Map();
export function imports(text) {
  let parsed=importMemo.get(text);
  if(parsed===undefined) {
    parsed=Object.freeze(scanFixtureImports(text));
    importMemo.set(text,parsed);
  }
  return parsed.slice();
}

// The actual complete toolchain is read, never inferred from mtimes/version.
function toolchainInputs() {
  const inputs={};
  const toolchain=process.env.LEAN_SYSROOT;
  if(!toolchain) throw new Error("LEAN_SYSROOT must identify the actual capped toolchain");
  // In the authorized wrapper /opt/lean-real is the immutable actual compiler.
  const binary=existsSync("/opt/lean-real/bin/lean")?"/opt/lean-real/bin/lean":`${toolchain}/bin/lean`;
  inputs["compiler-binary"]=hash(binary);
  // Bind the COMPLETE actual toolchain, including transitive .olean modules,
  // IR and shared runtime libraries; root .olean/version hashes are insufficient.
  const toolRoot=existsSync("/opt/lean-real/bin/lean")?"/opt/lean-real":toolchain;
  const files=[], directories=[""];
  while(directories.length) {
    const rel=directories.pop();
    for(const entry of readdirSync(`${toolRoot}/${rel}`,{withFileTypes:true})) {
      const child=rel?`${rel}/${entry.name}`:entry.name;
      if(statSync(`${toolRoot}/${child}`).isDirectory()) directories.push(child);
      else files.push(child);
    }
  }
  const byRealPath=new Map();
  for(const rel of files.sort()) {
    const path=realpathSync(`${toolRoot}/${rel}`);
    if(!byRealPath.has(path)) byRealPath.set(path,hash(path));
    inputs["toolchain/"+rel]=byRealPath.get(path);
  }

  return inputs;
}

// Production traversal is serial and stops at the first failed fixture.
// Exported solely to test the same traversal without substituting mock gates.
export function visitFixtures(files,check) {
  const results=[];
  for(const file of files) results.push(check(file));
  return results;
}
export function requireSameToolchain(before,after) {
  if(JSON.stringify(before)!==JSON.stringify(after)) throw new Error("toolchain changed during complete fixture batch");
}
// Audit records are not certificates. A start is explicitly unfinished until
// an observed return/error supplies a terminal record; SIGKILL cannot invent one.
export class StageJournal {
  constructor(out) { this.path=`${out}/fixture-stages.jsonl`; this.run=randomUUID(); this.next=0; this.active=[]; }
  record(event,data={}) {
    const row={...data,run:this.run,pid:process.pid,event,monotonic_ns:process.hrtime.bigint().toString(),utc:new Date().toISOString()};
    const fd=openSync(this.path,"a");
    try { writeFileSync(fd,JSON.stringify(row)+"\n"); fsyncSync(fd); } finally { closeSync(fd); }
  }
  start(stage,data) { const frame={id:++this.next,stage,start:process.hrtime.bigint()}; this.record("start",{...data,id:frame.id,parent:this.active.at(-1)?.id??null,stage,state:"unfinished"}); frame.start=process.hrtime.bigint(); this.active.push(frame); return frame; }
  end(frame,error) {
    const data={id:frame.id,stage:frame.stage,elapsed_ns:(process.hrtime.bigint()-frame.start).toString()};
    try { if(error) this.record(error.interrupted?"unfinished":"failure",{...data,state:error.interrupted?"unfinished":"failed",error:{name:error.name,message:error.message,code:error.code,signal:error.signal,exitCode:error.exitCode}});
    else this.record("end",{...data,state:"complete"});
    } finally { if(this.active.pop()!==frame) throw new Error("nonserial stage lifecycle"); }
  }
  measure(stage,fn,data={}) {
    const frame=this.start(stage,data);
    let value; try { value=fn(); if(value?.then) throw new Error("async work in synchronous stage"); } catch(error) { this.end(frame,error); throw error; }
    this.end(frame); return value;
  }
  async measureAsync(stage,fn,data={}) {
    const frame=this.start(stage,data);
    let value; try { value=await fn(); } catch(error) { this.end(frame,error); throw error; }
    this.end(frame); return value;
  }
}
export async function visitFixturesAsync(files,check) {
  const results=[]; for(const file of files) results.push(await check(file)); return results;
}
export const MAX_CHILD_OUTPUT_BYTES=64*1024*1024; // Original spawnSync maxBuffer.
class ChildExit extends Error { constructor(code,signal) { super(`child failed: ${signal??code}`); this.exitCode=code??1; this.signal=signal; } }
class Interrupted extends Error { constructor(signal) { super(`interrupted by ${signal}`); this.interrupted=true; this.signal=signal; } }
export function cliFailure(error) {
  if(error.interrupted) { process.kill(process.pid,error.signal); return; }
  if(!(error instanceof ChildExit)) console.error(error);
  process.exitCode=error.exitCode??1;
}

// Await every child and durably retain RECEIVED chunks, even on outer timeout.
// The completed log retains legacy stdout+stderr grouping for exact parsing.
// No partial/failed result is returned to guards or certificate writers.
export async function run(args,log,journal,limit=MAX_CHILD_OUTPUT_BYTES) {
  if(!Number.isSafeInteger(limit)||limit<0||limit>MAX_CHILD_OUTPUT_BYTES) throw new Error("invalid output bound");
  return journal.measureAsync("child",async()=>{
    const paths={stdout:log+".stdout",stderr:log+".stderr"};
    const fds={}; let child,completion,completed,escalation,problem,interrupted,received=0,retained=0,cleanupError,returned=false;
    const kill=signal=>{if(child?.pid)try{process.kill(-child.pid,signal);}catch(error){if(error.code!=="ESRCH"){cleanupError??=error;problem??=error;}}};
    const stop=()=>{kill("SIGTERM");if(!escalation)escalation=setTimeout(()=>kill("SIGKILL"),1000);};
    const handlers=new Map();
    try {
      for(const signal of ["SIGTERM","SIGINT","SIGHUP"]) {
        const handler=()=>{interrupted??=new Interrupted(signal);try{journal.record("signal",{state:"unfinished",signal,child_pid:child?.pid});}catch(error){problem??=error;}finally{stop();}};
        handlers.set(signal,handler);process.on(signal,handler);
      }
      writeFileSync(log,"");
      fds.stdout=openSync(paths.stdout,"w"); fds.stderr=openSync(paths.stderr,"w");
      child=spawn("lake",args,{stdio:["ignore","pipe","pipe"],detached:true});
      // Observe errors/close BEFORE any fallible setup or journal write.
      completion=new Promise(resolve=>{
        child.on("error",error=>{problem??=error;});
        child.on("close",(code,signal)=>{completed={code,signal};resolve(completed);});
      });
      const consume=(stream,bytes)=>{
        received+=bytes.length;
        const available=Math.max(0,limit-retained),part=bytes.subarray(0,available);
        if(!problem&&part.length)try{let offset=0;while(offset<part.length){const n=writeSync(fds[stream],part,offset,part.length-offset);if(n<=0)throw new Error("short output write");offset+=n;retained+=n;}fsyncSync(fds[stream]);}catch(error){problem=error;stop();}
        if(received>limit&&!problem){problem=Object.assign(new Error("child output exceeds maxBuffer"),{code:"ENOBUFS"});stop();}
      };
      child.stdout.on("data",bytes=>consume("stdout",bytes));
      child.stderr.on("data",bytes=>consume("stderr",bytes));
      for(const stream of [child.stdout,child.stderr])stream.on("error",error=>{problem??=error;stop();});
      journal.record("child-spawn",{state:"unfinished",args,log,...paths,child_pid:child.pid,process_group:child.pid,limit});
      const result=await completion;
      journal.record("child-close",{...result,state:interrupted?"unfinished":problem||result.code!==0?"failed":"returned",received_bytes:received,retained_bytes:retained});
      if(interrupted)throw interrupted;
      if(problem)throw problem;
      fsyncSync(fds.stdout);fsyncSync(fds.stderr);
      const text=readFileSync(paths.stdout,"utf8")+readFileSync(paths.stderr,"utf8");
      writeFileSync(log,text,{flush:true});
      if(result.code!==0)throw new ChildExit(result.code,result.signal);
      returned=true;return text;
    } finally {
      // Only this invocation's private process group; never another session.
      // SIGKILL of the parent itself requires the existing container/supervisor
      // to stop its group, using child-spawn's recorded pgid. No fake end record.
      try {
        kill("SIGKILL");
        if(completion)await completion;
        journal.record("child-group-cleanup",{state:"cleanup-attempted",process_group:child?.pid,signal:"SIGKILL",scope:"only this invocation",observed_close:completed??null,cleanup_error:cleanupError?.code});
      } finally {
        if(escalation)clearTimeout(escalation);
        for(const [signal,handler]of handlers)process.removeListener(signal,handler);
        for(const fd of Object.values(fds))closeSync(fd);
      }
      if(returned&&cleanupError)throw cleanupError;
    }
  },{args,log,stdout:log+".stdout",stderr:log+".stderr",state:"unfinished"});
}

async function fixture(mode,file,out,sharedToolchain=null,batchItems=null,stages=null,preflightOwner=null) {
  if(!["prepare","check"].includes(mode) || !/^tests\/internal-flow\/[A-Za-z][A-Za-z0-9]*\.lean$/.test(file ?? "") || !out?.startsWith("/"))
    throw new Error("usage: fixture-cache.mjs prepare|check tests/internal-flow/Name.lean /absolute/evidence");
  const name=basename(file,".lean"),dir=".lake/build/lib/lean/tests/internal-flow";
  const object=`${dir}/${name}.olean`,manifest=`${dir}/${name}.v12-cache.json`;
  const expected=registry[name];
  if(!expected) throw new Error(`unregistered fixture: ${name}`);
  stages??=new StageJournal(out);
  return stages.measureAsync(`fixture.${mode}.${name}${batchItems?".precheck":""}`,async()=>{

function key() {
  const objectOwner=arguments[0]??null;
  // Source bytes/digests live only for THIS key invocation. Object reuse, if
  // supplied, belongs to a separately closed preflight/postflight owner and
  // still requires a complete fresh read and exact byte equality. Bind parsing
  // and its input hash to the same exact read; no source/hash freshness cache
  // survives the next pre/post key() call. Pure importMemo remains separate.
  const sourceDigests=new Map();
  function readSource(path) {
    const bytes=readFileSync(path);
    sourceDigests.set(path,createHash("sha256").update(bytes).digest("hex"));
    return imports(bytes.toString("utf8"));
  }
  const closure=new Set(), fixtureDeps=new Set(), pending=readSource(file);
  function sourceFor(mod) {
    if(mod.startsWith("Solidity.")) return mod.replaceAll(".","/")+".lean";
    const fixture=/^tests\.«internal-flow»\.([A-Za-z][A-Za-z0-9]*)$/.exec(mod);
    if(fixture && registry[fixture[1]]) {
      fixtureDeps.add(fixture[1]);
      return `tests/internal-flow/${fixture[1]}.lean`;
    }
    if(/^(Init|Lean|Std)(\.|$)/.test(mod)) return null;
    throw new Error(`unsupported fixture dependency ${mod}`);
  }
  while(pending.length) {
    const path=sourceFor(pending.pop());
    if(path===null) continue;
    if(path===file) throw new Error(`cyclic fixture dependency ${file}`);
    if(closure.has(path)) continue;
    closure.add(path);
    pending.push(...readSource(path));
  }
  const inputs={};
  if(!existsSync("tests/internal-flow/exact-byte-digest.mjs")) throw new Error("missing object digest implementation");
  for(const path of [file,pinsFile,expected.guard,"tests/internal-flow/fixture-cache.mjs","tests/internal-flow/exact-byte-digest.mjs","lean-toolchain","lakefile.lean","lakefile.toml","lake-manifest.json"])
    if(existsSync(path)) inputs[path]=sourceDigests.get(path) ?? hash(path);
  Object.assign(inputs, sharedToolchain ?? toolchainInputs());
  for(const path of [...closure].sort()) {
    inputs[path]=sourceDigests.get(path);
    inputs[".lake/build/lib/lean/"+path.slice(0,-5)+".olean"]=freshObjectDigest(".lake/build/lib/lean/"+path.slice(0,-5)+".olean",objectOwner);
  }
  for(const dependency of [...fixtureDeps].sort()) inputs[registry[dependency].guard]=hash(registry[dependency].guard);
  // An imported fixture must have its OWN prior checked source/object binding.
  // Merely hashing an arbitrary object alongside a source is insufficient.
  const dependencies=[];
  for(const dependency of [...fixtureDeps].sort()) {
    const path=`${dir}/${dependency}.v12-cache.json`;
    if(!existsSync(path)) throw new Error(`missing checked fixture dependency ${dependency}`);
    inputs[path]=hash(path);
    dependencies.push([dependency,JSON.parse(readFileSync(path,"utf8"))]);
  }
  for(const [dependency,saved] of dependencies) {
    if(saved.key!==createHash("sha256").update(JSON.stringify(saved.inputs)).digest("hex") ||
       saved.object_sha256!==inputs[`${dir}/${dependency}.olean`] ||
       Object.entries(saved.inputs).some(([path,digest])=>inputs[path]!==digest))
      throw new Error(`stale or altered checked fixture dependency ${dependency}`);
  }
  return {inputs,key:createHash("sha256").update(JSON.stringify(inputs)).digest("hex")};
}
function guard(log) {
  if(/\berror(?:\(|:)/.test(log)) throw new Error("Lean error in actual report");
  const actual={}, reports=[...log.matchAll(/\x27([^\x27]+)\x27 (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)/g)];
  for(const [,n,a] of reports) {
    if(n in actual) throw new Error(`duplicate axiom report ${n}`);
    actual[n]=(a??"").split(",").map(x=>x.trim()).filter(Boolean).sort();
  }
  const normalize=x=>JSON.stringify(Object.fromEntries(Object.entries(x).sort(([a],[b])=>a.localeCompare(b))));
  if(normalize(actual)!==normalize(expected.pins)) throw new Error("missing/extra/changed actual axiom report");
  return reports.length;
}
mkdirSync(dir,{recursive:true});
if(mode==="prepare") {
  // Call only AFTER actual Lake refresh of the full owned/fixture import list.
  const before=stages.measure(`key.before.${name}`,key);
  const log=await run(["env","lean","-j1","--tstack=131072","-o",object,file],`${out}/prepared-${name}.log`,stages);
  const reports=stages.measure(`reports.${name}`,()=>guard(log)), after=stages.measure(`key.after.${name}`,key);
  if(before.key!==after.key) throw new Error("inputs changed during kernel checking");
  writeFileSync(manifest,JSON.stringify({...after,object_sha256:hash(object),reports},null,2)+"\n");
  const result={fixture:file,mode,key:after.key,reports,object}; console.log(JSON.stringify(result)); return result;
} else {
  if(!existsSync(manifest)) throw new Error(`missing checked fixture cache: prepare ${file}`);
  const saved=JSON.parse(readFileSync(manifest,"utf8")), current=stages.measure(`key.before.${name}`,()=>key(preflightOwner));
  if(saved.key!==current.key || JSON.stringify(saved.inputs)!==JSON.stringify(current.inputs) || saved.object_sha256!==hash(object))
    throw new Error(`stale or altered compiled fixture ${file}; run bounded preparation`);
  const harness=`import tests.«internal-flow».${name}\n`+Object.keys(expected.pins).sort().map(n=>`#print axioms ${n}\n`).join("");
  const harnessFile=`.lake/build/${name}-v12-import.lean`;
  writeFileSync(harnessFile,harness);writeFileSync(`${out}/cached-${name}-import.lean`,harness);
  const finish=(log,postflightOwner=null)=>{
  const reports=stages.measure(`reports.${name}`,()=>guard(log));
  // Recheck keys after execution, including the exact consumed fixture object.
  if(stages.measure(`key.after.${name}`,()=>key(postflightOwner)).key!==saved.key || hash(object)!==saved.object_sha256) throw new Error("inputs changed while importing fixture");
  writeFileSync(`${out}/cached-${name}-key.json`,JSON.stringify({...saved,fixture:file,reports,toolchain_verification:sharedToolchain?"complete-batch-boundary":"complete-per-file-boundary"},null,2)+"\n");
  const result={fixture:file,mode,key:saved.key,reports,object}; console.log(JSON.stringify(result)); return result;
  };
  if(batchItems) { batchItems.push({file,harness,names:Object.keys(expected.pins).sort(),finish}); return; }
  return finish(await run(["env","lean","-j1","--tstack=131072",harnessFile],`${out}/cached-${name}-diagnostics.log`,stages));
}

  });
}
// Split ONLY actual Lean reports, retaining count/order and failing on any
// diagnostic error. Per-fixture exact-set guards still validate every slice.
export function splitBatchReports(log,groups) {
  if(/\berror(?:\(|:)/.test(log)) throw new Error("Lean error in actual batch report");
  const matches=[...log.matchAll(/\x27([^\x27]+)\x27 (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)/g)];
  const names=groups.flatMap(group=>group.names);
  if(matches.length!==names.length || matches.some((m,i)=>m[1]!==names[i]))
    throw new Error("missing/extra/duplicate/reordered actual batch axiom report");
  let offset=0;
  return groups.map(group=>{const slice=matches.slice(offset,offset+group.names.length);offset+=group.names.length;
    return slice.map(m=>m[0]).join("\n")+"\n";});
}

async function batch(out,files) {
  if(!out?.startsWith("/")) throw new Error("absolute batch evidence directory required");
  const all=Object.keys(registry).map(name=>`tests/internal-flow/${name}.lean`).sort();
  if(JSON.stringify(files)!==JSON.stringify(all)) throw new Error("batch must contain EVERY registered fixture exactly once in sorted order");
  const stages=new StageJournal(out);
  return stages.measureAsync("batch",async()=>{
  const before=Object.freeze(stages.measure("toolchain.before",toolchainInputs));
  const items=[];
  await withObjectDigests(owner=>visitFixturesAsync(files,file=>fixture("check",file,out,before,items,stages,owner)),record=>stages.record("object-digests.preflight-released",record));
  // Every fixture source/object/dependency key is freshly checked before the
  // actual combined Lean import. No fixture, report or freshness check is cut.
  const combined=items.map(item=>item.harness.split("\n")[0]).join("\n")+"\n"+
    items.map(item=>item.harness.split("\n").slice(1).join("\n")).join("\n");
  const harness=".lake/build/v12-all-fixtures-import.lean";
  stages.measure("harness.write",()=>{writeFileSync(harness,combined);writeFileSync(`${out}/cached-all-fixtures-import.lean`,combined);});
  const log=await run(["env","lean","-j1","--tstack=131072",harness],`${out}/cached-all-fixtures-diagnostics.log`,stages);
  const slices=stages.measure("reports.batch",()=>splitBatchReports(log,items));
  const results=await withObjectDigests(owner=>visitFixtures(items,(item)=>{
    const index=items.indexOf(item),slice=slices[index];
    writeFileSync(`${out}/cached-${basename(item.file,".lean")}-diagnostics.log`,slice);
    return item.finish(slice,owner); // Exact guard AND fresh post-import key/object.
  }),record=>stages.record("object-digests.postflight-released",record));
  const after=stages.measure("toolchain.after",toolchainInputs);
  stages.measure("toolchain.compare",()=>requireSameToolchain(before,after));
  const record={status:"pass",execution:"one-actual-Lean-process-all-imports-and-all-axiom-reports",toolchain_verification:"complete-before-and-after-batch",toolchain_entries:Object.keys(before).length,
    before_sha256:createHash("sha256").update(JSON.stringify(before)).digest("hex"),
    after_sha256:createHash("sha256").update(JSON.stringify(after)).digest("hex"),
    fixtures:results,reports:results.reduce((n,result)=>n+result.reports,0)};
  writeFileSync(`${out}/cached-batch-toolchain.json`,JSON.stringify(record,null,2)+"\n");
  console.log(JSON.stringify(record));
  });
}
if(process.argv[1] && import.meta.url===pathToFileURL(resolve(process.argv[1])).href) {
  const [mode,...args]=process.argv.slice(2);
  try {
    if(mode==="batch") await batch(args[0],args.slice(1));
    else await fixture(mode,args[0],args[1]);
  } catch(error) { cliFailure(error); }
}
