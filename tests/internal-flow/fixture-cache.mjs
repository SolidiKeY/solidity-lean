#!/usr/bin/env node
// Compiled fixture reuse in the ONE existing Lake tree. Not a full-source gate.
import {readFileSync,writeFileSync,mkdirSync,existsSync,readdirSync,realpathSync,statSync} from "node:fs";
import {resolve,basename} from "node:path";
import {createHash} from "node:crypto";
import {spawnSync} from "node:child_process";
const [mode,file,out] = process.argv.slice(2);
if (!["prepare","check"].includes(mode) || !/^tests\/internal-flow\/[A-Za-z][A-Za-z0-9]*\.lean$/.test(file ?? "") || !out?.startsWith("/"))
  throw new Error("usage: fixture-cache.mjs prepare|check tests/internal-flow/Name.lean /absolute/evidence");
const name=basename(file,".lean"), dir=".lake/build/lib/lean/tests/internal-flow";
const object=`${dir}/${name}.olean`, manifest=`${dir}/${name}.v12-cache.json`;
const pinsFile="tests/internal-flow/fixture-axiom-pins.json";
const registry=JSON.parse(readFileSync(pinsFile,"utf8"));
const expected=registry[name];
if (!expected) throw new Error(`unregistered fixture: ${name}`);
const hash=p=>createHash("sha256").update(readFileSync(p)).digest("hex");
function imports(text) {
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

function key() {
  const closure=new Set(), fixtureDeps=new Set(), pending=imports(readFileSync(file,"utf8"));
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
    pending.push(...imports(readFileSync(path,"utf8")));
  }
  const inputs={};
  for(const path of [file,pinsFile,expected.guard,"tests/internal-flow/fixture-cache.mjs","lean-toolchain","lakefile.lean","lakefile.toml","lake-manifest.json"])
    if(existsSync(path)) inputs[path]=hash(path);
  const toolchain=process.env.LEAN_SYSROOT;
  if(!toolchain) throw new Error("LEAN_SYSROOT must identify the actual capped toolchain");
  // In the authorized wrapper /opt/lean-real is the immutable actual compiler.
  const binary=existsSync("/opt/lean-real/bin/lean")?"/opt/lean-real/bin/lean":`${toolchain}/bin/lean`;
  inputs["compiler-binary"]=hash(binary);
  for(const path of [...closure].sort()) {
    inputs[path]=hash(path);
    inputs[".lake/build/lib/lean/"+path.slice(0,-5)+".olean"]=hash(".lake/build/lib/lean/"+path.slice(0,-5)+".olean");
  }
  for(const dependency of [...fixtureDeps].sort()) inputs[registry[dependency].guard]=hash(registry[dependency].guard);
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
function run(args,log) {
  const child=spawnSync("lake",args,{encoding:"utf8",maxBuffer:64*1024*1024});
  writeFileSync(log,(child.stdout??"")+(child.stderr??""));
  if(child.error) throw child.error;
  if(child.status!==0) process.exit(child.status??1);
  return (child.stdout??"")+(child.stderr??"");
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
  const before=key();
  const log=run(["env","lean","-j1","--tstack=131072","-o",object,file],`${out}/prepared-${name}.log`);
  const reports=guard(log), after=key();
  if(before.key!==after.key) throw new Error("inputs changed during kernel checking");
  writeFileSync(manifest,JSON.stringify({...after,object_sha256:hash(object),reports},null,2)+"\n");
  console.log(JSON.stringify({fixture:file,mode,key:after.key,reports,object}));
} else {
  if(!existsSync(manifest)) throw new Error(`missing checked fixture cache: prepare ${file}`);
  const saved=JSON.parse(readFileSync(manifest,"utf8")), current=key();
  if(saved.key!==current.key || JSON.stringify(saved.inputs)!==JSON.stringify(current.inputs) || saved.object_sha256!==hash(object))
    throw new Error(`stale or altered compiled fixture ${file}; run bounded preparation`);
  const harness=`import tests.«internal-flow».${name}\n`+Object.keys(expected.pins).sort().map(n=>`#print axioms ${n}\n`).join("");
  const harnessFile=`.lake/build/${name}-v12-import.lean`;
  writeFileSync(harnessFile,harness);writeFileSync(`${out}/cached-${name}-import.lean`,harness);
  const log=run(["env","lean","-j1","--tstack=131072",harnessFile],`${out}/cached-${name}-diagnostics.log`);
  const reports=guard(log);
  // Recheck keys after execution, including the exact consumed fixture object.
  if(key().key!==saved.key || hash(object)!==saved.object_sha256) throw new Error("inputs changed while importing fixture");
  writeFileSync(`${out}/cached-${name}-key.json`,JSON.stringify({...saved,fixture:file,reports},null,2)+"\n");
  console.log(JSON.stringify({fixture:file,mode,key:saved.key,reports,object}));
}
