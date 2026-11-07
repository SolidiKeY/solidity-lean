// Guard H112 known pin drift without masking new drift or any axiom-policy error.
// Baseline entries are exact file/name/kind/old-set/new-set identities, not names.
import {readFileSync,existsSync} from "node:fs";
import {join,resolve} from "node:path";
import {createHash} from "node:crypto";
import {execFileSync} from "node:child_process";
export const BASELINE_SHA256 = "4d98b1810853c54992feb064f1a7b028e23d8212fd2aad8b8b65e81895d7c701";
export const BASELINE_PATH = "scripts/g07-unrecorded-baseline.json";
export const ACTIVE_PATH = "scripts/g07-unrecorded-allowlist.json";
const require = (ok,message) => {if (!ok) throw Error(message);};
export const changeKey = row => JSON.stringify([row.key,row.kind,row.recorded,row.axioms]);
export function changeSet(rows,standard) {
  require(Array.isArray(rows),"pin drift allowlist must be an array");
  const seen=new Set(),result=new Set();
  const axioms=xs=>Array.isArray(xs) && xs.every(x=>typeof x==="string" && standard.includes(x)) &&
    new Set(xs).size===xs.length && JSON.stringify(xs)===JSON.stringify([...xs].sort());
  for (const row of rows) {
    require(row && typeof row==="object" && Object.keys(row).sort().join() === "axioms,key,kind,recorded", "invalid pin drift fields");
    require(typeof row.key==="string" && /^.+\.lean:[^\s]+$/.test(row.key) && !seen.has(row.key), "invalid/duplicate file-bound drift key");
    require(axioms(row.axioms),"invalid pin drift axiom set");
    require((row.kind==="new" && row.recorded===null) || (row.kind==="shrunk" && axioms(row.recorded) &&
      row.recorded.length>row.axioms.length && row.axioms.every(x=>row.recorded.includes(x))), "invalid pin drift kind/old set");
    seen.add(row.key);result.add(changeKey(row));
  }
  return result;
}
export function requireSubset(next,previous) {
  for (const key of next) require(previous.has(key),"pin drift baseline can only shrink: "+key);
}
export function loadDriftBaseline(root,standard) {
  const raw=readFileSync(join(root,BASELINE_PATH));
  require(createHash("sha256").update(raw).digest("hex")===BASELINE_SHA256,"pin drift baseline SHA256 mismatch");
  const snapshot=JSON.parse(raw);
  require(snapshot && Object.keys(snapshot).sort().join()==="entries,inventorySha256,masterCommit,schema,sourceCommit" && snapshot.schema===1,
    "invalid pin drift snapshot schema");
  require([snapshot.sourceCommit,snapshot.masterCommit].every(x=>typeof x==="string" && /^[0-9a-f]{40}$/.test(x)) &&
    typeof snapshot.inventorySha256==="string" && /^[0-9a-f]{64}$/.test(snapshot.inventorySha256),"invalid baseline provenance");
  const baseline=changeSet(snapshot.entries,standard);
  require(baseline.size===99,"H112 exact intake requires 99 entries");
  const active=changeSet(JSON.parse(readFileSync(join(root,ACTIVE_PATH),"utf8")),standard);
  requireSubset(active,baseline);
  const git=(...args)=>execFileSync("git",["--no-replace-objects",...args],{cwd:root,encoding:"utf8",stdio:["ignore","pipe","pipe"]});
  require(git("rev-parse","--is-shallow-repository").trim()==="false","full pin baseline history required");
  require(process.env.GIT_GRAFT_FILE===undefined && process.env.GIT_SHALLOW_FILE===undefined &&
    !existsSync(resolve(root,git("rev-parse","--git-path","info/grafts").trim())),"custom pin baseline history refused");
  const at=rev=>git("ls-tree",rev,"--",ACTIVE_PATH).trim() ? changeSet(JSON.parse(git("show",`${rev}:${ACTIVE_PATH}`)),standard) : null;
  const head=at("HEAD");if(head)requireSubset(active,head);
  const revisions=new Set(git("log","--full-history","--diff-merges=separate","--format=%H","--name-only","HEAD","--",ACTIVE_PATH)
    .split("\n").filter(x=>/^[0-9a-f]{40}$/.test(x)));
  for(const rev of revisions) {
    const [, ...parents]=git("rev-list","--parents","-n","1",rev).trim().split(" ");
    const current=at(rev), prior=parents.map(at).filter(x=>x!==null);
    if(current===null) {require(!prior.length,"pin baseline deletion is not permitted");continue;}
    requireSubset(current,baseline);
    if(!prior.length)require(current.size===baseline.size,"initial pin allowlist must equal pinned baseline");
    for(const previous of prior)requireSubset(current,previous);
  }
  return active;
}
