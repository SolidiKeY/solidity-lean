// Guard H112 against unsafe/new pins, resurrected debt, broad doc exceptions and optimized reproduction.
// Disposable Git/worktree fixtures exercise source tooling only; no Lean runs.
import {test} from "node:test";
import assert from "node:assert/strict";
import {mkdtempSync,mkdirSync,readFileSync,writeFileSync,rmSync,unlinkSync,copyFileSync} from "node:fs";
import {join,dirname,resolve} from "node:path";
import {tmpdir} from "node:os";
import {execFileSync,spawnSync} from "node:child_process";
import {fileURLToPath} from "node:url";
import {collect,compare,STANDARD} from "../../../../scripts/check-axiom-pins.mjs";
import {loadDriftBaseline,changeKey,BASELINE_PATH,ACTIVE_PATH} from "../../../../scripts/axiom-pin-drift-baseline.mjs";
const ROOT=resolve(dirname(fileURLToPath(import.meta.url)),"../../../..");
const BT=String.fromCharCode(96);
const baseline=JSON.parse(readFileSync(join(ROOT,BASELINE_PATH),"utf8"));
const git=(root,...args)=>execFileSync("git",args,{cwd:root,encoding:"utf8",stdio:["ignore","pipe","pipe"]});
function put(root,file,text){mkdirSync(dirname(join(root,file)),{recursive:true});writeFileSync(join(root,file),text);}
function commit(root){git(root,"add","-A");git(root,"commit","-qm","fixture");}
function fixture(t){
 const root=mkdtempSync(join(tmpdir(),"h112-baseline-"));t.after(()=>rmSync(root,{recursive:true,force:true}));
 git(root,"init","-q","-b","main");git(root,"config","user.name","fixture");git(root,"config","user.email","fixture@example.invalid");
 // Model the frozen initial epoch, so legitimate production allowlist shrinking
 // does not make these independent fixtures invalid at their first commit.
 put(root,BASELINE_PATH,readFileSync(join(ROOT,BASELINE_PATH)));
 put(root,ACTIVE_PATH,JSON.stringify(baseline.entries,null,2)+'\n');
 commit(root);return root;
}
function printed(name,axioms,target=name){return `/-- info: '${name}' ${axioms.length?`depends on axioms: [${axioms.join(", ")}]`:"does not depend on any axioms"} -/\n#guard_msgs in #print axioms ${target}\n`;}
function cliFixture(t){
 const root=fixture(t),old={};
 for(const file of ["scripts/check-axiom-pins.mjs","scripts/check-trust.mjs","scripts/axiom-pin-drift-baseline.mjs"])put(root,file,readFileSync(join(ROOT,file)));
 const byFile=new Map();
 for(const row of baseline.entries){const i=row.key.indexOf(".lean:"),file=row.key.slice(0,i+5),name=row.key.slice(i+6);
  byFile.set(file,(byFile.get(file)??"")+printed(name,row.axioms));if(row.recorded!==null)old[row.key]=row.recorded;}
 for(const [file,text] of byFile)put(root,file,text);
 old["Solidity/Recorded.lean:Recorded.good"]=[];put(root,"Solidity/Recorded.lean",printed("Recorded.good",[]));
 put(root,"scripts/g07-axiom-pins.json",JSON.stringify(old));return root;
}
const cli=root=>spawnSync(process.execPath,[join(root,"scripts/check-axiom-pins.mjs")],{cwd:root,encoding:"utf8"});
test("structured changes bind source file, theorem, kind and exact axiom sets",()=>{
 const found=new Map([['A.lean:Same',{file:'A.lean',name:'Same',target:'Same',axioms:[]}],['B.lean:Same',{file:'B.lean',name:'Same',target:'Same',axioms:['propext']}]]);
 const {errors,notes,changes}=compare(found,{});assert.equal(errors.length,0);assert.equal(notes.length,2);assert.equal(new Set(changes.map(changeKey)).size,2);
 const shrunk=compare(found,{'A.lean:Same':['propext'],'B.lean:Same':['propext']}).changes;assert.equal(shrunk[0].kind,'shrunk');assert.notEqual(changeKey(shrunk[0]),changeKey(changes[0]));
});
test("baseline CLI passes only its exact99 known changes",t=>{
 const root=cliFixture(t);let result=cli(root);assert.equal(result.status,0,result.stdout+result.stderr);assert.match(result.stdout,/0 errors, 0 unrecorded changes, 99 baselined/);
 put(root,"Solidity/New.lean",printed("SameNew",[]));result=cli(root);assert.equal(result.status,1);assert.match(result.stdout,/1 unrecorded changes/);
});
test("recorded axiom growth, nonstandard axioms, disappeared pins and malformed pins still fail",t=>{
 const root=cliFixture(t);
 for(const [source,pattern] of [[printed('Recorded.good',['propext']),/gained propext/],[printed('Recorded.good',['sorryAx']),/non-standard axioms sorryAx/],['',/recorded pin .* is gone/],['#guard_msgs in #print axioms Recorded.good\n',/prints no axiom line/]]){
  put(root,'Solidity/Recorded.lean',source);const result=cli(root);assert.equal(result.status,1);assert.match(result.stdout,pattern);}
});
test("baseline cannot mask policy errors on a baselined identity",t=>{
 const root=cliFixture(t),row=baseline.entries[0],i=row.key.indexOf('.lean:'),file=row.key.slice(0,i+5),name=row.key.slice(i+6);
 const text=readFileSync(join(root,file),'utf8');put(root,file,text.replace(`#print axioms ${name}`, '#print axioms Wrong.target'));
 const result=cli(root);assert.equal(result.status,1);assert.match(result.stdout,/prints /);assert.match(result.stdout,/99 baselined/);
});
test("shrinking is permanent in worktree and committed history",t=>{
 const root=fixture(t),p=join(root,ACTIVE_PATH),all=readFileSync(p,'utf8');writeFileSync(p,JSON.stringify(baseline.entries.slice(1)));commit(root);
 assert.equal(loadDriftBaseline(root,STANDARD).size,98);writeFileSync(p,all);assert.throws(()=>loadDriftBaseline(root,STANDARD),/only shrink/);commit(root);assert.throws(()=>loadDriftBaseline(root,STANDARD),/only shrink/);
});
test("delete/recreate and configured merge resurrection cannot restore debt",t=>{
 const root=fixture(t),p=join(root,ACTIVE_PATH),all=readFileSync(p,'utf8');writeFileSync(p,JSON.stringify(baseline.entries.slice(1)));commit(root);unlinkSync(p);commit(root);writeFileSync(p,all);commit(root);assert.throws(()=>loadDriftBaseline(root,STANDARD),/deletion/);
 const other=fixture(t);git(other,'checkout','-qb','shrink');writeFileSync(join(other,ACTIVE_PATH),JSON.stringify(baseline.entries.slice(1)));commit(other);git(other,'checkout','-q','main');git(other,'merge','--no-ff','-s','ours','shrink','-m','fixture');git(other,'config','log.diffMerges','first-parent');assert.throws(()=>loadDriftBaseline(other,STANDARD),/only shrink/);
});
test("SHA pin, changed fields and duplicate identities fail closed",t=>{
 const root=fixture(t),p=join(root,ACTIVE_PATH),rows=structuredClone(baseline.entries);rows[0].axioms=[];writeFileSync(p,JSON.stringify(rows));assert.throws(()=>loadDriftBaseline(root,STANDARD),/only shrink/);
 writeFileSync(p,JSON.stringify([...baseline.entries,baseline.entries[0]]));assert.throws(()=>loadDriftBaseline(root,STANDARD),/duplicate/);
 writeFileSync(p,JSON.stringify(baseline.entries));writeFileSync(join(root,BASELINE_PATH),readFileSync(join(root,BASELINE_PATH),'utf8')+' ');assert.throws(()=>loadDriftBaseline(root,STANDARD),/SHA256/);
});
test("linked worktree graft files are checked at their actual absolute path",t=>{
 const root=fixture(t),linked=join(root,'linked');git(root,'worktree','add','-qb','linked',linked);
 const graft=git(linked,'rev-parse','--path-format=absolute','--git-path','info/grafts').trim();mkdirSync(dirname(graft),{recursive:true});writeFileSync(graft,'# fixture\n');assert.throws(()=>loadDriftBaseline(linked,STANDARD),/custom.*history/);
});
test("only the five exact historical doc pairs are exempt; new sources or paths fail",t=>{
 const root=fixture(t);put(root,'scripts/check-doc-paths.sh',readFileSync(join(ROOT,'scripts/check-doc-paths.sh')));
 const pairs=[['docs/feature-work/h62-1-infer-helpers.md','Solidity/Source/InferHelpers.lean'],['docs/feature-work/h62-6-migrate-theory.md','StringApiWitness.original-unproved.lean'],['scripts/h62/item2/audit-abi-world/test_census.py','Backend/A.lean'],['tests/h62/item4/generic-structuredflow/registration.md','Backend/StructuredFlow/GenericMapped.lean'],['tests/h62/item4/generic-structuredflow/registration.md','Solidity/Backend/StructuredFlow/GenericMapped.lean']];
 for(const file of ['Solidity/Calculus/Close.lean','Solidity/Examples/Tactics/Values.lean','Solidity/KeyTaclets.lean','Solidity/ReadWrite.lean','Solidity/AST.lean','Solidity/Theory/Typed/Obs.lean'])put(root,file,'-- fixture\n');
 for(const [file,ref] of pairs)put(root,file,(readMaybe(root,file))+`Historical: \`${ref}\`\n`);
 commit(root);let result=spawnSync('bash',['scripts/check-doc-paths.sh'],{cwd:root,encoding:'utf8'});assert.equal(result.status,0,result.stdout+result.stderr);assert.equal((result.stdout.match(/historical:/g)??[]).length,5);
 put(root,'new.md',BT+'Solidity/Source/InferHelpers.lean'+BT+'\n');commit(root);result=spawnSync('bash',['scripts/check-doc-paths.sh'],{cwd:root,encoding:'utf8'});assert.equal(result.status,1);assert.match(result.stdout,/missing:.*new.md/);
 put(root,pairs[0][0],BT+'Solidity/Source/OtherMissing.lean'+BT+'\n');commit(root);result=spawnSync('bash',['scripts/check-doc-paths.sh'],{cwd:root,encoding:'utf8'});assert.equal(result.status,1);assert.match(result.stdout,/OtherMissing/);
});
function readMaybe(root,file){try{return readFileSync(join(root,file),'utf8');}catch{return '';}}

test("optimized Python cannot bypass immutable baseline verification",()=>{
 const result=spawnSync('python3',['-O',join(ROOT,'scripts/h62/item5/statement-graph/reproduce_pin_drift.py')],{cwd:ROOT,encoding:'utf8'});
 assert.equal(result.status,1);assert.equal(result.stdout,'');assert.match(result.stderr,/optimized Python refused/);
});
