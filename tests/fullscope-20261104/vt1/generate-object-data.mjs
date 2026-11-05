import {createHash} from 'node:crypto';
import {readFileSync,writeFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {dirname,join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import assert from 'node:assert/strict';
import {COMPILERS} from '../../../scripts/solc-unit.mjs';
const here=dirname(fileURLToPath(import.meta.url));
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
const pin=COMPILERS.find(p=>p.version.startsWith('0.8.38+'));
let check=false, dir=here, compilerPath;
const args=process.argv.slice(2);
for(let i=0;i<args.length;i++) {
  if(args[i]==='--check') check=true;
  else if(args[i]==='--dir') { assert.ok(args[++i]); dir=resolve(args[i]); }
  else { assert.ok(!compilerPath&&!args[i].startsWith('--'),'unknown argument'); compilerPath=args[i]; }
}
const compiler=resolve(compilerPath??'/workspace/.setup/soljson/'+pin.file);
function save(name,text) {
  if(check) assert.equal(readFileSync(join(dir,name),'utf8'),text,`fixture differs: ${name}`);
  else writeFileSync(join(dir,name),text);
}
assert.equal(sha(readFileSync(compiler)),pin.sha256);
const solc=createRequire(import.meta.url)(compiler);
assert.equal(solc.cwrap('solidity_version','string',[])(),pin.version);
const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
const content=readFileSync(join(dir,'ObjectData.yul'),'utf8');
const input={language:'Yul',sources:{'ObjectData.yul':{content}},settings:{evmVersion:'osaka',optimizer:{enabled:false},outputSelection:{'*':{'*':['evm.bytecode.object']}}}};
const output=JSON.parse(compile(JSON.stringify(input),0,0));
assert.deepEqual((output.errors??[]).filter(d=>d.severity==='error'),[]);
const hex=output.contracts['ObjectData.yul'].Root.evm.bytecode.object;
assert.match(hex,/^[0-9a-f]+$/); assert.ok(hex.endsWith('112233'));
const bytes=[...Buffer.from(hex,'hex')], offset=bytes.length-3;
const controlCases=[
  {id:'unknown-label',content:'object "A" { code { pop(dataoffset("missing")) } }',expected:['TypeError','Unknown data object "missing".']},
  {id:'duplicate-label',content:'object "A" { code { stop() } data "x" hex"11" data "x" hex"22" }',expected:['ParserError','Object name "x" already exists inside the containing object.']},
];
const controls=controlCases.map(({id,content,expected})=>{
  const input={language:'Yul',sources:{'control.yul':{content}},settings:{evmVersion:'osaka',outputSelection:{'*':{'*':['evm.bytecode.object']}}}};
  const output=JSON.parse(compile(JSON.stringify(input),0,0));
  const diagnostics=(output.errors??[]).filter(d=>d.severity==='error');
  assert.deepEqual(diagnostics.map(d=>[d.type,d.message]),[expected]);
  return {id,input,diagnostics};
});
const artifact={compiler:pin,input,output,controls,sha256:sha(Buffer.from(hex,'hex')),payload:{offset,size:3,bytes:[17,34,51]},boundary:'External assembled-byte fixture; label association and EVM execution are not kernel proved.'};
save('object-data.json',JSON.stringify(artifact,null,2)+'\n');
const values=bytes.map(b=>`⟨${b}, by decide⟩`).join(', ');
const lean=`import Solidity.SolcValidation.DataResolution
open Solidity.SolcValidation
-- Generated from exact pinned assembled bytes; this file proves byte intervals,
-- not compiler correctness, label association, gas or physical memory copying.
def assembledObject : List DataByte := [${values}]
def payload : DataRef assembledObject :=
  ⟨⟨${offset}, by decide⟩, ⟨3, by decide⟩, by decide⟩
def payloadTable : DataTable assembledObject :=
  ⟨[("payload", payload)], by decide⟩
example : payload.bytes = [⟨17, by decide⟩, ⟨34, by decide⟩, ⟨51, by decide⟩] := rfl
example : payload.datasize.val = 3 := rfl
example : payload.dataoffset.val = ${offset} := rfl
example : (payloadTable.select "payload").isSome = true := rfl
example : (payloadTable.select "absent").isSome = false := rfl
example : ((⟨⟨${bytes.length}, by decide⟩, ⟨0, by decide⟩, by decide⟩ : DataRef assembledObject).bytes) = [] := rfl
example (ref : DataRef assembledObject)
    (atEnd : ref.offset.val = ${bytes.length-2}) (size : ref.size.val = 3) : False := by
  have bound := ref.within
  change ref.offset.val + ref.size.val ≤ ${bytes.length} at bound
  rw [atEnd, size] at bound
  omega
example (table : DataTable assembledObject)
    (duplicate : table.entries = [("payload", payload), ("payload", payload)]) : False := by
  have invalid : ¬ (["payload", "payload"] : List String).Nodup := by decide
  apply invalid
  simpa only [duplicate, List.map_cons, List.map_nil] using table.unique
def endpoint : DataRef assembledObject :=
  ⟨⟨${bytes.length}, by decide⟩, ⟨0, by decide⟩, by decide⟩
def twoLabels : DataTable assembledObject :=
  ⟨[("empty", endpoint), ("payload", payload)], by decide⟩
def tailSelection : DataSelection twoLabels.entries "payload" :=
  ⟨payload, List.Mem.tail _ (List.Mem.head _)⟩
example : twoLabels.select "payload" = some tailSelection :=
  twoLabels.select_complete tailSelection
example (other : DataSelection twoLabels.entries "payload") : other.ref = payload :=
  twoLabels.selection_unique other tailSelection
example : ((twoLabels.select "empty").map fun selected => selected.ref.bytes) = some [] := rfl
example : (twoLabels.select "wrong").isSome = false := rfl
#print axioms DataTable.selection_unique
#print axioms DataSelection.ext
#print axioms DataTable.select_complete
#print axioms DataTable.select_iff
#print axioms DataRef.bytes_length
#print axioms DataRef.datasize_exact
#print axioms DataRef.dataoffset_exact
#print axioms DataRef.byte_exact
#print axioms DataSelection.sound
#print axioms selectData_complete
`;
save('ObjectDataChecks.lean',lean);
console.log(JSON.stringify({artifactBytes:bytes.length,payloadOffset:offset,payloadSize:3,compilerRejections:controls.length,check,sha256:artifact.sha256}));
