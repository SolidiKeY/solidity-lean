// Full compiler AST backfill. Expected outcomes are obligations, never verifier verdicts.
const started = process.hrtime.bigint();
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');
const root = __dirname;
const compiler = process.env.MEMORY_SOLJSON || '/workspace/.setup/soljson/soljson-v0.8.34+commit.80d5c536.js';
const sha = b => crypto.createHash('sha256').update(b).digest('hex');
const compilerSha = sha(fs.readFileSync(compiler));
assert.equal(compilerSha, 'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8');
const solc = require(compiler);
const compile = solc.cwrap('solidity_compile', 'string', ['string','number','number']);
const version = solc.cwrap('solidity_version','string',[])();
assert.equal(version,'0.8.34+commit.80d5c536.Emscripten.clang');
const cases = [
 ['identity','int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 1);','success'],
 ['false','int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 2);','panic'],
 ['default','int[] memory m = new int[](1); assert(m[0] == 0);','success'],
 ['alias','int[] memory m = new int[](1); int[] memory a = m; a[0] = -1; assert(m[0] == -1);','success'],
 ['aliasIsNotCopy','int[] memory m = new int[](1); int[] memory a = m; a[0] = 1; assert(m[0] == 0);','panic'],
 ['distinctAllocations','int[] memory m = new int[](1); int[] memory a = new int[](1); a[0] = 1; assert(m[0] == 0);','success'],
 ['zeroRead','int[] memory m = new int[](0); assert(m[0] == 0);','revert'],
 ['zeroWrite','int[] memory m = new int[](0); m[0] = 1; assert(false);','revert'],
 ['oobRead','int[] memory m = new int[](1); assert(m[1] == 0);','revert'],
 ['oobWrite','int[] memory m = new int[](1); m[1] = 1; assert(false);','revert'],
 ['emptySuccess','int[] memory m = new int[](0); assert(m.length == 0);','success'],
 ['uintIdentity','uint[] memory m = new uint[](1); m[0] = 1; assert(m[0] == 1);','success'],
 ['boolDefault','bool[] memory m = new bool[](1); assert(!m[0]);','success'],
 ['boolAlias','bool[] memory m = new bool[](1); bool[] memory a = m; a[0] = true; assert(m[0]);','success'],
 ['fixedDefault','int[1] memory m; assert(m[0] == 0);','success'],
 ['fixedAlias','int[1] memory m; int[1] memory a = m; a[0] = 1; assert(m[0] == 1);','success'],
 ['referenceAlias','int[][] memory m = new int[][](1); m[0] = new int[](1); int[] memory a = m[0]; a[0] = 1; assert(m[0][0] == 1);','success'],
 ['mappingRoot','int[] memory m = new int[](1); m[0] = 1; assert(m[0] == 1);','success','mapping(uint => int) unused;'],
 ['storageAlias','int[] storage a = stored; a[0] = 1; assert(stored[0] == 1);','conditionalSuccessOrRevert','int[] stored;',''],
 ['copyAfterPush','stored.push(0); uint i = stored.length - 1; int[] memory m = stored; m[i] = 1; assert(stored[i] == 0);','successOrExhausted','int[] stored;',''],
 ['storageCopy','int[] memory m = stored; m[0] = 1; assert(stored[0] == 0);','conditionalSuccessOrRevert','int[] stored;','view','require(stored.length == 1); require(stored[0] == 0); '],
];
const walk = function*(x) { if (x && typeof x === 'object') { yield x; for (const v of Object.values(x)) yield* walk(v); } };
const write = (p,s) => { fs.mkdirSync(path.dirname(p),{recursive:true}); fs.writeFileSync(p,s); };
const rows=[];
for (const [id,body,outcome,state='',mutability='pure',prefix=''] of cases) {
 for (const modality of ['box','diamond']) {
  const source = `pragma solidity ^0.8.34; contract Identity {${state ? ' '+state : ''}${modality === 'box' ? ' /// @custom:key box\n' : '\n'}function identity() public ${mutability} { ${prefix}${body} } }\n`;
  const stem = `${id}.${modality}`;
  write(path.join(root,'sources',stem+'.sol'),source);
  for (const viaIR of [false,true]) {
   const input={language:'Solidity',sources:{'Identity.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',outputSelection:{'*':{'':['ast']}}}};
   const output=JSON.parse(compile(JSON.stringify(input),0,0));
   assert.equal((output.errors||[]).filter(x=>x.severity==='error').length,0,JSON.stringify(output.errors));
   const ast=output.sources['Identity.sol'].ast;
   const nodes=[...walk(ast)];
   assert(nodes.some(n=>n.nodeType==='VariableDeclaration'&&['memory','storage'].includes(n.storageLocation)));
   if(id==='identity') {
    assert(nodes.some(n=>n.nodeType==='NewExpression'&&n.typeName.nodeType==='ArrayTypeName'));
    assert(nodes.some(n=>n.nodeType==='IndexAccess'));
    assert(nodes.some(n=>n.nodeType==='Assignment'));
    assert.equal(nodes.find(n=>n.nodeType==='FunctionDefinition').documentation?.text,modality==='box'?'@custom:key box':undefined);
   }
   const name=stem+(viaIR?'.ir':'.legacy');
   write(path.join(root,'compiler',name+'.input.json'),JSON.stringify(input,null,2)+'\n');
   write(path.join(root,'compiler',name+'.output.json'),JSON.stringify(output,null,2)+'\n');
   rows.push({id,modality,viaIR,source:'sources/'+stem+'.sol',input:'compiler/'+name+'.input.json',output:'compiler/'+name+'.output.json',sourceSha256:sha(source),modelHalt:outcome,initialModelHalt:outcome==='conditionalSuccessOrRevert'?'revert':outcome==='successOrExhausted'?'success':outcome,requiredProven:['success','successOrExhausted'].includes(outcome)||(['revert','conditionalSuccessOrRevert'].includes(outcome)&&modality==='box'),admission:'pending',proofClosure:'pending',native:'pending',browser:'pending'});
  }
 }
}
write(path.join(root,'manifest.json'),JSON.stringify({compilerVersion:version,compilerSha256:compilerSha,warning:'Expected model outcomes are obligations, not observed verifier verdicts. Bounds failures are revert in the existing model, solc panic externally. storageCopy is conditional on its requires.',cases:rows},null,2)+'\n');
// Compiler-invalid controls keep their complete diagnostics, not an AST success.
const invalid = [
 ['scalarMemory','int memory m = 1;'],
 ['missingLocation','int[] m = new int[](1);'],
 ['storageFromNew','int[] storage m = new int[](1);'],
 ['calldataFromNew','int[] calldata m = new int[](1);'],
 ['incompatibleElement','bool[] memory m = new int[](1);'],
 ['fixedNew','int[1] memory m = new int[1](1);'],
 ['negativeLength','int[] memory m = new int[](-1);'],
 ['mappingMemory','mapping(uint => int) memory m;'],
];
const invalidRows=[];
for(const [id,body] of invalid) {
 const source=`pragma solidity ^0.8.34; contract Invalid { function test() public pure { ${body} } }\n`;
 const input={language:'Solidity',sources:{'Invalid.sol':{content:source}},settings:{outputSelection:{'*':{'':['ast']}}}};
 const output=JSON.parse(compile(JSON.stringify(input),0,0));
 const errors=(output.errors||[]).filter(x=>x.severity==='error');
 assert(errors.length>0,id+' must fail compiler validation');
 write(path.join(root,'invalid',id+'.sol'),source);
 write(path.join(root,'invalid',id+'.input.json'),JSON.stringify(input,null,2)+'\n');
 write(path.join(root,'invalid',id+'.output.json'),JSON.stringify(output,null,2)+'\n');
 invalidRows.push({id,sourceSha256:sha(source),compilerErrorCodes:errors.map(x=>x.errorCode),runtimeAdmission:'pending'});
}
write(path.join(root,'invalid.json'),JSON.stringify(invalidRows,null,2)+'\n');
// These are deliberately corrupted compiler outputs. They have no compiler provenance.
const original=JSON.parse(fs.readFileSync(path.join(root,'compiler/identity.box.legacy.output.json')));
const mutations=[
 ['missingLocation',(d)=>{delete d.storageLocation;}],
 ['coherentStorageFromNew',(d)=>{d.storageLocation='storage';d.typeDescriptions.typeIdentifier=d.typeDescriptions.typeIdentifier.replaceAll('memory','storage');}],
 ['allocationResultLocation',(_,o)=>{const n=[...walk(o)].find(n=>n.nodeType==='FunctionCall'&&n.expression.nodeType==='NewExpression');n.typeDescriptions.typeIdentifier=n.typeDescriptions.typeIdentifier.replaceAll('memory','storage');}],
 ['constructorIdentifier',(_,o)=>{[...walk(o)].find(n=>n.nodeType==='NewExpression').typeDescriptions.typeIdentifier='t_bool';}],
 ['missingConstructorIdentifier',(_,o)=>{delete [...walk(o)].find(n=>n.nodeType==='NewExpression').typeDescriptions.typeIdentifier;}],
 ['tryAllocation',(_,o)=>{[...walk(o)].find(n=>n.nodeType==='FunctionCall'&&n.expression.nodeType==='NewExpression').tryCall=true;}],
 ['allocationArity',(_,o)=>{[...walk(o)].find(n=>n.nodeType==='FunctionCall'&&n.expression.nodeType==='NewExpression').arguments=[];}],
 ['wrongDeclarationNode',(d)=>{d.nodeType='Literal';}],
 ['missingDeclarationNode',(d)=>{delete d.nodeType;}],
 ['stateLocal',(d)=>{d.stateVariable=true;}],
 ['constantLocal',(d)=>{d.constant=true;}],
 ['calldataIdentifier',(d)=>{d.typeDescriptions.typeIdentifier=d.typeDescriptions.typeIdentifier.replaceAll('memory','calldata');}],
 ['missingIdentifier',(d)=>{delete d.typeDescriptions.typeIdentifier;}],
 ...[0n,2n**256n].map(n=>['fixedLength'+n,(d)=>{
   d.typeName.length={nodeType:'Literal',kind:'number',value:String(n),typeDescriptions:{typeString:'int_const '+n}};
   d.typeName.typeDescriptions={typeString:`int256[${n}]`,typeIdentifier:`t_array$_t_int256_$${n}_storage_ptr`};
   d.typeDescriptions={typeString:`int256[${n}]`,typeIdentifier:`t_array$_t_int256_$${n}_memory_ptr`};
 }]),
 ['calldataLocation',(d)=>{d.storageLocation='calldata';}],
 ['storageLocation',(d)=>{d.storageLocation='storage';}],
 ['unknownLocation',(d)=>{d.storageLocation='invented';}],
 ['incompatibleType',(d)=>{d.typeName.baseType.name='bool';}],
 ['missingTypeName',(d)=>{delete d.typeName;}],
];
for(const [id,mutate] of mutations) {
 const output=structuredClone(original);
 const d=[...walk(output)].find(n=>n.nodeType==='VariableDeclaration'&&n.name==='m');
 assert(d); mutate(d,output);
 write(path.join(root,'malformed',id+'.output.json'),JSON.stringify(output,null,2)+'\n');
}
// Coherent type metadata that still requires intrinsic rejection.
const mismatch=structuredClone(original);
const md=[...walk(mismatch)].find(n=>n.nodeType==='VariableDeclaration'&&n.name==='m');
md.typeName.baseType.name='bool';md.typeName.baseType.typeDescriptions={typeString:'bool',typeIdentifier:'t_bool'};
md.typeName.typeDescriptions={typeString:'bool[]',typeIdentifier:'t_array$_t_bool_$dyn_storage_ptr'};
md.typeDescriptions={typeString:'bool[]',typeIdentifier:'t_array$_t_bool_$dyn_memory_ptr'};
write(path.join(root,'type-errors/elementMismatch.output.json'),JSON.stringify(mismatch,null,2)+'\n');
const wrongAlias=JSON.parse(fs.readFileSync(path.join(root,'compiler/alias.box.legacy.output.json')));
const ad=[...walk(wrongAlias)].find(n=>n.nodeType==='VariableDeclaration'&&n.name==='a');
ad.storageLocation='storage';ad.typeDescriptions.typeIdentifier=ad.typeDescriptions.typeIdentifier.replaceAll('memory','storage');
write(path.join(root,'type-errors/storageFromMemory.output.json'),JSON.stringify(wrongAlias,null,2)+'\n');
write(path.join(root,'malformed/README.txt'),'Corrupted AST fixtures; NOT compiler-produced; must reject/unknown, never success. Admission remains pending.\n');
console.log(`PASS ${invalidRows.length} compiler-invalid controls and ${mutations.length} corrupted admission controls (not executed)`);
console.log(`PASS ${rows.length} full compiler AST fixtures; ${cases.length} scenarios x 2 modalities x 2 pipelines; compiler ${version}; no verifier invoked`);

console.log(JSON.stringify({wallSeconds:Number(process.hrtime.bigint()-started)/1e9,maxRssKiB:process.resourceUsage().maxRSS}));
