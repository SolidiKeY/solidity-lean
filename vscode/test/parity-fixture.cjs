// Deliberately injected transport/validator data; never native or parity evidence.
'use strict';
const {createHash}=require('node:crypto');
function inventoryFixture(){
 const upstream={repository:'dafny-lang/ide-vscode',path:'src/injected.ts',sha256:'1'.repeat(64)},id='behavior:injected-test';
 return {schemaVersion:1,upstream:{extension:{commit:'a'.repeat(40)},server:{commit:'b'.repeat(40)}},sources:[{...upstream}],discovery:{featureCount:1,featureIdsSha256:createHash('sha256').update(JSON.stringify([id])).digest('hex')},features:[{id,kind:'editor-behavior',upstream:[{...upstream}],assessment:{status:'partial',reason:'Injected validator fixture, no native observations.',localSource:[],scenarioIds:[],testEvidence:[]}}],mechanical:{rows:[{id:'injected:mechanical',assessment:{status:'unexamined'}}]}};
}
module.exports={inventoryFixture};
