import assert from 'node:assert/strict';
import {compareExact} from './check-pins.mjs';
const expected={T:['propext']};
assert.deepEqual(compareExact({T:['propext']},expected,['T']),[]);
for(const actual of [{},{T:[]},{T:['sorryAx']},{T:['propext'],X:[]}])assert.ok(compareExact(actual,expected,['T']).length);
assert.ok(compareExact({T:['propext']},{},['T']).length);
assert.ok(compareExact({T:['propext']},expected,[]).length);
console.log('V07 comparison unit controls: 6 rejected');

import {mkdtempSync,readFileSync,writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
const dir=mkdtempSync(join(tmpdir(),'v07-pin-copies-'));
const guards=readFileSync('tests/v07/Axioms.lean','utf8');
const registry=JSON.parse(readFileSync('tests/v07/axiom-pins.json','utf8'));
const guardPath=join(dir,'Axioms.lean'), registryPath=join(dir,'pins.json');
function run(g,r,expected,label) {
 writeFileSync(guardPath,g);writeFileSync(registryPath,JSON.stringify(r));
 const result=spawnSync(process.execPath,['tests/v07/check-pins.mjs',guardPath,registryPath],{encoding:'utf8'});
 assert.equal(result.status,expected,label+' '+result.stdout+result.stderr);
 console.log(label+': exit '+result.status);
}
run(guards,registry,0,'actual copied inputs');
run(guards,{...registry,'Unexpected.Proof':[]},1,'actual copied registry unexpected');
const first=Object.keys(registry)[0];
run(guards,{...registry,[first]:[]},1,'actual copied registry changed');
const omitted={...registry};delete omitted[first];
run(guards,omitted,1,'actual copied registry omitted');
const without=guards.replace(/\/-- info:[\s\S]*?-\/\n#guard_msgs in\n#print axioms [^\n]+\n/,'');
assert.notEqual(without,guards);
run(without,registry,1,'actual copied guard omitted');
console.log('Mutation copies retained at '+dir);

const client=Object.keys(registry).find(n=>n.startsWith('Solidity.Lowering.V07.RegisteredScalarClients.'));
assert.ok(client,'registered proof clients must be covered');
run(guards,{...registry,[client]:[]},1,'registered client copied registry changed');
const withoutClient={...registry};delete withoutClient[client];
run(guards,withoutClient,1,'registered client copied registry omitted');

const castClient='Solidity.Lowering.V07.WordCastControls.cast_to_int_transport';
assert.ok(Object.hasOwn(registry,castClient),'current cast clients must be covered');
run(guards,{...registry,[castClient]:[]},1,'cast client copied registry changed');
const withoutCast={...registry};delete withoutCast[castClient];
run(guards,withoutCast,1,'cast client copied registry omitted');

const conditionalClient='Solidity.Lowering.V07.ConditionalControls.conditional_transport';
assert.ok(Object.hasOwn(registry,conditionalClient),'current conditional clients must be covered');
run(guards,{...registry,[conditionalClient]:[]},1,'conditional client copied registry changed');
const withoutConditional={...registry};delete withoutConditional[conditionalClient];
run(guards,withoutConditional,1,'conditional client copied registry omitted');

const signedClient='Solidity.Lowering.V07.SignedSubtractionControls.signed_assignment';
assert.ok(Object.hasOwn(registry,signedClient),'current signed clients must be covered');
run(guards,{...registry,[signedClient]:[]},1,'signed client copied registry changed');
const withoutSigned={...registry};delete withoutSigned[signedClient];
run(guards,withoutSigned,1,'signed client copied registry omitted');

const boolClient='Solidity.Lowering.V07.UdvtBoolAssignmentControls.transport_client';
assert.ok(Object.hasOwn(registry,boolClient),'current Boolean transport client must be covered');
run(guards,{...registry,[boolClient]:[]},1,'Boolean client copied registry changed');
const withoutBool={...registry};delete withoutBool[boolClient];
run(guards,withoutBool,1,'Boolean client copied registry omitted');

const addressClient='Solidity.Lowering.V07.UdvtAddressAssignmentControls.transport_client';
assert.ok(Object.hasOwn(registry,addressClient),'current address transport client must be covered');
run(guards,{...registry,[addressClient]:[]},1,'address client copied registry changed');
const withoutAddress={...registry};delete withoutAddress[addressClient];
run(guards,withoutAddress,1,'address client copied registry omitted');

const fixedBytesClient='Solidity.Lowering.V07.FixedBytesAssignmentControls.transport_client';
assert.ok(Object.hasOwn(registry,fixedBytesClient),'current fixed-byte transport client must be covered');
run(guards,{...registry,[fixedBytesClient]:[]},1,'fixed-byte client copied registry changed');
const withoutFixedBytes={...registry};delete withoutFixedBytes[fixedBytesClient];
run(guards,withoutFixedBytes,1,'fixed-byte client copied registry omitted');

const udvtBytesClient='Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls.transport_client';
assert.ok(Object.hasOwn(registry,udvtBytesClient),'current UDVT bytes transport client must be covered');
run(guards,{...registry,[udvtBytesClient]:[]},1,'UDVT bytes client copied registry changed');
const withoutUdvtBytes={...registry};delete withoutUdvtBytes[udvtBytesClient];
run(guards,withoutUdvtBytes,1,'UDVT bytes client copied registry omitted');

const byteCompareClient='Solidity.Lowering.V07.FixedBytesComparisonControls.transport_client';
assert.ok(Object.hasOwn(registry,byteCompareClient),'current byte comparison transport client must be covered');
run(guards,{...registry,[byteCompareClient]:[]},1,'byte comparison client copied registry changed');
const withoutByteCompare={...registry};delete withoutByteCompare[byteCompareClient];
run(guards,withoutByteCompare,1,'byte comparison client copied registry omitted');

const integerConstantClient='Solidity.Lowering.V07.IntegerConstantControls.transport_client';
assert.ok(Object.hasOwn(registry,integerConstantClient),'current integer constant transport client must be covered');
run(guards,{...registry,[integerConstantClient]:[]},1,'integer constant client copied registry changed');
const withoutIntegerConstant={...registry};delete withoutIntegerConstant[integerConstantClient];
run(guards,withoutIntegerConstant,1,'integer constant client copied registry omitted');

const constantAssignClient='Solidity.Lowering.V07.IntegerConstantAssignmentControls.transport_client';
assert.ok(Object.hasOwn(registry,constantAssignClient),'constant assignment transport client covered');
run(guards,{...registry,[constantAssignClient]:[]},1,'constant assignment client copied registry changed');
const withoutConstantAssign={...registry};delete withoutConstantAssign[constantAssignClient];
run(guards,withoutConstantAssign,1,'constant assignment client copied registry omitted');

const rationalClient='Solidity.Lowering.V07.IntegralRationalControls.assignment_transport_client';
assert.ok(Object.hasOwn(registry,rationalClient),'rational assignment transport client covered');
run(guards,{...registry,[rationalClient]:[]},1,'rational client copied registry changed');
const withoutRational={...registry};delete withoutRational[rationalClient];
run(guards,withoutRational,1,'rational client copied registry omitted');

for (const name of ['Solidity.Lowering.V07.P12AssignedCondition.assignment','Solidity.Lowering.V07.P12AssignedConditionControls.producer']) {
assert.ok(Object.hasOwn(registry,name),'actual condition constructor covered');
run(guards,{...registry,[name]:[]},1,name+' copied registry changed');
const without={...registry};delete without[name];
run(guards,without,1,name+' copied registry omitted');}

for (const name of ['Solidity.Lowering.V07.P12NegatedCondition.negate','Solidity.Lowering.V07.P12NegatedConditionControls.producer']) {
assert.ok(Object.hasOwn(registry,name),'actual negated condition constructor covered');
run(guards,{...registry,[name]:[]},1,name+' copied registry changed');
const without={...registry};delete without[name];
run(guards,without,1,name+' copied registry omitted');}
