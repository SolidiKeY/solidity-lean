import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
const req = createRequire(resolve('scripts/evm-vectors/node_modules/reference.cjs'));
const version=JSON.parse(readFileSync(resolve('scripts/evm-vectors/node_modules/@ethereumjs/evm/package.json'),'utf8')).version;
assert.equal(version,'10.1.3');
const {createVM} = req('@ethereumjs/vm');
const {Common, Mainnet, Hardfork} = req('@ethereumjs/common');
const {createAddressFromString, createAccount} = req('@ethereumjs/util');
const {keccak256, sha256, ripemd160, toBeHex} = req('ethers');
const lines=readFileSync(process.argv[2],'utf8').split('\n');
const programs=JSON.parse(lines.find(l=>l.startsWith('[["environment"')));
const common=new Common({chain:Mainnet,hardfork:Hardfork.Osaka});
const vm=await createVM({common});
const self=createAddressFromString('0x'+'0'.repeat(39)+'7');
const caller=createAddressFromString('0x'+'0'.repeat(39)+'9');
await vm.stateManager.putAccount(self,createAccount({balance:41n}));
await vm.stateManager.putAccount(caller,createAccount({balance:73n}));
const input=Uint8Array.from([0,255,0,97]);
const first=BigInt(keccak256(input));
const predecessor=(first+(1n<<256n)-1n)%(1n<<256n);
const root=BigInt(keccak256(toBeHex(predecessor,32))) & ((1n<<256n)-256n);
const expected={environment:[9n,11n,13n,41n,7n],'balance-high':[41n],selector:[0x12345678n],
 'selector-abi':[0x12345678n<<224n],keccak:[BigInt(keccak256(input))],namespace:[root],
 sha256:[BigInt(sha256(Uint8Array.from([97,98,99])))],
 ripemd160:[BigInt(ripemd160(Uint8Array.from([97,98,99])))],ecrecover:[0n],'ecrecover-malformed':[0n],'ecrecover-valid':[0x2c7536e3605d9c16a7a3d7b1898e529396a65c23n],
 'utf8-name':[]};
assert.deepEqual(programs.map(([name])=>name).sort(),Object.keys(expected).sort(),'exact vector coverage: no omitted or duplicate programs');
const results=[];
for(const [name,code] of programs){
 const r=await vm.evm.runCode({code:Uint8Array.from(code),to:self,caller,value:11n,
  block:{header:{timestamp:13n}},gasLimit:1000000n});
 assert.equal(r.exceptionError,undefined,`${name}: ${r.exceptionError}`);
 const stack=r.runState.stack.getStack();
 assert.deepEqual(stack,expected[name],name);
 if(name==='utf8-name')assert.deepEqual(Array.from(r.runState.memory.read(5,3)),[0x41,0xce,0xbb]);
 results.push({name,bytes:code.length,stack:stack.map(String)});
}
assert.notDeepEqual(expected.selector,expected['selector-abi'],'wrong selector alignment must distinguish');
assert.notEqual(expected.environment[0],expected.environment[4],'CALLER/ADDRESS must distinguish');
console.log(JSON.stringify({fork:'Osaka',evmVersion:version,programs:results,pass:results.length},null,2));
