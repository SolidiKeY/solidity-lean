import {readFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
const hash = b => createHash('sha256').update(b).digest('hex');
const require = createRequire(import.meta.url);
const binary = process.argv[2];
const expectedHash = '6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390';
if (hash(readFileSync(binary)) !== expectedHash) throw Error('compiler hash mismatch');
const solc = require(binary);
const version = solc.cwrap('solidity_version','string',[])();
if (version !== '0.8.38+commit.1835d247.Emscripten.clang') throw Error('compiler version mismatch');
const compile = solc.cwrap('solidity_compile','string',['string','number','number']);
const cases = JSON.parse(readFileSync(new URL('./cases.json',import.meta.url)));
if (cases.length !== 12 || new Set(cases.map(r=>r.id)).size !== 12) throw Error('case inventory');
const products = new Set();
for (const row of cases) {
  if (!['constant','regular','immutable'].includes(row.kind) || !['pure','view'].includes(row.baseMutability) || typeof row.viaIR !== 'boolean') throw Error('case product field');
  const key = [row.kind,row.baseMutability,row.viaIR].join(':');
  if (products.has(key)) throw Error('duplicate product row');
  products.add(key);
  const expected = row.kind === 'constant' || row.baseMutability === 'view';
  if (row.expected !== expected || row.expectedGetterABI !== (expected?'view':null)) throw Error(row.id+': inconsistent frozen expectation');
}
const results = cases.map(row => {
  const source = readFileSync(new URL(row.file,import.meta.url),'utf8');
  const input = {language:'Solidity',sources:{'Case.sol':{content:source}},settings:{viaIR:row.viaIR,outputSelection:{'*':{'*':['abi','evm.bytecode.object']}}}};
  const result = JSON.parse(compile(JSON.stringify(input),0,0));
  const errors = (result.errors??[]).filter(e=>e.severity==='error').map(e=>({code:e.errorCode??null,type:e.type,message:e.message}));
  const accepted = errors.length === 0;
  if (accepted !== row.expected) throw Error(row.id+': compiler verdict mismatch');
  if (!accepted && !errors.some(e=>e.message.includes('state mutability'))) throw Error(row.id+': unexpected refusal family');
  const abi = result.contracts?.['Case.sol']?.C?.abi;
  const getter = abi?.find(e=>e.type==='function' && e.name==='f');
  const bytecode = result.contracts?.['Case.sol']?.C?.evm?.bytecode?.object;
  if (accepted && getter?.stateMutability !== row.expectedGetterABI) throw Error(row.id+': ABI getter must remain view');
  if (accepted && (!bytecode || !/^[0-9a-f]+$/i.test(bytecode))) throw Error(row.id+': code generation missing');
  return {...row,sourceSha256:hash(source),accepted,errors,getterABI:getter?.stateMutability??null,bytecodeBytes:bytecode?bytecode.length/2:0,bytecodeSha256:bytecode?hash(Buffer.from(bytecode,'hex')):null};
});
process.stdout.write(JSON.stringify({version,compilerSha256:expectedHash,outputSelection:['abi','evm.bytecode.object'],boundary:'Compiler code-generation differential only; no EVM execution or kernel Solidity-equivalence claim.',rows:results},null,2)+'\n');
