// Run: node check-solc.cjs /absolute/path/to/soljson.js
// This checks external layout metadata; it does not execute an EVM.
const fs = require('node:fs');
const path = require('node:path');
const assert = require('node:assert/strict');
const solc = require(path.resolve(process.argv[2]));
const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const version = solc.cwrap('solidity_version', 'string', [])();
const source = fs.readFileSync(path.join(__dirname, 'Layout.sol'), 'utf8');
const out = JSON.parse(compile(JSON.stringify({language: 'Solidity',
  sources: {'Layout.sol': {content: source}},
  settings: {outputSelection: {'*': {'*': ['storageLayout']}}}}), 0, 0));
assert.equal((out.errors || []).filter(e => e.severity === 'error').length, 0,
  JSON.stringify(out.errors));
function layout(name, expected) {
  const l = out.contracts['Layout.sol'][name].storageLayout;
  assert.deepEqual(l.storage.map(x => [x.label, x.slot, x.offset]), expected);
  return l;
}
layout('Packing', [['a','0',0],['b','0',1],['flags','1',0],['tail','2',0]]);
layout('Mixed', [['a','0',0],['n','1',0],['b','2',0],['c','2',1]]);
layout('Derived', [['baseFlag','0',0],['derivedFlag','0',1],['tail','1',0]]);
const l = layout('Shapes', [['packed','0',0],['afterPacked','1',0],
  ['wallet','2',0],['fixedWords','4',0],['words','7',0],['bits','8',0],['wallets','9',0]]);
const types = Object.values(l.types);
const packed = types.find(t => t.label === 'struct Shapes.Packed');
assert.equal(packed.numberOfBytes, '32');
assert.deepEqual(packed.members.map(x => [x.label,x.slot,x.offset]), [['a','0',0],['b','0',1]]);
const wallet = types.find(t => t.label === 'struct Shapes.Wallet');
assert.deepEqual(wallet.members.map(x => [x.label,x.slot,x.offset]), [['owner','0',0],['stash','1',0]]);
assert.equal(types.find(t => t.label === 'uint256[3]').numberOfBytes, '96');
for (const name of ['uint256[]', 'bool[]'])
  assert.equal(types.find(t => t.label === name).encoding, 'dynamic_array');
assert.equal(types.find(t => t.label === 'bool').numberOfBytes, '1');
console.log('PASS solc', version, 'packing, mixed types, structs, fixed/dynamic arrays, mappings in structs, inheritance');
console.log(JSON.stringify(out.contracts['Layout.sol'], null, 2));
