const fs = require('node:fs');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');
const solcPath = '/workspace/.setup/soljson/soljson-v0.8.34+commit.80d5c536.js';
const compilerHash = crypto.createHash('sha256').update(fs.readFileSync(solcPath)).digest('hex');
assert.equal(compilerHash, 'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8');
const solc = require(solcPath);
const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const source = fs.readFileSync(__dirname + '/Cell.sol', 'utf8');
const records = [];
for (const viaIR of [false, true]) {
 const input = {language: 'Solidity', sources: {'Cell.sol': {content: source}}, settings: {
   viaIR, optimizer: {enabled: false}, evmVersion: 'osaka',
   outputSelection: {'*': {'*': ['evm.bytecode.object', 'storageLayout']}}
 }};
 const output = JSON.parse(compile(JSON.stringify(input), 0, 0));
 assert.deepEqual((output.errors || []).filter(e => e.severity === 'error'), []);
 const cell = output.contracts['Cell.sol'].Cell;
 assert.ok(cell.evm.bytecode.object.length > 0);
 assert.deepEqual(cell.storageLayout.storage.map(x => [x.label, x.slot]), [['saved', '0'], ['captured', '1']]);
 records.push({pipeline: viaIR ? 'viaIR' : 'legacy', creationBytes: cell.evm.bytecode.object.length/2,
   bytecodeSha256: crypto.createHash('sha256').update(Buffer.from(cell.evm.bytecode.object, 'hex')).digest('hex'),
   slots: cell.storageLayout.storage.map(x => [x.label,x.slot])});
}
console.log(JSON.stringify({version: solc.cwrap('solidity_version', 'string', [])(),
 compilerSha256: crypto.createHash('sha256').update(fs.readFileSync(solcPath)).digest('hex'),
 sourceSha256: crypto.createHash('sha256').update(source).digest('hex'), records,
 boundary: 'Compiler acceptance and slot controls only; no EVM execution or compiler-correctness proof.'}, null, 2));
