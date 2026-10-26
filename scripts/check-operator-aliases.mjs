#!/usr/bin/env node
/** Independent solc/EVM reference. Dependencies are outside the Lean package.
 * node scripts/check-operator-aliases.mjs SOLJSON_FILE NODE_MODULES_DIRECTORY
 * @ethereumjs/{vm,common,util} 10.1.3; ethers 6.17.0.
 */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { resolve } from 'node:path';
const [compiler, modules] = process.argv.slice(2);
if (!compiler || !modules) throw new Error('expected compiler file and external node_modules directory');
assert.equal(createHash('sha256').update(readFileSync(compiler)).digest('hex'),
  '6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390');
const require = createRequire(resolve(modules, 'reference.cjs'));
const { createVM } = require('@ethereumjs/vm');
const { Common, Mainnet, Hardfork } = require('@ethereumjs/common');
const { hexToBytes, bytesToHex } = require('@ethereumjs/util');
const { Interface } = require('ethers');
const solc = createRequire(import.meta.url)(resolve(compiler));
const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
assert.match(solc.cwrap('solidity_version', 'string', [])(), /^0\.8\.38\+commit\.1835d247/);
const source = readFileSync(new URL('../tests/operators-0.8.38/OperatorAliases.sol', import.meta.url), 'utf8');
const errors = out => (out.errors ?? []).filter(e => e.severity === 'error');
const panic = code => '0x4e487b71' + code.toString(16).padStart(64, '0');
const positive = ['paddingCapture', 'numeric', 'comparisons', 'unary', 'nominal', 'order', 'nested', 'customZero', 'lazy', 'wrappingBody'];
const negative = [ ['checkedBody', panic(0x11)], ['discardedUnary', panic(0x11)],
  ['failureOrderRevert', '0x'], ['failureOrderPanic', panic(1)], ['falseBuiltin', panic(1)],
  ['castOrderBounds', panic(0x32)], ['castOrderDivision', panic(0x12)],
  ['lengthOrderDivision', panic(0x12)], ['modularOrderDivision', panic(0x12)] ];
let executed = 0;
for (const viaIR of [false, true]) {
  const out = JSON.parse(compile(JSON.stringify({ language: 'Solidity',
    sources: { 'OperatorAliases.sol': { content: source } }, settings: {
      viaIR, evmVersion: 'cancun', optimizer: { enabled: true },
      outputSelection: { '*': { '*': ['abi', 'evm.deployedBytecode.object'] } }
    } }), 0, 0));
  assert.deepEqual(errors(out), []);
  const c = out.contracts['OperatorAliases.sol'].OperatorAliases;
  const iface = new Interface(c.abi);
  const vm = await createVM({ common: new Common({ chain: Mainnet, hardfork: Hardfork.Cancun }) });
  const code = hexToBytes('0x' + c.evm.deployedBytecode.object);
  for (const name of positive) {
    const r = await vm.evm.runCode({ code, data: hexToBytes(iface.encodeFunctionData(name, [])), gasLimit: 30000000n });
    assert.equal(r.exceptionError, undefined, `${viaIR ? 'viaIR' : 'legacy'} ${name}`);
    executed++;
  }
  for (const [name, expected] of negative) {
    const r = await vm.evm.runCode({ code, data: hexToBytes(iface.encodeFunctionData(name, [])), gasLimit: 30000000n });
    assert.ok(r.exceptionError, name);
    assert.equal(bytesToHex(r.returnValue), expected, name);
    executed++;
  }
}
const invalid = [
  ['compound assignment', 'type N is uint; using {f as +} for N global; function f(N a,N b)pure returns(N){return a;} contract C{function g(N a,N b)external pure returns(N){a+=b;return a;}}', '7366', 'TypeError'],
  ['non-pure', 'type N is uint; using {f as +} for N global; function f(N a,N b)view returns(N){return a;}', '7775', 'TypeError'],
  ['wrong result', 'type N is uint; using {f as +} for N global; function f(N a,N b)pure returns(uint){return 0;}', '7743', 'TypeError'],
  ['comparison result', 'type N is uint; using {f as ==} for N global; function f(N a,N b)pure returns(N){return a;}', '7743', 'TypeError'],
  ['mixed nominal operands', 'type N is uint; type M is uint; using {f as +} for N global; function f(N a,M b)pure returns(N){return a;}', '1884', 'TypeError'],
  ['illegal unary arity', 'type N is uint; using {f as ~} for N global; function f(N a,N b)pure returns(N){return a;}', '1884', 'TypeError'],
  ['non-free target', 'type N is uint; library L{function f(N a,N b)internal pure returns(N){return a;}} using {L.f as +} for N global;', '7775', 'TypeError'],
  ['ambiguous source overload', 'type N is uint;type M is uint;using {f as +} for N global;function f(N a,N b)pure returns(N){return a;}function f(M a,M b)pure returns(M){return a;}', '9589', 'DeclarationError']
];
for (const [name, content, errorCode, type] of invalid) {
  const out = JSON.parse(compile(JSON.stringify({ language: 'Solidity',
    sources: { 'Bad.sol': { content: 'pragma solidity 0.8.38;' + content } },
    settings: { outputSelection: { '*': { '': ['ast'] } } } }), 0, 0));
  assert.ok(errors(out).some(e => e.errorCode === errorCode && e.type === type),
    `${name} must be rejected upstream with ${type} ${errorCode}`);
}
// The committed modern fixtures must carry every nominal operand identity.
function nodes(j) {
  if (Array.isArray(j)) return j.flatMap(nodes);
  if (j && typeof j === 'object') return (j.nodeType ? [j] : []).concat(Object.values(j).flatMap(nodes));
  return [];
}
for (const fixture of ['OperatorAliases.ast.json', 'OperatorAliasesIR.ast.json']) {
  const j = JSON.parse(readFileSync(new URL('../tests/operators-0.8.38/' + fixture, import.meta.url)));
  const ns = nodes(j.ast), byId = new Map(ns.filter(n => n.id !== undefined).map(n => [n.id, n]));
  const seen = new Set();
  for (const n of ns.filter(n => ['BinaryOperation', 'UnaryOperation'].includes(n.nodeType) && 'function' in n)) {
    const d = byId.get(n.function);
    assert.equal(d?.kind, 'freeFunction'); assert.equal(d.stateMutability, 'pure');
    const ps = d.parameters.parameters, as = n.nodeType === 'UnaryOperation' ? [n.subExpression] : [n.leftExpression, n.rightExpression];
    assert.equal(ps.length, as.length);
    const nominal = ps[0].typeDescriptions.typeIdentifier;
    assert.ok(nominal?.startsWith('t_userDefinedValueType'));
    for (const a of as) assert.equal(a.typeDescriptions.typeIdentifier, nominal);
    if (ps[0].typeDescriptions.typeString === 'N') seen.add(`${as.length}:${n.operator}`);
  }
  assert.equal(seen.size, 16, 'all legal N signatures must execute in the fixture');
}
console.log(`${executed} solc 0.8.38/EVM execution cases, ${invalid.length} compiler rejection cases, and both nominal metadata fixtures passed`);
