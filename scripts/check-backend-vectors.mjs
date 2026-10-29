#!/usr/bin/env node
// Agreement vectors for the backend's byte encoding (`Solidity/Backend/`,
// docs/feature-work/backend-assembler.md, checkpoint 3). Two references:
//
// * the vendored EVMYulLean tables, read from their source
//   (`Bridge/vendor/EvmYul/EVM/Instr.lean`: `parseInstr`;
//   `Bridge/vendor/EvmYul/EVM/Semantics.lean`: `argOnNBytesOfInstr`),
//   not edited and not run (the Bridge needs Mathlib);
// * EthereumJS at Osaka (pinned in scripts/evm-vectors/package.json): its
//   opcode table (`getOpcodesForHF`) and its jump-destination scan
//   (`Interpreter._getValidJumpDestinations`) on randomized byte strings.
//
// It writes them as Lean literals to `Solidity/Backend/EvmVectors.lean`,
// whose `#guard`s check `byteName`, `immWidth` and `jumpdests` against them.
//
// Usage: npm ci --ignore-scripts --prefix scripts/evm-vectors
//        node scripts/check-backend-vectors.mjs [--write]
// Without --write: exit 1 when the committed Lean file differs from what the
// references give now.
import {readFileSync, writeFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {resolve, dirname} from 'node:path';
import {fileURLToPath} from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const modules = resolve(root, 'scripts/evm-vectors/node_modules');
const req = createRequire(resolve(modules, 'reference.cjs'));
const {Common, Mainnet, Hardfork} = req('@ethereumjs/common');
const {getOpcodesForHF, paramsEVM} = req('@ethereumjs/evm');
const {Interpreter} = req(resolve(modules, '@ethereumjs/evm/dist/cjs/interpreter.js'));
const version = (m) => JSON.parse(readFileSync(resolve(modules, m, 'package.json'), 'utf8')).version;
const evmVersion = version('@ethereumjs/evm');
const commonVersion = version('@ethereumjs/common');

// --- EVMYulLean, from its source -------------------------------------------
const instr = readFileSync(resolve(root, 'Bridge/vendor/EvmYul/EVM/Instr.lean'), 'utf8');
const stripComments = (t) => t.replace(/--.*$/gm, '');
const parseBody = stripComments(instr.slice(instr.indexOf('def parseInstr')));
const evmYul = new Map();
for (const m of parseBody.matchAll(/\|\s*0x([0-9a-f]{2})\s*=>\s*some\s*\.(\w+)/g)) {
  evmYul.set(parseInt(m[1], 16), m[2]);
}
if (!/\|\s*_\s*=>\s*some\s*\.INVALID/.test(parseBody)) throw new Error('parseInstr default changed');
// Every arm must have been read: a differently written arm fails loudly.
if ((parseBody.match(/^\s*\|/gm) ?? []).length !== evmYul.size + 1) throw new Error('unread parseInstr arm');
const sem = readFileSync(resolve(root, 'Bridge/vendor/EvmYul/EVM/Semantics.lean'), 'utf8');
const argBody = stripComments(sem.slice(sem.indexOf('def argOnNBytesOfInstr'), sem.indexOf('def N ')));
const evmYulWidth = new Map();
for (const m of argBody.matchAll(/\|\s*\.Push\s*\.(PUSH\d+)\s*=>\s*(\d+)/g)) evmYulWidth.set(m[1], +m[2]);
if (!/\|\s*_\s*=>\s*0/.test(argBody) || (argBody.match(/^\s*\|/gm) ?? []).length !== evmYulWidth.size + 1) {
  throw new Error('unread argOnNBytesOfInstr arm');
}
const evmYulRows = [...evmYul].sort((a, b) => a[0] - b[0])
  .map(([b, name]) => [b, name, evmYulWidth.get(name) ?? 0]);

// --- EthereumJS at Osaka ---------------------------------------------------
const common = new Common({chain: Mainnet, hardfork: Hardfork.Osaka, params: paramsEVM});
const ops = getOpcodesForHF(common).opcodes;
const ejsRows = [...ops].sort((a, b) => a[0] - b[0]).map(([b, op]) => [b, op.fullName]);
const analyse = (code) => {
  const self = {common, lookupOpInfo: () => undefined};
  return Interpreter.prototype._getValidJumpDestinations.call(self, Uint8Array.from(code));
};
const scan = (code) => {
  const {jumps} = analyse(code);
  return [...jumps.keys()].filter((i) => jumps[i] === 1);
};

// Randomized byte strings, biased towards PUSHn, JUMPDEST and undefined bytes.
let seed = 0x2545f491;
const next = () => { seed ^= seed << 13; seed >>>= 0; seed ^= seed >>> 17; seed ^= seed << 5; seed >>>= 0; return seed; };
// 0xe6-0xe8 take an immediate after Osaka (EIP-8024): a later pin would show here.
const undefinedBytes = [0x0c, 0x0f, 0x21, 0x4c, 0xa5, 0xe6, 0xe7, 0xe8, 0xef, 0xf6, 0xfb, 0xfc];
const randomByte = () => {
  const r = next() % 10;
  if (r < 3) return 0x5b;
  if (r < 6) return 0x5f + (next() % 33);
  if (r < 7) return undefinedBytes[next() % undefinedBytes.length];
  return next() % 256;
};
const cases = [];
for (let k = 0; k < 300; k++) {
  const len = next() % 72;
  const code = Array.from({length: len}, randomByte);
  cases.push([code, scan(code)]);
}

// Randomized encoded programs: any Osaka opcode, PUSHn with n random bytes.
const plainOps = ejsRows.map(([b]) => b).filter((b) => b < 0x5f || b > 0x7f);
const programs = [];
for (let k = 0; k < 200; k++) {
  const len = next() % 24;
  const code = [];
  for (let i = 0; i < len; i++) {
    if (next() % 2 === 0) code.push(plainOps[next() % plainOps.length]);
    else {
      const n = next() % 33;
      code.push(0x5f + n);
      for (let j = 0; j < n; j++) code.push(next() % 256);
    }
  }
  const {jumps, pushes} = analyse(code);
  const pushList = Object.keys(pushes).map(Number).sort((a, b) => a - b).map((o) => [o, pushes[o]]);
  programs.push([code, [...jumps.keys()].filter((i) => jumps[i] === 1), pushList]);
}
const hexOf = (c) => c.map((b) => b.toString(16).padStart(2, '0')).join('');

// --- The Lean file ---------------------------------------------------------
const hex = (b) => '0x' + b.toString(16).padStart(2, '0');
const list = (xs, f) => '[' + xs.map(f).join(', ') + ']';
const chunks = (xs, n) => Array.from({length: Math.ceil(xs.length / n)}, (_, i) => xs.slice(i * n, i * n + n));
const lean = `/-
Generated by \`node scripts/check-backend-vectors.mjs --write\`; do not edit.
EthereumJS @ethereumjs/evm ${evmVersion}, @ethereumjs/common ${commonVersion}, at Osaka; EVMYulLean from Bridge/vendor/EvmYul.
-/
import Solidity.Backend.Assembler

/-!
# Agreement vectors (G45.05 checkpoint 3)

The opcode tables of EthereumJS at Osaka and of the vendored EVMYulLean,
and the jump-destination scans of EthereumJS and of EVMYulLean's \`D_J_aux\`
(transliterated over its extracted table) on 300 randomized byte strings,
against \`byteName\`, \`immWidth\` and \`jumpdests\`
(\`docs/feature-work/backend-assembler.md\`, checkpoint 3).
-/

namespace Solidity.Backend.EvmVectors

open Solidity.Backend

/-- EthereumJS's Osaka opcodes: byte and name. -/
def ethereumjsOsaka : List (Nat × String) :=
  ${list(ejsRows, ([b, n]) => `(${hex(b)}, "${n}")`)}

/-- EVMYulLean's \`parseInstr\` arms: byte, name and \`argOnNBytesOfInstr\`;
every other byte parses as \`INVALID\`. -/
def evmYulTable : List (Nat × String × Nat) :=
  ${list(evmYulRows, ([b, n, w]) => `(${hex(b)}, "${n}", ${w})`)}

/-- The bytes of a hex string (two digits per byte). -/
def ofHex (s : String) : List Nat :=
  let d : Char → Nat := fun c => if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List Nat
    | a :: b :: rest => (16 * d a + d b) :: go rest
    | _ => []
  go s.toList

/-- Randomized code (hex) and EthereumJS's valid jump destinations in it. -/
def ethereumjsJumpdests : List (String × List Nat) := List.flatten [
${chunks(cases, 20).map((cs) => '  [' + cs.map(([c, j]) => `("${c.map((b) => b.toString(16).padStart(2, '0')).join('')}", ${list(j, String)})`).join(',\n   ') + ']').join(',\n')}]

-- Every byte EthereumJS defines at Osaka is ours, by name, and nothing else is.
#guard ethereumjsOsaka.all fun (b, n) => byteName (UInt8.ofNat b) == some n
#guard (List.range 256).all fun b =>
  (byteName (UInt8.ofNat b)).isSome == ethereumjsOsaka.any (·.1 == b)

-- EVMYulLean agrees on every byte it parses, names and immediate widths alike.
#guard evmYulTable.all fun (b, n, w) =>
  byteName (UInt8.ofNat b) == some n && immWidth (UInt8.ofNat b) == w
-- It parses every Osaka opcode except CLZ (EIP-7939, after its pinned fork),
-- which it reads as INVALID, like an undefined byte.
#guard (List.range 256).filter (fun b => (byteName (UInt8.ofNat b)).isSome && b != 0x1e) =
  evmYulTable.map (·.1)

-- The jump-destination scan agrees with EthereumJS's on every randomized case.
#guard ethereumjsJumpdests.all fun (c, j) => jumpdests ((ofHex c).map UInt8.ofNat) == j

/-- Randomized encoded programs (hex), with EthereumJS's valid jump
destinations and the value it records for each \`PUSH1\`–\`PUSH32\`, keyed
by the offset of the immediate. -/
def ethereumjsPrograms : List (String × List Nat × List (Nat × Nat)) := List.flatten [
${chunks(programs, 20).map((ps) => '  [' + ps.map(([c, j, pu]) => `("${hexOf(c)}", ${list(j, String)}, ${list(pu, ([o, v]) => `(${o}, ${v})`)})`).join(',\n   ') + ']').join(',\n')}]

/-- The \`PUSH1\`–\`PUSH32\` immediates of a program: the offset of each
immediate and its big-endian value. -/
def pushValues (p : Program) : List (Nat × Nat) :=
  ((List.range p.length).zip p).filterMap fun (k, i) =>
    match i with
    | .push n imm => if n.val = 0 then none else some (offset p k + 1, ofBytesBE imm.toList)
    | .op _ => none

-- Each program decodes, re-encodes to its bytes, has EthereumJS's jump
-- destinations, and pushes the values EthereumJS reads.
#guard ethereumjsPrograms.all fun (c, j, pu) =>
  let bytes := (ofHex c).map UInt8.ofNat
  match decode bytes with
  | some p => encode p == bytes && jumpdests bytes == j && pushValues p == pu
  | none => false

/-- EVMYulLean's \`parseInstr\` read through its table: name and immediate
width, \`INVALID\` (no immediate) for every byte without an arm. -/
def evmYulParse (b : Nat) : String × Nat :=
  ((evmYulTable.find? (·.1 == b)).map (·.2)).getD ("INVALID", 0)

/-- EVMYulLean's \`D_J_aux\` (\`Bridge/vendor/EvmYul/EVM/Semantics.lean\`),
transliterated: from offset \`i\`, record \`i\` when it parses as
\`JUMPDEST\`, then go to \`N i\` (\`i + 1 + argOnNBytesOfInstr\`), until
the offset leaves the code. \`fuel\` replaces its \`partial\`. -/
def evmYulDJAux (c : List Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, i =>
    match c[i]? with
    | none => []
    | some b =>
      let (n, w) := evmYulParse b
      (if n == "JUMPDEST" then [i] else []) ++ evmYulDJAux c fuel (i + 1 + w)

-- EVMYulLean's reading of every byte has our immediate width and our JUMPDEST.
#guard (List.range 256).all fun b =>
  (evmYulParse b).2 == immWidth (UInt8.ofNat b) && ((evmYulParse b).1 == "JUMPDEST") == (b == 0x5b)
-- Its jump-destination scan agrees with ours on every randomized case.
#guard ethereumjsJumpdests.all fun (c, _) =>
  evmYulDJAux (ofHex c) ((ofHex c).length + 1) 0 == jumpdests ((ofHex c).map UInt8.ofNat)
#guard ethereumjsPrograms.all fun (c, _, _) =>
  evmYulDJAux (ofHex c) ((ofHex c).length + 1) 0 == jumpdests ((ofHex c).map UInt8.ofNat)

/-- EVMYulLean's \`decode\` immediate, transliterated: the big-endian value
(\`uInt256OfByteArray\`) of the bytes \`extract'\` takes after the opcode at
\`o\`, which on code that ends early are fewer than the width. -/
def evmYulPushValue (c : List Nat) (o w : Nat) : Nat :=
  ((c.drop (o + 1)).take w).foldl (fun acc b => acc * 256 + b) 0

-- On encoded programs its immediates are our values at every PUSH1–PUSH32.
#guard ethereumjsPrograms.all fun (c, _, _) =>
  match decode ((ofHex c).map UInt8.ofNat) with
  | some p => (pushValues p).all fun (o, v) =>
      evmYulPushValue (ofHex c) (o - 1) (evmYulParse ((ofHex c).getD (o - 1) 0)).2 == v
  | none => false
-- On a truncated final PUSH it reads the bytes present; EthereumJS pads on the right.
#guard evmYulPushValue [0x61, 0x01] 0 2 = 0x01
#guard (${analyse([0x61, 0x01]).pushes[1]} : Nat) = 0x0100

end Solidity.Backend.EvmVectors
`;

const out = resolve(root, 'Solidity/Backend/EvmVectors.lean');
if (process.argv.includes('--write')) {
  writeFileSync(out, lean);
  console.log(`wrote ${out}: ${ejsRows.length} EthereumJS opcodes, ${evmYulRows.length} EVMYulLean arms, ${cases.length} scans, ${programs.length} programs`);
} else {
  let cur = '';
  try { cur = readFileSync(out, 'utf8'); } catch {}
  if (cur !== lean) { console.log('DRIFT: Solidity/Backend/EvmVectors.lean differs; rerun with --write'); process.exit(1); }
  console.log(`ok: ${ejsRows.length} EthereumJS opcodes, ${evmYulRows.length} EVMYulLean arms, ${cases.length} scans, ${programs.length} programs`);
}
