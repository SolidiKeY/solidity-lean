#!/usr/bin/env node
// Copies the rule lines of `Solidity/Calculus/Rules.lean` into
// `Solidity/Calculus/Core/Rules.lean`, between its markers
// `-- BEGIN scripts/core-rules.mjs: <J>` and `-- END scripts/core-rules.mjs: <J>`,
// under the scoped judgement's header (`docs/intrinsic.md`, W1 "rules").
// The constructor lines are copied verbatim: under
// `open scoped Solidity.Core.Schema` the same `dl{ … }` text writes the
// scoped taclet.  `scripts/check-rule-text.sh` checks the two copies agree.
//
//   node scripts/core-rules.mjs          rewrite the copy
//   node scripts/core-rules.mjs --check  exit 1 if the copy is stale

import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const srcPath = join(root, 'Solidity/Calculus/Rules.lean');
const dstPath = join(root, 'Solidity/Calculus/Core/Rules.lean');

// The judgements copied, with their scoped headers.
const judgements = {
  Taclet:
    'inductive Taclet (C : Contract) (k : Nat) :\n' +
    '    Modality → {Γ Γ\' : Ctx} → Stmt C Γ Γ\' → Premise C Γ Γ\' → Prop where',
};

// The constructor lines of `inductive <name> … where`: every line after the
// header up to the first one that is not indented (blank lines inside kept,
// trailing ones dropped).
export function ruleLines(text, name) {
  const lines = text.split('\n');
  const i = lines.findIndex((l) => l.startsWith(`inductive ${name} `));
  if (i < 0) throw new Error(`no inductive ${name}`);
  let j = i;
  while (!lines[j].trimEnd().endsWith('where')) j++;
  const out = [];
  for (let n = j + 1; n < lines.length; n++) {
    const l = lines[n];
    if (l !== '' && !l.startsWith(' ')) break;
    out.push(l);
  }
  while (out.length && out[out.length - 1] === '') out.pop();
  return out;
}

const src = readFileSync(srcPath, 'utf8');
let dst = readFileSync(dstPath, 'utf8');
const old = dst;
for (const [name, header] of Object.entries(judgements)) {
  const begin = `-- BEGIN scripts/core-rules.mjs: ${name}`;
  const end = `-- END scripts/core-rules.mjs: ${name}`;
  const a = dst.indexOf(begin);
  const b = dst.indexOf(end);
  if (a < 0 || b < a) throw new Error(`markers for ${name} missing in ${dstPath}`);
  const body = [header, ...ruleLines(src, name)].join('\n');
  dst = dst.slice(0, a) + begin + '\n' + body + '\n' + dst.slice(b);
}
if (process.argv.includes('--check')) {
  if (dst !== old) {
    console.error('Solidity/Calculus/Core/Rules.lean is stale: run node scripts/core-rules.mjs');
    process.exit(1);
  }
} else if (dst !== old) {
  writeFileSync(dstPath, dst);
}
