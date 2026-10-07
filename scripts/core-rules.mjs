#!/usr/bin/env node
// Copies the rule lines of `Solidity/Calculus/Rules.lean` into
// `Solidity/Calculus/Core/Rules.lean`, between its markers
// `-- BEGIN scripts/core-rules.mjs: <J>` and `-- END scripts/core-rules.mjs: <J>`,
// under the scoped judgement's header (`docs/intrinsic.md`, W1 "rules").
//
// A constructor's docstring and its `dl{ … }` line are copied verbatim: under
// `open scoped Solidity.Core.Schema` the same text writes the scoped taclet.
// Only the binders written before the line change, by the substitutions
// below (a scoped value is read in a context, `Val C Γ p`; a loop body's
// frame is `Prog.frame`); a constructor the scoped table states otherwise is
// omitted here and written by hand after the END marker.
//
//   node scripts/core-rules.mjs          rewrite the copy
//   node scripts/core-rules.mjs --check  exit 1 if the copy is stale
//   node scripts/core-rules.mjs --diff   print where the lines differ (exit 1 if they do)
//
// `scripts/check-rule-text.sh` runs `--diff`.

import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const srcPath = join(root, 'Solidity/Calculus/Rules.lean');
const dstPath = join(root, 'Solidity/Calculus/Core/Rules.lean');

const header = (name) =>
  `inductive ${name} (C : Contract) (k : Nat) :\n` +
  "    Modality → {Γ Γ' : Ctx} → Stmt C Γ Γ' → Premise C Γ Γ' → Prop where";

// A value read in the `\find`'s context.
const valInCtx = [[/Val C \./g, 'Val C Γ .']];

const judgements = {
  Taclet: { header: header('Taclet'), omit: [], binders: {} },
  LeanTaclet: {
    header: header('LeanTaclet'),
    // its line escapes to today's call (`‹.call f args hsep ret body›`)
    omit: ['functionCallArgCapture'],
    binders: {
      '*': valInCtx,
      whileInvariantBox: [[/\(Prog\.loopFrame body\)\.isSome = true/, 'Prog.frame body = some (xs, hv)']],
      whileInvariantDiamond: [[/\(Prog\.loopFrame body\)\.isSome = true/, 'Prog.frame body = some (xs, hv)']],
      whileClose: [[/\(Prog\.loopFrame body\)\.isSome = false/, 'Prog.frame body = none']],
      whileNoVariantDiamond: [[/Prog\.loopFrame body/, 'Prog.frame body']],
    },
  },
};

// The lines after `inductive <name> … where` up to the first that is not
// indented.
function blockLines(text, name) {
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

// The constructors of a block: for each, the lines before it (docstring,
// comments), its head (`| name` and its binders, up to the line), and its
// `dl…{ … }` line, braces balanced; and the lines after the last.
function constructors(lines) {
  const ctors = [];
  let pre = [];
  let n = 0;
  while (n < lines.length) {
    const l = lines[n];
    const m = /^  \| (\S+)/.exec(l);
    if (!m) { pre.push(l); n++; continue; }
    const head = [];
    while (n < lines.length && !/dl(\[[^\]]*\])?\{/.test(lines[n])) head.push(lines[n++]);
    const dl = [];
    let depth = 0;
    let started = false;
    while (n < lines.length) {
      const t = lines[n++];
      dl.push(t);
      const at = started ? 0 : t.search(/dl(\[[^\]]*\])?\{/);
      for (const ch of t.slice(Math.max(at, 0))) {
        if (ch === '{') { depth++; started = true; }
        else if (ch === '}') depth--;
      }
      if (started && depth === 0) break;
    }
    ctors.push({ name: m[1], pre, head, dl });
    pre = [];
  }
  return { ctors, post: pre };
}

const subst = (lines, rules) =>
  lines.map((l) => rules.reduce((acc, [re, to]) => acc.replace(re, to), l));

function scoped(text, name, j) {
  const { ctors, post } = constructors(blockLines(text, name));
  const out = [j.header];
  for (const c of ctors) {
    if (j.omit.includes(c.name)) continue;
    const rules = [...(j.binders['*'] ?? []), ...(j.binders[c.name] ?? [])];
    out.push(...c.pre, ...subst(c.head, rules), ...c.dl);
  }
  out.push(...post);
  return out.join('\n');
}

// What must agree: every constructor's docstring and line, binders aside.
function comparable(text, name, omit) {
  const { ctors } = constructors(blockLines(text, name));
  return ctors.filter((c) => !omit.includes(c.name))
    .flatMap((c) => [...c.pre, `  | ${c.name}`, ...c.dl]);
}

const src = readFileSync(srcPath, 'utf8');
let dst = readFileSync(dstPath, 'utf8');

if (process.argv.includes('--diff')) {
  let bad = false;
  for (const [name, j] of Object.entries(judgements)) {
    const a = comparable(src, name, j.omit);
    const b = comparable(dst, name, []);
    const len = Math.max(a.length, b.length);
    for (let i = 0; i < len; i++) {
      if (a[i] !== b[i]) {
        console.log(`${name}: Core/Rules.lean differs from Rules.lean at constructor line ${i + 1}:`);
        console.log(`< ${a[i] ?? ''}\n> ${b[i] ?? ''}`);
        console.log('(run node scripts/core-rules.mjs)');
        bad = true;
        break;
      }
    }
  }
  process.exit(bad ? 1 : 0);
}

const old = dst;
for (const [name, j] of Object.entries(judgements)) {
  const begin = `-- BEGIN scripts/core-rules.mjs: ${name}`;
  const end = `-- END scripts/core-rules.mjs: ${name}`;
  const a = dst.indexOf(begin);
  const b = dst.indexOf(end);
  if (a < 0 || b < a) throw new Error(`markers for ${name} missing in ${dstPath}`);
  dst = dst.slice(0, a) + begin + '\n' + scoped(src, name, j) + '\n' + dst.slice(b);
}
if (process.argv.includes('--check')) {
  if (dst !== old) {
    console.error('Solidity/Calculus/Core/Rules.lean is stale: run node scripts/core-rules.mjs');
    process.exit(1);
  }
} else if (dst !== old) {
  writeFileSync(dstPath, dst);
}
