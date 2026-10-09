#!/usr/bin/env bash
# The rule table (`Solidity/Calculus/Rules.lean`) is written in the
# calculus's notation: every constructor of `Taclet` and `LeanTaclet` states its
# conclusion as a `dl{ … }` (or `dl[J C k]{ … }`) line, solkey's `\find` and
# `\replacewith`, but the ones stated by hand and listed below with why.
# Until W4 `calc-del` the lines were copied from today's `Calculus/Rules`
# and diffed against it (`docs/intrinsic.md`); the scoped table is the only
# one now.  Prints nothing when every line is in notation.
set -euo pipefail
cd "$(dirname "$0")/.."
node - <<'JS'
const { readFileSync } = require('node:fs');
const src = readFileSync('Solidity/Calculus/Rules.lean', 'utf8');
// stated by hand: a block's end is a frame (`Premise.unfold`'s `Ext`), and an
// argument's capture closes the call over its frame (`Premise.argCapture`)
const byHand = { Taclet: ['blockEmpty'], LeanTaclet: ['functionCallArgCapture'] };
let bad = 0;
for (const j of Object.keys(byHand)) {
  const start = src.indexOf(`inductive ${j} (C : Contract)`);
  if (start < 0) { console.log(`no inductive ${j}`); bad++; continue; }
  const rest = src.slice(start);
  const stop = rest.search(/\n(\/-! |inductive |end |section |theorem |def )/);
  const body = stop < 0 ? rest : rest.slice(0, stop);
  for (const c of body.split(/\n  \| /).slice(1)) {
    const name = c.split(/[\s{(:]/)[0];
    const inNotation = /dl(\[[^\]]*\])?\{/.test(c);
    if (!inNotation && !byHand[j].includes(name)) { console.log(`${j}.${name}: not a dl{ } line`); bad++; }
    if (inNotation && byHand[j].includes(name)) { console.log(`${j}.${name}: listed as by hand, but in notation`); bad++; }
  }
}
process.exit(bad ? 1 : 0);
JS
