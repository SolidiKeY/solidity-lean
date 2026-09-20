#!/usr/bin/env node
// The paper-rule enumeration, checked against the paper.
//
// `Solidity/Calculus/PaperRules.lean`'s `PaperRule` is one constructor per
// distinct `name = {...}` the paper's `\DeclarePaperRule` blocks declare.  Lean
// checks the correspondence to `RuleName` (`paperOrigin` is a total match, and
// `paper_rules_partitioned` says every paper rule is claimed or excused); it
// cannot check the enumeration against the `.tex` files.  This script does,
// in both directions: a paper name with no constructor, or a constructor the
// paper no longer declares, fails.
//
//   node scripts/check-paper-rules.mjs [--paper ../Pre-licenciate-paper]
//
// Seconds: two files' worth of regex matches.  A name the paper declares twice
// (the `unfold_*` templates, in storage and memory; the `arith-checked.tex`
// twins) is one constructor, so the comparison is on the set of names.

import { readFileSync, readdirSync, existsSync } from 'node:fs'
import { join } from 'node:path'

const argv = process.argv.slice(2)
const paperIx = argv.indexOf('--paper')
const paperDir = paperIx >= 0 ? argv[paperIx + 1] : '../Pre-licenciate-paper'
const leanFile = 'Solidity/Calculus/PaperRules.lean'

const rulesDir = join(paperDir, 'rules')
if (!existsSync(rulesDir)) {
  console.log(`paper-rules: no paper checkout at ${paperDir}; skipping.`)
  process.exit(0)
}

/** Every `name = {...}` inside a `\DeclarePaperRule{id}{...}` block, `\_` read as `_`. */
function paperRules(dir) {
  const out = new Map()
  for (const f of readdirSync(dir)) {
    if (!f.endsWith('.tex')) continue
    const text = readFileSync(join(dir, f), 'utf8')
    const blocks = text.split(/\\DeclarePaperRule\{/).slice(1)
    for (const block of blocks) {
      const m = /name\s*=\s*\{([^}]*)\}/.exec(block)
      if (!m) continue
      const name = m[1].replace(/\\_/g, '_').trim()
      if (!out.has(name)) out.set(name, [])
      out.get(name).push(f)
    }
  }
  return out
}

/** Every constructor of `PaperRule`. */
function leanRules(file) {
  const text = readFileSync(file, 'utf8')
  const start = text.indexOf('inductive PaperRule where')
  const body = text.slice(start, text.indexOf('deriving DecidableEq, Repr', start))
  return new Set([...body.matchAll(/^\s*\|\s*([A-Za-z_][A-Za-z0-9_]*)\s*$/gm)].map((m) => m[1]))
}

const paper = paperRules(rulesDir)
const lean = leanRules(leanFile)

let failed = 0
for (const [name, where] of paper) {
  if (lean.has(name)) continue
  console.error(`missing: ${name} (declared in ${where.join(', ')}) has no PaperRule constructor`)
  failed = 1
}
for (const name of lean) {
  if (paper.has(name)) continue
  console.error(`stale: PaperRule.${name} is in no \\DeclarePaperRule block`)
  failed = 1
}

if (failed) {
  console.error('paper-rules: the enumeration and rules/*.tex disagree.')
  process.exit(1)
}
console.log(`paper-rules: ${paper.size} paper names, ${lean.size} constructors, none unaccounted for.`)
