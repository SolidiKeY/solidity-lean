#!/usr/bin/env node
// The theory-rule table, checked against the paper.
//
// `Solidity/Theory/Rewrite.lean`'s `TheoryRule` is one constructor per rewrite
// rule of the paper's signature.  Lean checks the table in one direction --
// `lemmaNames` is a total match over double-backtick names, so a constructor
// without a theorem, or a theorem that does not exist, is a build failure.
// This script checks the other direction: a rule the *paper* declares and the
// enumeration has no constructor for.  And the reverse of that: a constructor
// the paper does not declare must be in `TheoryRule.paperAbsent`, the list of
// Lean's additions the paper is to gain (this repository is the source of
// truth; the paper is ported from it).  Those are printed, not failed on.
//
//   node scripts/check-theory-rules.mjs [--paper ../Pre-licenciate-paper]
//
// Seconds: it reads two files' worth of regex matches.  A rule that is
// deliberately absent goes in KNOWN_ABSENT below, with its reason, which is
// what keeps "not ported" a claim with an argument rather than a silence.

import { readFileSync, readdirSync, existsSync } from 'node:fs'
import { join } from 'node:path'

const argv = process.argv.slice(2)
const paperIx = argv.indexOf('--paper')
const paperDir = paperIx >= 0 ? argv[paperIx + 1] : '../Pre-licenciate-paper'
const leanFile = 'Solidity/Theory/Rewrite.lean'

/** Paper rules with no constructor, and why. */
const KNOWN_ABSENT = {
  selectDelNodeMap:
    'architectural: a `Seg` carries no `MapField` (docs/lean-key-rule-map.md)',
  expandInUintNTrue: 'the paper lists the arithmetic expansions as not implemented',
  expandInIntNTrue: 'the paper lists the arithmetic expansions as not implemented',
  expandInUintN: 'the paper lists the arithmetic expansions as not implemented',
  expandInIntN: 'the paper lists the arithmetic expansions as not implemented',
}

if (!existsSync(paperDir)) {
  console.log(`theory-rules: no paper checkout at ${paperDir}; skipping.`)
  process.exit(0)
}

/** Every `\namedRwRule{\handle}{name}{...}` / `\namedRwRuleIf` the paper declares. */
function paperRules(dir) {
  const out = new Map()
  for (const sub of ['sections', '.']) {
    const here = join(dir, sub)
    if (!existsSync(here)) continue
    for (const f of readdirSync(here)) {
      if (!f.endsWith('.tex')) continue
      const text = readFileSync(join(here, f), 'utf8')
      const re = /\\namedRwRule(?:If|WC)?\{\\[A-Za-z]+\}\{([A-Za-z][A-Za-z0-9]*)\}/g
      let m
      while ((m = re.exec(text))) out.set(m[1], `${sub}/${f}`)
    }
  }
  return out
}

/** Every constructor of `TheoryRule`. */
function leanRules(file) {
  const text = readFileSync(file, 'utf8')
  const body = text.slice(
    text.indexOf('inductive TheoryRule where'),
    text.indexOf('deriving DecidableEq, Repr, Inhabited'),
  )
  return new Set([...body.matchAll(/^\s*\|\s*([A-Za-z][A-Za-z0-9]*)\s*$/gm)].map((m) => m[1]))
}

/** The constructors `TheoryRule.paperAbsent` lists: Lean's additions. */
function leanOnlyRules(file) {
  const text = readFileSync(file, 'utf8')
  const start = text.indexOf('def paperAbsent : List TheoryRule :=')
  if (start < 0) throw new Error(`${file}: no \`def paperAbsent\``)
  const body = text.slice(start, text.indexOf(']', start))
  return new Set([...body.matchAll(/\.([A-Za-z][A-Za-z0-9]*)/g)].map((m) => m[1]))
}

const paper = paperRules(paperDir)
const lean = leanRules(leanFile)
const leanOnly = leanOnlyRules(leanFile)

let failed = 0
for (const [name, where] of paper) {
  if (lean.has(name)) continue
  if (name in KNOWN_ABSENT) {
    console.log(`absent (by argument): ${name} — ${KNOWN_ABSENT[name]}`)
    continue
  }
  console.error(`missing: ${name} (declared in ${where}) has no TheoryRule constructor`)
  failed = 1
}

// The other direction: every constructor is a paper rule or in `paperAbsent`.
for (const name of lean) {
  if (paper.has(name)) continue
  if (leanOnly.has(name)) {
    console.log(`Lean-only (to add to the paper): ${name}`)
    continue
  }
  console.error(`unlisted: TheoryRule.${name} is in no paper rule block and not in paperAbsent`)
  failed = 1
}
for (const name of leanOnly) {
  if (!lean.has(name)) {
    console.error(`stale: paperAbsent lists ${name}, which is not a constructor`)
    failed = 1
  } else if (paper.has(name)) {
    console.error(`stale: paperAbsent lists ${name}, which the paper now declares`)
    failed = 1
  }
}

if (failed) {
  console.error('theory-rules: the paper and the enumeration disagree.')
  process.exit(1)
}
console.log(
  `theory-rules: ${paper.size} paper rules, ${lean.size} constructors, ` +
    `${leanOnly.size} Lean-only, none unaccounted for.`,
)
