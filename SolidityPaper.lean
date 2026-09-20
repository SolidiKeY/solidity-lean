-- Root of the `SolidityPaper` library: one `sol_derivation` chain per worked
-- example of the calculus, written the way the calculus writes it.
--
-- Deliberately not imported by `Solidity.lean`, for the same reason
-- `SolidityCorpus` is not: it is ~45 derivations over ~240 rule applications,
-- each one a pinned `find_pinned_step` paying its own `simp`+`decide`, which
-- costs about 30 minutes of CPU (1m25s wall on 32 cores). The whole default
-- build is about 24, so folding this in would roughly double it. Build this
-- target with `./scripts/check-paper.sh`.
--
-- The derivations here are a *rendering* of the rule set, not new results:
-- the same rules are already exercised by `Solidity/Examples/Derivations/`
-- and `Solidity/Examples/Taclets/`, which are in the default build. What this
-- target adds is the calculus's own chains, program and accumulated update
-- together, one per worked example of the paper.
import Solidity.Paper.Storage
import Solidity.Paper.Memory
import Solidity.Paper.CrossDomain
import Solidity.Paper.Control
import Solidity.Paper.Checks
import Solidity.Paper.Theory

/-!
# The calculus's worked examples

One chain per worked example of the calculus, written the way the calculus
writes them: the program shrinks on the right while the accumulated update
grows on the left, and the chain ends not at an empty program but at a formula
under one update.

```
    => <[ alice.account.balance = 10 ]>(φ)
~>  => <[ uint se = 10; Account storage sp = alice.account; sp.balance = se ]>(φ)
~*> => { se := 10 ‖ sp := alice·account } <[ sp.balance = se ]>(φ)
~>  => { se := 10 ‖ sp := alice·account ‖ storage := save(alice·account·balance, 10) } (φ)
```

Each is one `sol_derivation` and each is a named theorem about `⇝ᵘ*`, so a
derivation is a reusable fact rather than a picture.  **No rule names appear
on the arrows**: `~>` and `~*>` ask `UniquenessAux.candidate` for the rule at
each step, so a rule rename or a changed residual is a build failure here, not
a stale list to re-derive.  To see what fired, put
`set_option trace.solidity.steps true in` above a chain.

This file is the target root, the conventions and the imports.  The chains
are in five modules, one per group of the calculus's sections:

| Module | Sections |
|---|---|
| `Solidity/Paper/Storage.lean` | 1 storage fields and roots · 2 storage arrays · 3 delete · 4 compound assignment |
| `Solidity/Paper/Memory.lean` | 5 memory · 6 memory delete · 7 memory arrays and allocation |
| `Solidity/Paper/CrossDomain.lean` | 8 cross-domain copies |
| `Solidity/Paper/Control.lean` | 9 payment · 10 require, assert and if/else |
| `Solidity/Paper/Checks.lean` | the lines, run against the interpreter |

**`docs/paper-parity.md` is the map**: one row per worked example of the
paper, naming either the theorem that is it or the reason there is no chain.
That is where a missing example is accounted for, and
`scripts/check-paper-parity.sh` fails if a row names a theorem this package
does not have.

## How to read a line

`=>` is the turnstile the calculus draws only when a line branches; writing it
on every line is what makes a chain uniform.  What precedes it is the
antecedent, each formula under the update stack it is read in; what follows is
the accumulated update and then the goal.  The last line drops the modality,
as the calculus does, and `(φ)` is the opaque postcondition
(`Update/SequentSyntax.lean` for the grammar, `.claude/rules/derivations.md`
for the conventions).

A **branching line is a bracketed list**: a guarded rule leaves one sequent
open per goal whose mode applies, which is how the calculus draws an array
access.  In the combined modality `⟨[ … ]⟩` both modes apply, so an
out-of-bounds branch appears twice — closed with `⊤` for the box reading and
`⊥` for the diamond one.  A chain written in one modality shows one of them.

## Where this differs from the calculus, and why

**The scratch names are the paper's rule names.**  A residual binds `se`,
`ie`, `sp`, `mv` — the kind-names of the paper's schema-variable tables —
where the paper's worked examples instantiate them with concrete names
(`pv`, `idx`, `acc`), and `Calculus/Rules.lean` records why the names are
fixed rather than fresh.  A stack scratch name carries its type — `se@uint`,
`se@bool`, `sp@UintArray` — because `SoliditySyntax.aliasKind` is a name-only
table that cannot see it.  The calculus's auxiliary arrays and its bucket are scratch
aliases here, because a fresh name would fall to `rootExpr`'s stack default:
`carolValues` is `mv@UintArray`, `carolTokens`/`davidTokens` are
`mv2@TokenArray`, `carolToken` is `mv3@Token`, and `bucket` is a state
variable `bucket@@TokenBucket`.  `docs/paper-parity.md` carries the whole
table.

**The freeze is the calculus's own step; the declaration it leaves costs
three the calculus does not draw.**  A complex value source is hoisted into
`se` by the same step that aliases the receiver — `nsp.fld = e ⇝ T se ?= e;
T storage sp = nsp; sp.fld = se`, the calculus's partition, with the value
frozen before the target is captured (`Counterexamples/ErrorOrder.lean` is
why) and a source that already *is* `se` left alone — so a chain's first
`~>` lands on exactly the line the calculus draws.  What the calculus then
elides inside its `~*>` is the stack declaration running down:
`localValueDeclInitDrop` → `valueDeclSkip` → `localValueAssign`, which is
where the `{ se := default(uint) } { se := 10 }` pair of an unmerged line
comes from.  They are inside a `~*>` here too.

**The merge is part of an arrow, not a line of its own.**  The calculus's last
line is usually not a rule application but the update calculus collapsing
`{u}{v}` into `{u ‖ {u}v}`.  `~>`/`~*>` absorb it: a step lands on the target
as soon as the two agree on every antecedent and goal, and what is left is
`Upd.Par.seq_single` and the reader lemmas of `Update/Merge.lean`.  Where those
lemmas do not reach — an earlier `storage`/`memory` write, a `push`, an
`alloc` — the line stays in the stacked `{U₁}{U₂}` form the derivation
accumulated, which is equally what the calculus writes before it merges.

**The chains that have a semantic twin have it in `Solidity/Paper/Checks.lean`**, not
all of them: `Sequent.check` runs a line against the interpreter, and the
checks take the first and the last line of one chain per section and run both
on a concrete store.  The chains themselves add no axiom: a pinned step goes
through `UniquenessAux.firstStepCase_both` -- these chains are written in the
block modality, and what stands in for the mode check there is the box and
diamond oracles agreeing -- whose exclusivity theorem is decided by
`native_decide` in `Calculus/Uniqueness.lean`, which is the block layer's proof
route.  The checks are the only `native_decide` written here, and
`docs/paper-parity.md` says which sections have one.

## What has no chain here

Some programs the calculus draws cannot be written as a chain, and the reason
is informative in each case: call-valued operands, a declaration of one of the
worked-example roots, the first-order side condition `sizeNotNegative`, the
sequent rule `ifElseSplit`, the memory identity layer, and checked
arithmetic.  Each is argued in **`docs/paper-parity.md`**, beside
the row of the example it belongs to; they are not restated here, because an
argument in two places drifts in one of them.
-/
