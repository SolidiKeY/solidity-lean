import Solidity.Examples.Derivations.Paper.Storage
import Solidity.Examples.Derivations.Paper.Memory
import Solidity.Examples.Derivations.Paper.CrossDomain
import Solidity.Examples.Derivations.Paper.Control
import Solidity.Examples.Derivations.Paper.Checks

/-!
# The calculus's worked examples

One chain per worked example of the calculus, written the way the calculus
writes them: the program shrinks on the right while the accumulated update
grows on the left, and the chain ends not at an empty program but at a formula
under one update.

```
    => <[ alice.account.balance = 10 ]>(φ)
~>  => <[ uint rv = 10; Account storage sp = alice.account; sp.balance = rv ]>(φ)
~*> => { rv := 10 ‖ sp := alice·account } <[ sp.balance = rv ]>(φ)
~>  => { rv := 10 ‖ sp := alice·account ‖ storage := save(alice·account·balance, 10) } (φ)
```

Each is one `sol_derivation` and each is a named theorem about `⇝ᵘ*`, so a
derivation is a reusable fact rather than a picture.  **No rule names appear
on the arrows**: `~>` and `~*>` ask `UniquenessAux.candidate` for the rule at
each step, so a rule rename or a changed residual is a build failure here, not
a stale list to re-derive.  To see what fired, put
`set_option trace.solidity.steps true in` above a chain.

This file is the conventions and the imports.  The chains are in five modules,
one per group of the calculus's sections:

| Module | Sections |
|---|---|
| `Paper/Storage.lean` | 1 storage fields and roots · 2 storage arrays · 3 delete · 4 compound assignment |
| `Paper/Memory.lean` | 5 memory · 6 memory delete · 7 memory arrays and allocation |
| `Paper/CrossDomain.lean` | 8 cross-domain copies |
| `Paper/Control.lean` | 9 payment · 10 require, assert and if/else |
| `Paper/Checks.lean` | the lines, run against the interpreter |

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

**The scratch names are Lean's.**  The calculus writes `pv` for a frozen value
operand and `acc` for a storage alias; the rules here bind `rv` and `sp`, and
`Rules.lean` records why the calculus's own examples are inconsistent about
it.  A stack scratch name carries its type — `rv@uint`, `pv@bool`,
`sp@UintArray` — because `SoliditySyntax.aliasKind` is a name-only table that
cannot see it.  The calculus's auxiliary arrays and its bucket are scratch
aliases here, because a fresh name would fall to `rootExpr`'s stack default:
`carolValues` is `mv@UintArray`, `carolTokens`/`davidTokens` are
`mv2@TokenArray`, `carolToken` is `mv3@Token`, and `bucket` is a state
variable `bucket@@TokenBucket`.  `docs/paper-parity.md` carries the whole
table.

**The freeze costs three steps the calculus does not draw.**  A value operand
is frozen before the target is captured (`Counterexamples/ErrorOrder.lean` is
why), which is `localValueDeclInitDrop` → `valueDeclSkip` → `localValueAssign`.
They are inside a `~*>`, as the calculus elides them.

**The merge is part of an arrow, not a line of its own.**  The calculus's last
line is usually not a rule application but the update calculus collapsing
`{u}{v}` into `{u ‖ {u}v}`.  `~>`/`~*>` absorb it: a step lands on the target
as soon as the two agree on every antecedent and goal, and what is left is
`Upd.Par.seq_single` and the reader lemmas of `Update/Merge.lean`.  Where those
lemmas do not reach — an earlier `storage`/`memory` write, a `push`, an
`alloc` — the line stays in the stacked `{U₁}{U₂}` form the derivation
accumulated, which is equally what the calculus writes before it merges.

**The chains that have a semantic twin have it in `Paper/Checks.lean`**, not
all of them: `Sequent.check` runs a line against the interpreter, and the
checks take the first and the last line of one chain per section and run both
on a concrete store.  The chains themselves add no axiom: a pinned step goes
through `UniquenessAux.firstStepCase_box`, whose exclusivity theorem is decided
by `native_decide` in `Uniqueness.lean`, which is the block layer's proof
route.  The checks are the only `native_decide` written here, and
`docs/paper-parity.md` says which sections have one.

## What has no chain here

Some programs the calculus draws cannot be written as a chain, and the reason
is informative in each case: call-valued operands, a declaration of one of the
worked-example roots, the first-order side condition `sizeNotNegative`, the
sequent rule `ifElseSplit`, the memory identity layer, the unfunded transfer,
and checked arithmetic.  Each is argued in **`docs/paper-parity.md`**, beside
the row of the example it belongs to; they are not restated here, because an
argument in two places drifts in one of them.
-/
