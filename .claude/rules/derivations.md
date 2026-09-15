---
paths:
  - "Solidity/Examples/**/*.lean"
  - "Solidity/Update/**/*.lean"
  - "Solidity/Update.lean"
  - "Solidity/MultiStep.lean"
---

# Derivations and the `sol!` notation

Derivations are written in the surface notation — `solbox!{ … }`,
`soldiamond!{ … }`, `solboth!{ … }`, `sol!{ < … > (post) }`, `seq!{ … }` — and
that is the point of them: a chain is meant to read as the symbolic execution
a reader could follow by hand.

**Do not "fix" a derivation by spelling its residual out as raw constructors**
(`⟨.box, [ sstmt!{ … }, Stmt.assign … ]⟩`). That is not a smaller edit, it is
the deletion of the artefact.

When a step stops elaborating, the cause is almost never the notation:

1. **The residual really is different** — more steps, not different syntax. A
   frozen value operand adds `uint rv = e;`, which costs three steps
   (`localValueDeclInitDrop` → `valueDeclSkip` → `localValueAssign`). Write
   them, or collapse them into one `⇝*` line.
2. **A scratch name has no explicit `rootExpr`/`rootPlace` arm.** The default
   arm gives the right term but leaves `decide` goals unreduced, so the
   failure looks like a parse problem and is not. Add the name to the
   explicit-arms list in `AST.lean` beside `"rv"`, `"idx"`, `"result"`.
   **But not for the worked-example identifiers**: giving those explicit arms
   overflowed Lean's stack (see the `Paper.lean` docstring). Explicit
   arms are for scratch names that appear in *residuals*.
3. **The grammar genuinely lacks a form.** Check `syntax … : sol_stmt` in
   `AST.lean` first — it covers bare declarations, plain and compound
   assignment, `push`/`pop`/`delete`, `predec`/`postdec`, and the `.. name`
   splice. If something really is missing, *extend the grammar*; an escape
   hatch used once becomes the house style.

## The arrows

| Lean | Means | Proof |
|---|---|---|
| `b ⇝ b'` | one rewrite step | `block_step` |
| `b ⇝[.rule] b'` | one step, by that named rule | `rule_step` |
| `b ⇝* b'` | zero or more steps | `steps [.r₁, …]`, or `steps!` |
| `j ⇝ᵈ[.rule] j'`, `j ⇝ᵈ* j'` | the same, on a judgment | `dl_rule_step` / `dl_steps […]` |
| `f ⇝ᵘ[.rule] f'`, `f ⇝ᵘ* f'` | the same, on a frontier of updated sequents | `seq_rule_step` / `seq_steps […]` / `seq_steps!` |
| `f ⇝≡ f'` | the **merge line**: not a rule, the update respelled | `upd_merge` |

ASCII twins: `~>`, `~>[.r]`, `~>*[…]`, `~>*`, `~>=`, and `~*>` for `⇝*` —
the spelling the paper's chains are written in.

**At the sequent layer `⇝`/`~>` and `⇝*`/`~*>` may absorb a trailing merge.**
`seq_steps!` stops as soon as the frontier reaches the stated target *or*
agrees with it on every antecedent and goal, at which point the only thing
left between them is the spelling of the update and `upd_merge` closes it.
That is what lets a chain land on the calculus's parallel form mid-derivation,
with the program still open. `⇝≡` is still how a line that takes **no** step
is written.

**The rule goes on the arrow, not in the proof.** `⇝[.storageFieldWriteSave]`
is a claim Lean checks; do not re-list the rules in a docstring above the
derivation.

**Elide administrative runs with `⇝*`.** `steps [.r₁, …]` when the rules are
part of what the derivation shows (the right choice in `Examples/Derivations/`);
`steps!` when they are bookkeeping. `steps!` asks `UniquenessAux.candidate` for
the rule at each step and then discharges it by the same pinned route, so the
emitted proof is identical and no new axioms appear. `candidate` is an oracle,
not an authority: `find_pinned_step` still proves the rule applies, so the one
case where it overreaches fails loudly. `steps_search!` is the old blind loop,
kept only as the oracle-free fallback. To see what `steps!` picked:
`set_option trace.solidity.steps true in …`, or write `steps?` for a pasteable
suggestion.

**Name the inactive suffix instead of retyping it.** A trailing `.. name`
splice means `[…] ++ name`. Write the suffix out again once it becomes active.

## Commands

`sol_derivation` is the chain and nothing else — no `calc`, no per-line
`:= by …`, and a `where` clause for the abbreviations. It states
`theorem <name> : <first> ⇝* <last>`, so each derivation is a reusable fact.
It serves all three layers, picked from the first line's notation: a `=>` line
or `seq!` is the sequent layer, `sol!` the judgment layer, anything else the
block layer. Single steps stay as `example : A ⇝[.r] B := by rule_step`.

**A sequent line is written with the turnstile in front**, the way
`Examples/Derivations/Paper.lean` writes the calculus's own chains:

```
sol_derivation deepFieldWrite :
    => <[ alice.account.balance = 10 ]>(φ)
  ~> => <[ uint rv = 10; … ]>(φ)
  ~*> => { rv@uint := 10 ‖ sp@Account := path(alice.account) } <[ … ]>(φ)
  ~> => { … ‖ storage := save(alice.account.balance, 10) } (φ)
```

Three things about that shape. A **bare `(φ)` goal** is the paper's last line,
where no program is left and the modality is no longer drawn: it is the one
the chain's *first* line wrote, so a chain agrees with itself by construction.
A **bare, atomic identifier in parentheses is a Lean term**; `(alice.age)` and
`(result == 10)` are programs, as everywhere else. A parenthesised *goal* is
always a postcondition over the empty program, so obligations — `⊤`, `⊥`,
`funded(se)`, `CInv` — are written without parentheses. And a **branching line
is a bracketed list** of such lines, which is what a guarded rule leaves open:
`[ inBounds(values[i]) => { v := values[i] } [ ](φ), ¬inBounds(values[i]) => ⊤ ]`.

`sol_runs name { stmt; stmt }` when the point is only *that* a program runs to
the empty block. **Statements are `;`-separated, deliberately**: newline
separation parses, but postfix `++` and the call form `ident(…)` reach across
a line break, and the misparse is *silent* — the merged program still reduces
to the empty block, so the theorem would be true and about a different program.

## Two scratch-name notes

- The capture rules' `pv` is a *stack* variable: spell it `pv@uint` / `pv@bool`
  (likewise `rv@uint`, `idx@uint`). A bare `pv` is a storage alias, and
  `SoliditySyntax.aliasKind` is a name-only table that cannot see the type. A
  *reference*-typed `pv@Account` is still a memory path alias.
- **`--` cannot be a Lean token** (it starts a comment), so a decrement is
  `predec(e)` / `postdec(e)`. That is surface notation, not an escape hatch.

`Examples/Common.lean`'s `rvExpr`/`idxExpr`/`spExpr` family exists for
residuals whose type is not fixed, not as a general substitute for the
notation.
