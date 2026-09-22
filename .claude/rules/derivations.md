---
paths:
  - "Solidity/Examples/**/*.lean"
  - "Solidity/Paper/*.lean"
  - "Solidity/Corpus/**/*.lean"
  - "Solidity/Tactics/*.lean"
  - "Solidity/Update/**/*.lean"
  - "Solidity/Update.lean"
  - "Solidity/Theory/*.lean"
  - "Solidity/Calculus/MultiStep.lean"
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
   frozen value operand adds `uint se = e;`, which costs three steps
   (`localValueDeclInitDrop` → `valueDeclSkip` → `localValueAssign`). Write
   them, or collapse them into one `⇝*` line.
2. **A scratch name has no explicit `rootExpr`/`rootPlace` arm.** The default
   arm gives the right term but leaves `decide` goals unreduced, so the
   failure looks like a parse problem and is not. Add the name to the
   explicit-arms list in `AST.lean` beside `"se"`, `"ie"`, `"result"`.
   **But not for the worked-example identifiers**: giving those explicit arms
   overflowed Lean's stack (see the `SolidityPaper.lean` docstring). Explicit
   arms are for scratch names that appear in *residuals*; a worked example's
   own identifiers go in `name_table_arms` in `Tactics/Derivation.lean`, which
   states the default arm's instance as a lemma instead of growing the match.
   That list is also **where a slow derivation is fixed**: a name missing from
   it still elaborates — `rule_cond` falls back to `rule_simp_tables`, which
   unfolds the tables — but every rule condition then re-reduces a match on a
   string literal, which is a second a step rather than a hundredth.
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
| `f ≡ f'` | the **merge line**: not a rule, the update respelled | `upd_merge` |
| `t = t'`, `t =[.rule] t'` | a **theory rewrite**, in a `sol_rewrite` | the rule's theorem |
| (no arrow) | run to closure, endpoint computed | `seq_closes` |

A chain written as a `sol_derivation` states its intermediate lines and Lean
checks them. **The other presentation states only the endpoints and puts the
rules in the proof** — `theorem first ⇝ᵘ* last := by seq_step .r₁; …;
seq_done`, one rule per line, with the frontier in between left to the goal
rather than the page. Reach for it when what you want is to *step through* a
derivation; keep `sol_derivation` when the intermediate lines are the artefact,
which in `Paper/` they always are. `Examples/Derivations/StorageSteps.lean` is
the worked example: every chain of `Paper/Storage.lean` in that presentation,
under the same names, and the headline one in both spellings side by side.

| Tactic | On a `⇝ᵘ*` goal |
|---|---|
| `seq_step .rule` | take one step; the successor the rule computes becomes the goal |
| `seq_done` | close: reflexivity, or the trailing merge |
| `seq_steps [.a, .b]` | the same run on one line; each rule name carries its own info node, so the cursor on `.b` shows that frontier, as inside `rw [a, b]` |
| `seq_steps?` | run it and report a pasteable `seq_steps [...]` — how a chain gets written |
| `seq_norm` | reduce both frontiers to literal constructor applications |

`seq_step` and `seq_rule_step` are different shapes and the table above says
which: the first *advances* a `⇝ᵘ*` goal with the successor unwritten, the
second *closes* a `⇝ᵘ[.rule]` line whose successor is written out.

**Goals print in the `seq!` notation** (`Update/SequentPP.lean`), so a frontier
between two steps reads as the line the calculus draws rather than as
constructor applications. It is a printer for the *data*, not an inverse of the
parser — an annotation the term does not carry cannot come back, so `se@uint`
prints as `se` — and whatever it cannot fully account for falls back to Lean's
own printing for that line. Whitespace is the auto-derived formatter's, not the
house style's. `set_option pp.solidity.seq false` turns it off.

ASCII twins: `~>`, `~>[.r]`, `~>*[…]`, `~>*`, `~*>` for `⇝*`, and `=`, `=[h]`,
`=*` for the `≡` family — the spellings the paper's chains are written in.
`⇝≡`/`~>=` are the older names of `≡`/`=` and still parse.

**`=` means two different things, and the layer says which.** In a
`sol_derivation` it is the merge — a `Frontier.Equiv`, an equality of *state
functions*. In a `sol_rewrite` it is a rule of the theories — an equality of
*terms*. They cannot be one chain: `{u}{v := alice.age}` and `{u ‖ v := 34}`
are not equal as state functions, because at a pre-state where the memory
variable is unbound the first errors and the second does not. The paper has
the same split, between its calculus and its signature.

`seq_closes` is the one loop that does not run toward a stated target: it
steps while `Frontier.firstOpen?` finds a line with a statement and then
assigns the target to whatever the rules produced. `seq_steps!` cannot be
pointed at a metavariable — its first move is `isDefEq` against the target,
which a metavariable satisfies at once, so the chain would close having taken
no step.

**At the sequent layer `⇝`/`~>` and `⇝*`/`~*>` may absorb a trailing merge.**
`seq_steps!` stops as soon as the frontier reaches the stated target *or*
agrees with it on every antecedent and goal, at which point the only thing
left between them is the spelling of the update and `upd_merge` closes it.
That is what lets a chain land on the calculus's parallel form mid-derivation,
with the program still open. `=`/`≡` is still how a line that takes **no** step
is written, and the paper draws that line — so write it where the paper does,
rather than letting the preceding `~>` swallow it.

**A memory merge is usually not writable, and that is a fact about the
readers.** `Wp.memBase` addresses a *simple* place only, so the one-line twin
of `{mv := ref(carol.account)}{memory := write(mv.balance, 100)}` does not
exist: `write(carol.account.balance, 100)` is stuck where the stacked pair
reads. Do not spend time on `upd_merge` when a merge line fails on a memory
chain — check first whether the merged spelling means anything.
`docs/paper-parity.md` records this under section 8.

**Updates are terms, and an allocation is two elements.**
`memoryRules.key`'s signature is what `Rules.MemTerm` spells and
`structRules.key`'s what `Rules.StTerm` does, so an update nests:
`{ storage := save(storage, alice.account.balance, 10) }`,
`{ storage := delAt(storage, alice.account) }`,
`{ memory := write(memory, mv@Account.balance, 100) }`,
`{ memory := write(alloc(Person), mv@Person.account, fresh) }`. A declaration
or a root delete writes the pair KeY writes —

```
{ mv@Person := freshId(alloc(Person)) ‖ memory := alloc(Person) }
```

— and the two agree on the root because they name the same term, not because
either re-derives it. `image(src)` is a reference source's value; `fresh` is
the root the enclosing `alloc` minted; `defVal(T)` is KeY's reset constant.
`docs/lean-key-rule-map.md` has the symbol-by-symbol table.

A **push** and a **pop** are nested writes over the array's extent, as the
paper draws them — `{ storage := save(save(storage, values[values.length],
42), values.length, values.length + 1) }`, and `delAt` in place of the slot
write for the bare `push()`.  `Rules.StTerm` says why the two positions are
constructors of their own rather than plain `save`s: a *program* cannot write
one past the end or assign `a.length`, so the soundness bridges compare a
rule's update with `SVal.save` while these two need `SVal.saveExt`.

There is **no `path(·)` wrapper**.  A bare right-hand side binds by its sort —
`{ sp := alice.account }` is an alias, `{ mv := carol }` an identity — and a
*read* is marked instead, the way the paper marks it: `{ v := find(storage,
alice.account.balance) }`, `{ v := select(storage, total) }`.  `defVal(T)` is
what a declaration without initialiser binds.

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
`Solidity/Paper/` writes the calculus's own chains
(`SolidityPaper.lean` is the target root, the conventions and the imports; `docs/paper-parity.md`
maps the chains to the paper's worked examples):

```
sol_derivation deepFieldWrite :
    => <[ alice.account.balance = 10 ]>(φ)
  ~> => <[ uint se = 10; … ]>(φ)
  ~*> => { se@uint := 10 ‖ sp@Account := alice.account } <[ … ]>(φ)
  ~> => { … ‖ storage := save(storage, alice.account.balance, 10) } (φ)
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

`sol_rewrite` is the same chain one layer down: the paper's lines *after* the
program is gone, where the accumulated update's terms are rewritten by the
theories. Lines are plain terms of `Theory/Terms.lean`, `Theory/Storage.lean`,
`Theory/Memory.lean` and `Theory/CrossDomain.lean`, arrows are the `=` family only, and the
statement is an `Eq`:

```
sol_rewrite memoryToStorageRootCopyValue (r : Nat) :
    StValue.find (.storeSt Struct.mtSt alice (.st (.copyMem M (.idC r [])))) [alice, age]
  =[.findPath]       StValue.find (.copyMem M (.idC r [])) [age]
  =[.findCopyMem]    MemValue.ofView M (Memory.readR M (.idC r []) [age])
  =[.readWriteEqual] StValue.prim (PrimVal.int 34)
```

The name on the arrow is a `TheoryRule` (`Theory/Rewrite.lean`) under **the
paper's** name, not KeY's — `findPath`, not `findDefinitionCons`. It is
resolved to the theorem(s) it is and *those* discharge the line, so a wrong
name does not elaborate. `#theory_rules` prints the table when you need to know
whether a rule exists before writing it. Binders go after the name, a `let`
prefix writes the paper's `Let S₁ = …`, and a chain goes in
`Paper/Theory.lean` with a row in `docs/paper-parity.md` § 8b.

`sol_calculus name from <store> { stmt; stmt }` when the point is that the
**rule table proves the obligation**: it states `CalculusHolds`, runs the
taclets with `seq_closes` until no line of the frontier has a statement left,
and decides the frontier reached. Use it for a whole solkey function, where
the accumulated update is not something to write out; use a `sol_derivation`
chain where the update *is* what the example shows.

Two things about writing a command that generates one of these. The endpoint
is `native_decide` and has to be: `Frontier.Holds` runs the accumulated update
through the interpreter's readers and the WF-recursive interpreter does not
kernel-reduce, so `decide` fails on it. And **an identifier inside the
generating macro's own quotation is not the Solidity variable of that name**:
it carries the macro's hygiene scopes, and `sol_expr`'s ident production reads
the mangled name as a variable. `sexpr!{ true }` written inside a macro
elaborates to a seven-deep chain of stack field accesses named after the macro
scope, and the obligation is then about that. Write the term
(`Typed.WrappedExpr.bool true`); spliced user syntax is fine, because it
carries the user's scopes.

`sol_runs name { stmt; stmt }` when the point is only *that* a program runs to
the empty block. **Statements are `;`-separated, deliberately**: newline
separation parses, but postfix `++` and the call form `ident(…)` reach across
a line break, and the misparse is *silent* — the merged program still reduces
to the empty block, so the theorem would be true and about a different program.

## Two scratch-name notes

- The scratch names are the paper's kind-names: `se` (value), `ie` (index),
  `sp`, `mv`. A primitive `se` is a *stack* variable: spell it `se@uint` /
  `se@bool` (likewise `ie@uint`), because `SoliditySyntax.aliasKind` is a
  name-only table that cannot see the type; a *reference*-typed `se@Account`
  is a memory path alias (the `_ se = e` capture at a reference source).
- **`--` cannot be a Lean token** (it starts a comment), so a decrement is
  `predec(e)` / `postdec(e)`. That is surface notation, not an escape hatch.

`Tactics/Derivation.lean`'s `rvExpr`/`idxExpr`/`spExpr` family exists for
residuals whose type is not fixed, not as a general substitute for the
notation.
