# Working in this repository

A Lean 4 model of solkey, the KeY-based Solidity prover:
<https://github.com/SolidiKeY/solkey>. `lake exe solkeycheck` expects a
checkout beside this repository (`../solkey`); it takes an explicit path
(`--key`/`SOLKEY_RULES`) when it lives elsewhere.

The design follows mini-solkey (`~/projects/side-projects/lean/mini-solkey`),
a small readable copy of the calculus: typed syntax, one inductive taclet
judgement written in the calculus's notation, and a sound proof system.
`docs/kernel-port.md` says which chapter landed where and what is still to
port.

**Updates are terms** (`Update.lean`): `STerm` at `structRules.key`'s
signature, `MTerm` at `memoryRules.key`'s — `save`/`delAt` nest, and so do
`write`/`addM`/`copySt`.  An allocation is the two parallel elements KeY
writes, a push and a pop are nested writes over `size`, and
`docs/lean-key-rule-map.md` is the symbol table.  A path alias binds bare
(`{ sp := alice.account }`); a read marks the *value* side instead
(`find`/`select`/`read`).

**Calls are inlined** (`Syntax.lean`): a contract declares its functions
(`contract!{ function f(uint x) returns (uint r) { … } }`), a function may
call only the ones declared before it, and a call statement (`Stmt.call`)
carries its callee's body with every local renamed fresh — KeY's
`FunctionBodyStatement`; `functionBodyExpand` inlines it.  **Callbacks** are
a second reading of the modalities (`Semantics/Callback.lean`, `holdsC`, the
`CallbackTaclet`s and `ProvesC` of `Calculus/Callback.lean`), not a change
to `Stmt.run`.

**`sol{ … }` is Solidity, with two spellings of its own** (`Syntax.lean`):
a decrement is `x−−`/`−−x` (two U+2212; `--` opens a Lean comment), and
effects stay out of values — an `++` inside an expression or a conditional
of references is captured by the elaborator before its statement, in solc's
evaluation order.

A second consumer is **the `SolKey` reader**, a Lean reader for KeY `.key`
files in a separate repository. It imports only `Solidity.Calculus.Rules` and
`Solidity.Calculus.KeyTaclets` (and through them the syntax). That is its
whole dependency surface: renaming a `Taclet` constructor breaks its
correspondence proofs, which is the point of it. It still names the old
`RuleName` table and is to be migrated (`docs/kernel-port.md`, "Port later").

## The one hard constraint

**The package has no external dependencies.** `lakefile.toml` declares no
`[[require]]`: no Mathlib, no Loom. Keep it that way — every require added
here is a clone every consumer has to pay for. Anything a proof needs from
Mathlib is a sign the proof should be done differently, or the lemma stated
locally.

**Warn before a refactor that may slow checking.** When asked to change a
representation (shallow ↔ deep embedding, one taclet for another), say first
if it could make elaboration slower, and whether `git log` shows it undoes an
earlier change made for speed.

## Where things are

`docs/module-map.md` — one line per module. Read it instead of searching
when you need to know where something lives.

Layering: types and names in `AST.lean`, the typed syntax in `Syntax.lean`,
the interpreter in `Semantics.lean`, terms and formulas in `Update.lean`, the
taclets in `Calculus/Rules.lean`, everything proved about them after. Keep
imports acyclic and local. Add new modules to `Solidity.lean`:
`node scripts/check-orphans.mjs` fails on a module nothing imports.

Before editing one of these families, read its conventions file. Claude Code
loads them automatically when you open a matching file; other agents should
read them by path.

| Editing | Read first |
|---|---|
| the rule table: `Calculus/{Rules,RuleSyntax,Completeness,RuleShapes,PrintedRules,KeyTaclets}.lean`, `SortCheck/**` | `.claude/rules/rule-table.md` |
| `Examples/**`, `Theory/**`, `Update.lean` (derivations and notation) | `.claude/rules/derivations.md` |
| `Calculus/{Sound*,RuleSoundness,Logic,Symex,Close}.lean`, `Counterexamples/**` | `.claude/rules/soundness.md` |
| `Typing/**`, `Semantics/**` | `.claude/rules/typing.md` |

`docs/README.md` indexes the documents. `docs/lean-key-rule-map.md` is the
authority for the name-by-name map to solkey's taclets (do not restate it in
module docstrings); `docs/solc-alignment.md` for where the interpreter follows
solc over KeY.

## Using the calculus

A formula is written in `dl!{ … }` over a named contract (`local instance :
InContract := ⟨StandardExample⟩`, `Calculus/Notation.lean`). Import
`Solidity.Calculus.Close` for the tactics, `Solidity.Calculus.Chains` for
chains, `Solidity.Tools.ProofTree` for the tree. `Examples/` shows each of
these once; `.claude/rules/derivations.md` is the convention.

**The taclets.** A taclet is one constructor of `Taclet C k m s p`
(`Calculus/Rules.lean`), named as solkey names it, typed `dl{ ⟨[ s; ]⟩ ⇝ p }`.
`#taclet storageFieldWriteSave` (or a KeY name as a string) prints it with the
solkey taclets it transcribes and its soundness theorem. Every statement has
exactly one rule (`Stmt.step`), so the strategy never chooses. To prove
`⊨ dl!{ pre → [ program ] post }`:

- **by the strategy**: `sol_symex; sol_close` (`sol_decide` for reads of
  writes; `sol_spec` for a `spec!{f}` obligation). `#wp φ` prints what
  `sol_symex` leaves, `#step φ` one step and the rule it fired.
- **by a walk**: `apply Proves.valid`, then one `apply` per rule — `intro`,
  `update r`, `unfold r`, `split r` (goals `thn`/`els`/`cov`), `Proves.check r`
  (an `assert`; goals `thn`/`els`; qualified, since `check` is also the
  elaborator's), `done r`, `empty` — and `refine close ?_; sol_symex; sol_close` at each leaf.
  `apply` refuses a rule whose `\find` or side conditions do not match.
  `sol_derive` runs the walk; `sol_derive?` prints it as a `Try this`.
- **by a chain**: `(chain .box φ).valid h`, with `h` proving its last line
  (`Fml.Via.valid`, `Fml.Steps.valid`, `Fml.Leads.valid`).

**Chains** (`Calculus/Chains.lean`) state a derivation with every line
written, as one chain term proved `by sol_chain`:
`A ~[r]~> B ~*> C ~[sequentialToParallel]~> D ~[findOnSave]~> E` — `~[r]~>`
a rule of the strategy (a wrong name is an elaboration error), `~>` one
step, `~*>` several, and past the program the rewrite links
`~[sequentialToParallel]~>`, `~[findOnSave]~>`, … (`Calculus/ChainRewrites.lean`).
`Fml.Via.leads` makes a chain `A ~~> E`, and `Fml.Leads.via` composes
segments of a long one. `#derivation φ` prints the strategy's lines, in the
rules' fresh names (`se1`, `sp1`); `#chain φ` (`Calculus/ChainGen.lean`)
writes the whole chain, the program and then one rewrite a link to a last
line, as the declaration to paste (`#chain_rest c` from the end of the chain
`c`; `sol_chain?` on a `φ ~~> ψ` goal). A line keeps a modality open with
`dl![m]{ ⟨[ p ]⟩ φ }` and a postcondition with `φ : Post C`; a box chain's
last line is `dl![.box]{ … }`.
When a line is not reached, `sol_chain`'s error shows the derivation it
computed.

**The proof tree API** (`Calculus/ProofTree.lean`, `Tools/ProofTree.lean`) is
solkey's view of `⊢ φ`, a tree of sequents grown by running the strategy as a
walk; every node is an elaborated `apply`, nothing is trusted.
`ProofTree.ofFormula C φ : TermElabM Tree`; `Tree.rows` are solkey's
`[serial, parent, name, branchLabel, state]`, `Tree.toJson` the web prover's
shape, `Tree.openGoals`/`Tree.closed` its state. Branch labels are the case
names `thn`/`els`/`cov`. The commands: `#proof_tree φ` (the GUI layout and a
summary), `#proof_node n φ` (sequent, rule, parent, children, tactics),
`#proof_tree_json φ`. `Examples/ProofTree.lean` pins their output: a change
to the strategy or a printer fails there.

## Writing or fixing a tactic

1. **Search once, replay cheaply.** A tactic that searches (`sol_chain`,
   `sol_derive`, `sol_rws`) gets a `?` twin that runs the search, then offers
   the explicit proof as a `Try this` (`sol_chain?`, `sol_derive?`, `sol_rws?`).
   The file keeps the replay, which must not search on every re-check.
   Nothing the tactic computes is trusted: the kernel checks every line.
2. **Bound every search.** Use a node budget, give each step its own
   heartbeats (`withCurrHeartbeats`), and catch timeouts per step
   (`tryCatchRuntimeEx`; a plain `try` does not catch them). A step that
   fails ends the search with a note, not with an error. Greedy choices can
   dead-end: search depth first in a fixed order and keep the best leaf
   (`ChainGen.searchRewrites`).
3. **Measure before optimising.** In a scratch module under
   `Solidity/Scratch/` (never committed), time one term or tactic with an
   `IO.monoNanosNow` wrapper, or set `trace.profiler` on one declaration. A
   cost in `compilation (LCNF …)` comes from `evalExpr`. The usual cause is an
   instance parameter that the compiler specializes at every call: mark its
   class `attribute [nospecialize]` (as `FreshNames` is). Put a cache in an
   `EnvExtension` with `asyncMode := .local` (`Chain.runCache`), so it ends
   with the declaration and cannot go stale.
4. **Pin the output.** Add a `#guard_msgs` example of the suggestion to
   `Examples/ProofTree.lean`, and a regression example for each shape a
   review found broken.
5. **Verify.** Check one file at a time (`lean_diagnostic_messages`). The
   machine has no RAM for parallel Lean checks. Then run one read-only review
   pass, a finder and a skeptic per area, that never calls the Lean server.
   Fix what it confirms.

If changing a module's imports leaves its language-server worker stuck
("still elaborating" forever), run the command from a fresh scratch module
that imports the module instead.

## Checking your work

Prefer the Lean MCP server (diagnostics, goals, hover, outline) over the
shell. Per-file diagnostics after an edit are the check; a full build is for
import changes and final confirmation. The `lean-verify` skill in
`.claude/skills/` is the loop written out.

| Command | What it covers |
|---|---|
| `./run-lean.sh` | `lake build` (default targets) then the solkey sort check |
| `node scripts/check-orphans.mjs` | every module is reachable from a library root |
| `./scripts/check-doc-paths.sh` | every backticked `*.lean` in the prose names a file that exists |
| `lake exe solkeycheck` | sort annotations against solkey's `.key` |
| `./scripts/check-corpus.sh` | the solkey corpus (`SolidityCorpus`) against `tests/solkey/expected.tsv` |

`solkeycheck` is at zero against solkey `100f7f24c3` (313 taclets,
2026-10-04). Re-pinning to a newer checkout is its own change: it regenerates
`Calculus/KeyTaclets.lean`, moves `SortCheck/Annotations.lean`, and
re-partitions `RuleShapes.taclets_partitioned`.

Run long builds in the background and grep the log for `error` rather than
reading it back whole.

## Lean notes

- Lake commands run from the project root, or use `./run-lean.sh`.
  (`scripts/lean-vscode/bin` wrappers exist only so the VS Code extension
  finds the Nix-provided `lean`/`lake` on NixOS; elan must come first on
  `PATH`, since it honours `lean-toolchain`.)
- **The language server needs `--tstack=131072`**, the number `lakefile.toml`
  already gives `lake build`: symbolic execution elaborates through deep
  recursion. The server does not read `weakLeanArgs`, so the flag is set twice
  more: `.vscode/settings.json`'s `lean4.serverArgs` for the editor, and
  `scripts/lean-mcp/bin/lake` for the MCP, whose client spawns a hardcoded
  `lake serve` with no hook for arguments.
- `lake env lean --tstack=131072 file.lean` checks one scratch file in
  seconds; the MCP server is slow on this package.
- `grind` is built in on this toolchain. Try `grind` or `grind [lemmas]`
  before a long manual script. For Boolean/bitvector goals prefer
  `bv_decide`/`omega`.
- **Finish a working proof with `simp only [...]`.** Once a proof passes,
  replace each bare `simp` with the lemma list `simp?` prints. Unrestricted
  `simp` re-searches the whole simp set on every re-check.
- **Do not raise `maxHeartbeats`.** When a proof needs more, make it cheaper
  (`simp only`, a helper lemma, a smaller `decide`). New overrides use the
  smallest value that passes. Existing ones go up to 8000000; lower them when
  you touch them. A runaway should fail in seconds, not use tens of GB of RAM.
- **Write the types of signatures and `have`s explicitly.** Errors then point
  at the line that is wrong. Do not annotate every subterm: that only adds
  places for a type mismatch.
- Use `rg`, which honours `.gitignore` and so skips `.lake/`.

## Reading before writing

Module docstrings carry the conventions and the rationale for their file.
They deliberately do not restate the declarations below them, so if you want
to know what a definition is, look at the definition.
