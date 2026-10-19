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

**The model is intrinsic** (`docs/intrinsic.md`). A statement is
`Stmt C Γ Γ'` (`Syntax/Scoped.lean`): its locals are positions `Idx Γ t` in a
context (`Scope.lean`), so a local read out of scope or at another type cannot
be written. The run (`Stmt.run`, `Semantics/Run.lean`) is over a state typed by
the context (`State C Γ`: typed storage, heap and locals) and halts only by
revert, panic, divergence or exhaustion: it is never stuck. The elaborator
emits it directly (`Syntax/Elab.lean`) and the printers print it
(`Calculus/PrintStmt.lean`): no untyped statement, program or formula as
written remains (decision 11, resolved at W8). Formulas are `Fml C Γ`
(`Calculus/Fml.lean`). The closer reads scoped formulas (M6c): `sol_decide`
reduces a scoped leaf by position and closes it there
(`Calculus/DecideScoped.lean`, `Calculus/DecideTyped.lean`), `sol_close`
reads a leaf's parameters at their types, `sol_prove`'s leaves on `⊢` and
on `⊨` are scoped sequents (`rw` in them, `Calculus/SeqRewrite.lean`),
`sol_upd`/`sol_merge` rewrite the scoped leaf, and a chain rewrites while
the program is open (`Calculus/RewriteScoped.lean`) and past it
(`Calculus/RewritePast.lean`, `Calculus/RewriteLaws.lean`). No leaf is
erased: the untyped formulas (`NFml`) are gone (W9.5a), and so are the
erased program evaluators (W9.6.4), and so are the untyped terms by name
(`Surface.Tm`, W9.7.1), and so is the erased state (W9.7.3); the terms'
symbols read the typed state (W9.8.3). KeY's unbounded `int` is its own
sort (`Srt.kint`): the ledger, `toInt`, a spec's arithmetic over them. The
rest is typed too (W10): `sol_decide`'s language is the typed signature
with atoms and guards (`Calculus/DecideLang.lean`), the Theory's values
are their observations (`Theory/Typed/Obs.lean`, `Theory/Typed/Mem.lean`;
`Tm.denote`, `.eq` is `=`), and `Tools/Counterexample.lean`'s candidates
are typed states.  So is every other state read: the run invariants
(`Typing/`), the EVM simulation (`Evm/`), the memory laws, the tools and
`wt(storage)` (`Semantics/StorageWt.lean`) read the typed state; there is
no untyped one (W10.5.6). External-call inputs retain their Solidity types (`CallValue`, `ExtKey`),
path segments retain their endpoints (`Seg`, `Segs`, `RefSegments`), the
ledger has bounded address keys and unbounded KeY `int` amounts (`Ledger`),
and the EVM's store holds `Fin (2^256)` words (`Evm.WordStore`), its stack words or symbolic slots (`Evm.Word`). External
responses are ABI words (`ExtResult`, `Word`), decoded at the locals' types
(`PrimTy.ofWord?`), and tool input/output are typed values (`CallValue`):
there is no untyped value (W11). Selector labels, the paths' comparison
observations, carry `uint` indices and typed keys (W11.9).


**Updates are terms** (`Signature.lean`: KeY's sorts indexed by Solidity
types; `Calculus/Fml.lean`'s terms): a storage at `structRules.key`'s
sorts, a memory at `memoryRules.key`'s — `save`/`delAt` nest, and so do
`write`/`addM`/`copySt`.  An allocation is the two parallel elements KeY
writes, a push and a pop are one symbol each (printed as KeY's
nested writes over `size`), and
`docs/lean-key-rule-map.md` is the symbol table.  A path alias binds bare
(`{ sp := alice.account }`); a read marks the *value* side instead
(`find`/`select`/`read`).

**Calls are inlined** (`Syntax.lean`, `Syntax/Elab.lean`, `Syntax/Scoped.lean`): a contract declares its functions
(`contract!{ function f(uint x) returns (uint r) { … } }`), a function may
call only the ones declared before it, and a call statement (`Stmt.call`)
carries its callee's body, closed over a frame of its own — KeY's
`InternalCall`, which `internalCallExpand` inlines (`functionBodyExpand` for
a call with targets, `CallRet.rets`: a tuple assignment's, a spec
obligation's).  **Callbacks** are
a second reading of the modalities (`Semantics/Callback.lean`, `holdsC` of
`Calculus/CallbackHolds.lean`, the `CallbackTaclet`s and `ProvesC` of
`Calculus/Callback.lean`), not a change to `Stmt.run`; which statements call
back, and the other options of the calculus, are `docs/options.md`'s.

**`sol{ … }` is Solidity, with two spellings of its own** (`Syntax.lean`):
a decrement is `x−−`/`−−x` (two U+2212; `--` opens a Lean comment), and
effects stay out of values — an `++` inside an expression or a conditional
of references is captured by the elaborator before its statement, in solc's
evaluation order.

**The `SolKey` reader** (side-projects, `lean/solkey`), a Lean reader for
KeY `.key` files that once consumed this package, is outdated since W9.7: it
read the erased terms (`Surface.Tm`, `Delab.tr`, `NFml`), now deleted, and
no longer builds against this checkout. It is not maintained from here; do
not edit it or keep anything for it.

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

Layering: types and names in `AST.lean`, contexts in `Scope.lean`, the grammar
and raw syntax in `Syntax.lean`, elaborated (`Syntax/Elab.lean`) to the scoped
syntax of `Syntax/Scoped.lean`, the typed state in `Semantics/State.lean`
(storage `Semantics/Storage.lean`, heap `Semantics/Heap.lean`) and the run in
`Semantics/Run.lean`, the terms' signature in `Signature.lean`, scoped
formulas and their updates in `Calculus/Fml.lean`,
the taclets in `Calculus/Rules.lean`, everything proved about them after. Keep
imports acyclic and local. Add new modules to `Solidity.lean`:
`node scripts/check-orphans.mjs` fails on a module nothing imports.

Before editing one of these families, read its conventions file. Claude Code
loads them automatically when you open a matching file; other agents should
read them by path.

| Editing | Read first |
|---|---|
| the rule table: `Calculus/{Rules,RuleSyntax,Arms,Blocks,Step,Taclet,Completeness,RuleShapes,PrintedRules,KeyTaclets}.lean`, `SortCheck/**` | `.claude/rules/rule-table.md` |
| `Examples/**`, `Theory/**`, `Update.lean` (derivations and notation) | `.claude/rules/derivations.md` |
| `Calculus/{Sound*,ProvesSound,Logic,Symex}.lean`, `Counterexamples/**` | `.claude/rules/soundness.md` |
| `Typing/**`, `Semantics/**` | `.claude/rules/typing.md` |

`docs/README.md` indexes the documents. `docs/lean-key-rule-map.md` is the
authority for the name-by-name map to solkey's taclets (do not restate it in
module docstrings); `docs/solc-alignment.md` for where the interpreter follows
solc over KeY.

## Using the calculus

A formula is written in `dl!{ … }` over a named contract (`local instance :
InContract := ⟨StandardExample⟩`), which reads it as a scoped `Fml C []`;
under `open scoped Solidity.Scoped` (`Calculus/Surface.lean`) its
parameters are bound by `∀`, outside by hidden binders. Import
`Solidity.Calculus.Surface`, `Solidity.Calculus.Closers` and
`Solidity.Calculus.Close` for the tactics (and
`Solidity.Calculus.SolSpec` for `sol_spec`),
`Solidity.Calculus.LastLine` for chains, `Solidity.Tools.Inspect` for `#wp`,
`#step` and the tree. `Examples/` shows each of
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
- **by a walk**: `apply Proves.valid`, then one `apply` per rule — `intro`
  (solkey's `impRight`), `update r`, `unfold r`, `split r` (KeY's two
  goals `thn`/`els`; `splitBox r` is the same rule), `Proves.check r` (an `assert`; goals `thn`/`els`; qualified,
  since `check` is also the elaborator's), `done r`, `empty`
  (`emptyModality`), `allIntro` (`allRight`) — and
  `sol_leaf; sol_close` at each leaf (`sol_leaf`: the sequent as `⊨ ψ`,
  scoped; `sol_decide` or `sol_spec_close` in place of `sol_close`).
  `sol_derive?` writes
  the solkey names (`impRight`, `emptyModality`, `allRight`).
  `apply` refuses a rule whose `\find` or side conditions do not match.
  `sol_derive` runs the walk; `sol_derive?` prints it as a `Try this`.
- **by a chain**: `chain.valid h`, with `h` proving its last line
  (`Fml.Via.valid`, `Fml.Steps.valid`, `Fml.Leads.valid`); the lines
  past the program are scoped too (`Calculus/RewritePast.lean`).

**Chains** (`Calculus/Chains.lean`) state a derivation with every line
written, as one chain term proved `by sol_chain`:
`A ~[r]~> B ~*> C ~[sequentialToParallel]~> D ~[findOnSave]~> E` — `~[r]~>`
a rule of the strategy (a wrong name is an elaboration error), `~>` one
step, `~*>` several, and the rewrite links
`~[sequentialToParallel]~>`, `~[findOnSave]~>`, … (`Calculus/RewriteScoped.lean`
while the program is open, `Calculus/RewritePast.lean` past it).
`Fml.Via.leads` makes a chain `A ~~> E` (`Fml.Via.leadsK`/`Fml.LeadsK`
when it ends on a written last line, the same up to its binders' names;
`Fml.LeadsK.valid h hL` proves `A` from it and `Valid L`), and `Fml.Leads.via` composes
segments of a long one. `#derivation φ` prints the strategy's lines, in the
rules' fresh names (`se1`, `sp1`); `#chain φ` (`Calculus/ChainGen.lean`)
writes the whole chain, the program and then one rewrite a link to a last
line, as the declaration to paste (`#chain_rest c` from the end of the chain
`c`; `sol_chain?` on a `φ ~~> ψ` goal). A line keeps a modality open with
`dl![m]{ ⟨[ p ]⟩ φ }` and a postcondition with `φ : Post C Γ`; a box chain's
last line is `dl![.box]{ … }`.
When a line is not reached, `sol_chain`'s error shows the derivation it
computed.

**The proof tree API** (`Calculus/ProofTree.lean`, `Tools/ProofTree.lean`) is
solkey's view of `⊢ φ`, a tree of sequents grown by running the strategy as a
walk; every node is an elaborated `apply`, nothing is trusted.
`ProofTree.ofFormula C φ : TermElabM Tree`; `Tree.rows` are solkey's
`[serial, parent, name, branchLabel, state]`, `Tree.toJson` the web prover's
shape, `Tree.openGoals`/`Tree.closed` its state. Branch labels are solkey's
(`Taclet.branchLabels`, as the rules write them: `"Holds"`, `"if s#se true"`
with `se` filled in); `thn`/`els` are only the walk's case names. The
commands: `#proof_tree φ` (the GUI layout and a
summary), `#proof_node n φ` (sequent, rule, parent, children, tactics),
`#proof_tree_json φ`. `Examples/ProofTree.lean` pins their output: a change
to the strategy or a printer fails there.

## Repairing a broken rule

Follow [docs/rule-repair.md](docs/rule-repair.md): establish the execution
meaning, prototype a lazy rule, reject bad candidates with concrete cases
and bounded proofs, then prove local soundness and integrate it. Check
coverage, overlap and termination separately. Keep detailed guidance there.

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
   (`Chain.pastSearchFrom`).
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
5. **Verify.** Check one file at a time (`lean_diagnostic_messages`), within
   the memory limits of "Copies and branches". Then run the review pass of
   "Checking your work".

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
| `./run-lean.sh` | `lake build` (default targets), `lake build SolkeyTestSuite` (the solc import, 437 statements, the derived theorems `TestSuite/Report.lean` counts: the slowest part), then the solkey sort check |
| `node scripts/check-orphans.mjs` | every module is reachable from a library root |
| `./scripts/check-doc-paths.sh` | every backticked `*.lean` in the prose names a file that exists |
| `lake exe solkeycheck` | sort annotations against solkey's `.key` |
| `./scripts/check-corpus.sh` | the solkey corpus (`SolidityCorpus`) against `tests/solkey/expected.tsv` |
| `./scripts/check-testsuite.sh` | the TestSuite rows against `Report.lean`'s pin and solkey's functions; no Lean |

`solkeycheck` is at zero against frozen solkey `473da8944c` in
`tests/migration/solkey` (377 taclets, 131 read-bearing annotations,
2026-10-17). See `docs/solkey-migration.md` for remaining migration gaps.
Re-pinning to a newer checkout is its own change: it regenerates
`Calculus/KeyTaclets.lean`, moves `SortCheck/Annotations.lean`, and
re-partitions `RuleShapes.taclets_partitioned`.

Run long builds in the background and grep the log for `error` rather than
reading it back whole.

**End every milestone with one read-only review pass**: a finder and a
skeptic per area, neither of which calls the Lean server, then fix what the
skeptic confirms and record it in the milestone's doc section.

## Copies and branches

Lake's artifact cache is on (`lakefile.toml`): every module is stored once,
under the hash of its inputs, in `~/.elan/toolchains/<toolchain>/lake/cache`,
and every checkout reads from it. A branch, a `git worktree` or a copy
therefore rebuilds only the modules its own edits change, and master
rebuilds nothing after merging a lane that was built elsewhere.

- **A parallel lane is a `git worktree`** on its own branch
  (`git worktree add ../solidity-lean-<lane> -b <lane>`), not a `cp -r`:
  the cache fills its `.lake` in seconds (a file importing `Calculus/Close`
  opened in 8 s with no build directory), and its commits are visible to
  master without a fetch.
- **RAM is per open file, not per build.** A Lean worker holds 0.6–1.5 GB,
  3–4 GB on `Calculus/Decide.lean` or a `TestSuite/Derived*` module, and the
  MCP keeps up to 8 open per checkout, so one agent can hold about 16 GB.
  A session runs under a 32 GiB memory cap (`crc` starts it with
  `systemd-run -p MemoryMax=32G`), and past it the kernel kills single Lean
  processes, so a check fails for no reason in the code. Run at most two Lean
  agents at once (one while a large rebuild is due: Lake compiles stale
  imports in parallel), and keep each to three or four open files.
- **End a lane by freeing it:** after the merge, stop its workers
  (`pkill -f 'lean --worker.*solidity-lean-<lane>/'`) and remove the
  worktree. Idle workers of finished lanes stay resident otherwise.
- **Edit low modules first.** A change to `Syntax`, `Semantics`, `Rules` or
  `Decide` invalidates everything above it in that checkout; finish those
  edits before checking the files that import them.
- The cache only grows. `rm -rf ~/.elan/toolchains/*/lake/cache` empties it;
  the next build refills it.

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

## Following solkey

Semantics are Lean's (`docs/solc-alignment.md`); everything a reader sees
follows solkey.

- **Every rule of `⊢` reads like its solkey taclet**: the program taclets,
  the `Proves` rules, the term and update rules, and each clause of the
  closer (storage and memory). Same name, same `\find`/`\replacewith`
  shape, KeY's schema-variable names, side conditions and branch labels.
  Spelling is solkey's: `save`/`find` at a root (`store`/`select` still
  parse), solkey's memory taclet names.
- **A new closer feature starts from solkey's taclets**, not from a decision
  procedure of its own: find the taclets in the `.key` files, make each one
  a clause, take the interpreter lemma as its soundness and cite the
  `Theory/` lemma that transcribes it, and give it a row in
  `docs/lean-key-rule-map.md`. Mark Lean-only clauses and deviations as such.
- **Notation, not constructor trees.** A taclet is `dl{ … }`, a sequent
  `dl{ ..Γ, c ⟹[R] ⟨[ s; ..ω ]⟩ φ }`, a term `tm{ … }`, used in
  definitions' patterns and arms, with a printer that shows the same in
  `#wp`, errors and pins. A new term language gets its notation and printer
  with it. Notation is macros only: the kernel and compiled code see the
  same terms, which a restated type proves by `rfl` before anything
  downstream is checked.

## Reading before writing

When asked to change documentation, keep `AGENTS.md` succinct: put detailed
guidance in the relevant `docs/` document, and add only essential instructions
and pointers here. Update the docs index and affected conventions as needed.

Module docstrings carry the conventions and the rationale for their file.
They deliberately do not restate the declarations below them, so if you want
to know what a definition is, look at the definition.
