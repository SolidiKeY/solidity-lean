# Using the calculus

Public `⊨` reads `Spec` only; internal formula validity is `Fml.Valid`
(`⊨ᶠ`). `Proves.valid` and `ProvesC.valid` bridge proofs of `Spec.toFml`
to direct correctness. See [correctness.md](correctness.md).

For paper derivations with separate captures and checked LaTeX/JSON output,
use `Solidity.Tools.ProgramTrace` (`#latex_program`, [latex.md](latex.md)), rather
than copying exporter internals. Disabling grouping alone does not split a
native `CaptureAll` rule.
For clickable operator definitions, configure `#latex_definition_targets`
with the paper's exact destinations ([latex.md](latex.md)).

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
`⊨ᶠ dl!{ pre → [ program ] post }`:

- **by the strategy**: `sol_symex; sol_close` (`sol_decide` for reads of
  writes; `sol_spec` for a `spec!{f}` obligation); `sol_prove` on a goal
  read with callbacks (`ValidT`, `ValidC`; [options.md](options.md));
  `sol_prove (chunk := n)` where the walk is too long for one kernel check
  (`Calculus/ProveChunked.lean`). `#wp φ` prints what
  `sol_symex` leaves, `#step φ` one step and the rule it fired.
- **by a walk**: `apply Proves.fmlValid`, then one `apply` per rule — `intro`
  (solkey's `impRight`), `update r`, `unfold r`, `split r` (KeY's two
  goals `thn`/`els`; `splitBox r` is the same rule), `Proves.check r` (an `assert`; goals `thn`/`els`; qualified,
  since `check` is also the elaborator's), `done r`, `empty`
  (`emptyModality`), `allIntro` (`allRight`) — and
  `sol_leaf; sol_close` at each leaf (`sol_leaf`: the sequent as `⊨ᶠ ψ`,
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
`Fml.LeadsK.valid h hL` proves `A` from it and `Fml.Valid L`), and `Fml.Leads.via` composes
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

## Source syntax and symbolic updates

In `sol{ … }`, decrement is `x−−` / `−−x` (two U+2212 characters):
`--` opens a Lean comment. Effects inside values, such as `++` or reference
conditionals, are captured before the statement in solc's evaluation order.
`checked { … }` makes overflow fail as an assertion;
`ignoringOverflow { … }` assumes it away. See [options.md](options.md).

Updates are typed terms, with storage sorts from `structRules.key` and memory
sorts from `memoryRules.key`. `save` / `delAt` and `write` / `addM` /
`copySt` nest. An allocation is two parallel elements; push and pop are each
one symbol, printed as KeY's nested writes over `size`.
A path alias binds bare (`{ sp := alice.account }`); a read marks the value
side (`find` / `select` / `read`).
[lean-key-rule-map.md](lean-key-rule-map.md) is the symbol table.

A `contract!{ … }` function can call functions declared before it.
`Stmt.call` carries the callee's body closed over its own frame:
`internalCallExpand` inlines it (`functionBodyExpand` for `CallRet.rets`).
Repeated calls share the same body term and its first call's local names
(`CallMemo`); calls that only compute values may use `internalCallSummary`.
See [automation.md, M6](automation.md#m6--the-automation-gate-2026-10-24).
Callbacks use a separate reading of modalities (`holdsC`, `ProvesC`) while
`Stmt.run` keeps its execution meaning; see [options.md](options.md).
