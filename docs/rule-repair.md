# Repairing a broken rule

Use this workflow for a failing Solidity example or a new rule. `|=` (`⊨ᶠ`)
is semantic validity over the typed run; `|-` (`⊢`) is derivability in the
calculus. Establish the execution meaning first, prototype a lazy rule,
reject bad candidates cheaply, then finish the proof that `|-` implies `|=`.
The semantic model is the reference, not something to change to make a
candidate rule sound.

1. **Keep the smallest counterexample and a baseline.** Record the program,
   initial state/precondition, expected observation and current failing leaf
   or rewrite. Check the relevant solc/EVM behavior when establishing the
   expected result, recording compiler version and settings. Distinguish
   defined behavior from compiler-specific/undefined behavior. Keep a nearby
   false assertion with a concrete semantic counterexample; leaving it open
   is a regression check, not a proof of soundness. Record proof nodes and
   elapsed time before changing the rule.
2. **Fix the right layer.** Is the fault in elaboration/evaluation order,
   `Stmt.run`, a program rule, a read/update rewrite, or the closer's ability
   to use it? Expand or correct `|=` only if its execution meaning is wrong
   or missing. Read `docs/module-map.md` and the conventions for that layer.
   Record a run change in `docs/solc-alignment.md`. For a closer change, start
   from SolKey's actual taclets as required by
   [Following SolKey](#following-solkey).
3. **State the candidate before implementing it.** Write its precondition,
   transformation and postcondition in plain English, as SolKey's taclet
   workflow requires. State the semantic read equations, including the
   unchanged locations, and the local agreement lemma it must satisfy.
   Prototype in an uncommitted `Solidity/Scratch/` module with local imports;
   avoid a representation refactor before testing the idea.
4. **Use cheap rejection gates.** First compare the proposed operation's
   observations with the semantic operation on concrete cases. A disagreement
   rejects the candidate. For numeric local update rules, run
   `cd Bridge && lake exe rulecheck --seed 42 --samples 1000` (Plausible,
   Lean's QuickCheck). Add the candidate to the named cases in
   `Bridge/SolidityBridge/PropertyChecks.lean`; `checkUpdateWith` also tests
   a proposed update before installing it in `Stmt.step`. Its observation
   receives the global state and typed locals: include the locations the
   rule writes and nearby locations it must preserve. The harness currently
   supports single-update premises; unsupported shapes are not successes.
   A failing run prints its seed, rule, type and shrunk operands. Preserve
   that witness as a deterministic regression. Next try the original proof and boundary cases
   under a fixed node budget and time limit. Inspect the remaining leaf:
   repeated expansion, cycling or term duplication calls for redesign;
   budget exhaustion alone does not refute the rule. Attempt the general
   local soundness lemma early, before broad integration. A counterexample
   rejects the rule; a difficult proof may instead need a helper lemma.
5. **Check the structural obligations separately.** An exhaustive `Stmt.step`
   covers the syntax. `Taclet.toStep`/`Rule.toStep` make each declared rule
   agree with that dispatcher; `Stmt.rule_exists` supplies the converse.
   `Rule.premise_unique` proves equal premises for two rules on the same
   input, not that their constructor names are equal. Check applicability
   and side conditions to maintain one named program rule per input. For
   read/update rewrites, inspect overlapping patterns and their side
   conditions separately: program-rule uniqueness does not cover them.
   Give automatic rewrites a decreasing measure or a bounded strategy;
   run an applicable termination checker if one exists and record its
   scope/result. Lean accepting a recursive definition, or `symex` consuming
   fuel, does not prove unrestricted rewriting terminates. Termination does
   not prove coverage, uniqueness or soundness.
6. **Integrate the surviving candidate and finish soundness.** For a program
   arm, prove the local run/update agreement or simulation and connect it
   through `Stmt.stepSound_arms` (or the blocks' soundness) to `Stmt.sound`;
   a new arm's lemma is a file of its own, `Calculus/Sound/<Arm>.lean`
   (`.claude/rules/soundness.md` has the template).
   For a read/update law, prove its semantic equation in `Theory/` and use
   that theorem in the rewrite/closer. Reuse the global lifting to
   `Proves.sound`/`Proves.fmlValid`; do not re-prove it for each rule. Follow
   `.claude/rules/rule-table.md` for registration and correspondence checks.
   No `sorry`, new axiom or weakened theorem to accept a prototype. Preserve
   the regression examples and measured costs, then run the review pass.

## Following SolKey

Every program, proof, term and update rule, and every storage/memory closer
clause, follows its SolKey taclet: name, `\find` / `\replacewith` shape,
schema-variable names, side conditions and branch labels. Canonical root
spelling is `save` / `find`; `store` / `select` remain accepted aliases.
Semantic deviations belong in [solc-alignment.md](solc-alignment.md).

A closer feature starts from the actual `.key` taclets. Make each one a
clause, use the interpreter lemma for soundness, cite the transcribing
`Theory/` lemma and add its row to [lean-key-rule-map.md](lean-key-rule-map.md).
Mark Lean-only clauses and deviations explicitly.

Write taclets and sequents in `dl{ … }`, and terms in `tm{ … }`, including
definition patterns and arms. Add notation and a printer with a new term
language, so `#wp`, errors and pins show the same form. Notation consists
only of macros: prove a restated type by `rfl` before checking downstream
code, establishing that kernel and compiled code see the same terms.

## What lazy means here

Keep writes, copies and resets as symbolic terms. Interpret an operation
when a `find`/`select`/`read` observes it; do not eagerly enumerate a struct,
array or mapping just to construct the update. The executable semantic
operation can use a different representation: prove agreement of the
observations rather than forcing the run to share the symbolic strategy.

Read the sibling SolKey checkout's [storage primitives](../../solkey/docs/storage.md#3-storage-model-primitives),
[shape predicates](../../solkey/docs/storage.md#8c-fixed-size-arrays-have-their-declared-length-layoutinv-types-as-sorts)
and [memory rules](../../solkey/docs/memory.md) before designing storage/memory
rules. In particular:

- `delAt(storage, path)` mentions the old storage once. Expanding it into a
  save containing both the old storage and a deleted value read from that
  storage duplicates history; repeated operations can grow exponentially.
- A copy's `save(st, nil, v)` remains a term. Its reads distinguish preserved
  destination mappings from copied members; replacing the whole leaf by
  `v` loses that distinction. A reset's reads must likewise distinguish
  mappings, primitive defaults and fixed/dynamic array lengths.
- Laziness applies to predicates too: SolKey's entry `wf` atoms answer
  demanded selectors through triggers rather than unfolding every element.
  Do not import its assumptions into Lean's typed run without justification.

Use the relevant cases to challenge a candidate: same/different/prefix paths,
aliasing, nested writes, zero/nonzero lengths, fixed/dynamic arrays, mapping
members, delete-then-copy and repeated push/pop. An illustrative read law is
`read(reset(S, p), q) = read(S, q)` for disjoint paths; the overlapping cases
need their own typed semantics. This is a design sketch, not new notation.

For bounded Lean proof-tree experiments use `ProofTree.Config.maxNodes`
passed to `ProofTree.ofFormula`/`ProofTree.build`. `symex n` bounds strategy
steps, which are not proof-tree nodes. Record the API, bound and elapsed
time, with closure/open goals if a tree returns. Node exhaustion throws an
error rather than returning a partial tree: record that as budget exhaustion.
Do not raise `maxHeartbeats` to rescue a candidate.
In SolKey, diagnose with `--why`, use `--budget` for recorded step counts,
and inspect `./run-key.sh --help` for the current runner's options. A baseline
checks regressions but is not a budget. Use each tool's actual counting unit.
