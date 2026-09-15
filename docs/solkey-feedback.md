# Improvement ideas flowing Lean → solkey

Collected during the 2026-08-29 re-sync of `lean-key-rule-map.md` against
solkey (`~/projects/solkey`, 238 program taclets). The reverse direction —
solkey rules the Lean calculus still lacks — is tracked as `planned` rows
in the map itself.

## What solkey should have and does not — ranked (2026-09-09)

A consolidated list, ordered by how much each item changes what solkey
can prove *correctly*. Items 1 and 2 are the ones where KeY can today
close a goal that is false on the chain; everything below is coverage or
hygiene. Each entry points at the Lean artefact that establishes it;
the sections further down carry the details.

1. **A correct evaluation order in the `*NonSimpleIndexCapture` taclets.**
   ~~Open~~ **Fixed on both sides, independently** — solkey in `8ba30fd742`
   (storage) and `63c38cfaf6` (memory + recursion), Lean in the
   `Rules.freezeRhs` change. The 2026-09-09 attempt noted in earlier
   revisions of this file was reverted the same day (`beeb97d2b1`); these
   are the commits that stuck.

   The bug was unsound, not merely incomplete: the taclets captured the
   target index into a fresh variable before the simple right-hand side was
   read, while solc and the Lean interpreter read the right-hand side first.
   `values[i++] = i` with `i = 0` writes `0` in Solidity and `1` under the
   pre-fix taclet.

   **Two things the Lean side learned that solkey should know.**

   *The freeze is needed even when the path is pure.* It is tempting to fire
   the freeze only on a `nonSimpleIndex` receiver and leave the ordinary
   `_unfold_leftFst` alone. That is unsound, for a reason independent of
   interference: the interpreter evaluates the value operand first, so a
   failing right-hand side decides the outcome, while an unfrozen
   target-capture residual resolves the path first, so a failing path decides
   it instead — and the two failure modes differ. A *simple* right-hand side
   can only get stuck (unbound variable); a *pure* path can revert, because
   path resolution evaluates the index and checked arithmetic reverts.
   `people[1 / 0].age = ghost` hits both at once, and
   `Counterexamples/ErrorOrder.lean` proves `¬ ResultsAgree` on it. Any
   guard of the form "freeze only when the receiver is non-simple" inherits
   this hole.

   *The four `*IndexedReceiver_unfold_leftFst` taclets are right but do not
   fire.* ~~Open~~ **Diagnosed and fixed** (patch in this working tree).
   Neither hypothesis in `docs/taclet-ideas.md` was the cause. `aliasType`
   and `rvType` coexisting is harmless — `\program Type` schema variables are
   display-only (`StatementVariableDeclaration.schemaType` is documented
   "kept for display only; not matched", `getChildCount()` returns 1, so
   `ProgramSVCollector` never collects them) — and sort matching is fine:
   `PathSVSort.classify` on `matrix[i+1]` against
   `Path[storage,complex,nonSimpleIndex]` matches, now pinned by two new
   `PathSVSortTest` cases (the `anyIndex`/`nonSimpleIndex` flags previously
   had none).

   The actual cause is a null dereference in name proposal. A schema variable
   whose sort is not the plain `ProgramSVSort.VARIABLE` gets no proposal, so
   `VariableNamer`'s `previousProposals` list can carry `null`. These four
   taclets are the only ones minting two fresh program variables at
   *different* data locations, which is what first puts a `null` in that list
   ahead of a live entry; `previousProposal.equals(...)` then throws and the
   taclet silently fails to apply. Two one-line fixes: skip `null` entries in
   `VariableNamer`, and do not append a `null` proposal in `TacletApp`. Result:
   242 -> 0 failures, 784 tests green, all three CI gates pass.

   *Where solkey is right and the Lean interpreter is wrong: reference
   sources.* The freeze above is correct for a **primitive** right-hand side.
   For a **struct** source solc is *not* right-hand-side-first — it resolves
   the target slot and copies member by member, reading the source at copy
   time — so an impure target index has already run. KeY's answer matches the
   chain; `Semantics.execAssignNested` is uniformly value-first and does not.
   Witness, added here and green on a real EVM as
   `TestSuite.storageIndexWriteRefSourceImpureIndex`:
   `persons[p.age++] = p;` stores `age == 1`. So do **not** extend the freeze
   to reference sources. This is what the `hprim` hypothesis on the Lean
   `*UnfoldLeft*` soundness theorems fences off
   (`Counterexamples/RefSourceOrder.lean`, `docs/solc-alignment.md`); the fix
   owed is on the Lean side.

   *The deleted `Inner*NonSimpleIndexCapture` pair was doubly wrong*, which
   is worth recording rather than just dropping: its `\find` was hard-coded
   to `e1[nse][e2]`, so `m[i++][j][k] = v` matched nothing, **and** it bound
   `pv = nse` before reading `se`, so it had the same evaluation-order bug at
   depth 2. Lean never modelled it separately — it always captured the whole
   inner path, which is strictly more general.

2. **Checked `uint256`/`int256` arithmetic.** Solidity ≥ 0.8 reverts
   when `+`, `-`, `*`, unary `-` and the compound forms leave the type's
   range. The Lean interpreter models it (`Semantics.checkArith`), the
   specification layer discharges it (`docs/spec-language.md`), and the
   EVM compiler proves the guard (`Evm/Compile.checkedOpCode`,
   `Evm/Correctness.checkedOp_sim`). solkey's arithmetic taclets
   compute in unbounded `int`, so a postcondition proved in KeY can be
   false on the chain when a value wraps and the transaction reverts.
   Either the arithmetic taclets split on the range (revert branch
   under `\diamond`, closed branch under `\box`) or the sort `uint`
   carries the range as an axiom that every update re-establishes.

3. **A `wellFormed(storage)` precondition, stated once.** The taclets
   consume facts the symbolic storage does not provide: `size ≥ 0` for
   `pop`, an in-bounds `at(i)` read succeeds, an unwritten mapping key
   reads `defaultValue`, a declared struct member is never stuck.
   `WellFormedConsumers.lean` proves every such row from
   `wellTypedStorageB`/`canonicalStorageB`, and `Reachability.lean`
   shows the canonical form is exactly what execution from the initial
   state reaches. In solkey these facts come from nowhere. Shape it
   like `heapRules.key`'s `wellFormed(heap)`: proving taclets per store
   constructor, using taclets per consumer row (details in
   "Is `wellFormed(storage)` complete?" below).

4. **A balance-checked `transfer`.** `a.transfer(v)` reverts when the
   contract's own balance cannot cover `v` (the EVM value-transfer
   check). The Lean semantics reverts (`Semantics.execStmt`, transfer
   arm), the compiled code checks the reserved balance word
   (`Evm/Compile.transferTail`). solkey's `net` ledger debits
   unconditionally, so any claim that a transfer completes is
   unconditional in KeY and conditional on the chain.

5. **The calculus's real boundary, written down.** Progress is false
   for the conditional rules: `if (flag) …` with a symbolic stack boolean has
   no rule under any modality (`Progress.lean`, `not_progress`,
   `not_normalizing`); the split belongs to the judgment layer
   (`symbolicIte_judgment_split`; solkey's `ifSplit`). Completeness holds
   only over a rule-independent fragment: well-typed (`stmtWt`) and not
   one of the 24 syntactic `ResidueShape` families of `Coverage.lean`
   (`RuleStep.complete_of_wellTyped`). That list — symbolic `if`
   conditions, `**=`, inc/dec on memory or storage-local targets,
   stack values into storage-local roots, `delete` on storage-local
   roots, memory-value pushes, … — is the precise statement of what the
   taclet corpus does not cover; solkey's docs should carry it instead
   of leaving users to discover a stuck proof.

6. **`unfoldArgument` (Lean `functionCallArgCapture`).** Already on
   solkey's backlog (`docs/net.md` §5.1). The Lean rule plus its
   inlining-relative soundness statement is a worked design, and its
   hypotheses are the taclet's side conditions: the captured argument
   mentions no callee parameter, the callee body and result are free of
   the fresh `pv`. That its Lean proof is still a documented `sorry`
   (`functionCallArgCapture_sound_inlined`) is an argument for a
   calculus rule rather than a user-side rewrite.

7. **Determinism under the block modality.** solkey's rule set is
   mutually exclusive per modality (`Uniqueness.lean`,
   `stepCases_exclusive`), but under the block modality a box/diamond
   twin pair applies at once. The twelve twin pairs are effect-identical
   up to mode (`CandidateStep.twinEffects`); KeY's strategy should
   either prefer one deterministically or the taclets should share a
   single mode-generic rule. Not a soundness issue — a proof-search and
   reproducibility one.

8. **The two open `Struct` sort findings** (`SortFaithfulness.openFindings`).
   ~~Open~~ **Fixed upstream on 2026-09-10.**
   `find<[Struct]>` reads whose value is a `Struct` node at run time but
   whose static sort is an array or mapping sort below `StValue`. Sound
   today because the corpus binds only `alphaPrim`; latent for any
   future `alphaSt`-bound rule (`Counterexamples/StaticRuntimeSort.lean`).
   solkey took the first of the two options offered: `SolJSONParser` now
   builds `T[]`, `T[n]` and `mapping(K => V)` with `Struct` as their
   supersort rather than `StValue`, so the lattice states what the values
   already were, and `docs/storage.md`'s "`Struct` (incl. the dynamically
   created array/mapping sorts)" became true of the lattice rather than
   only of the prose. `docs/taclets-implementation.md`'s sort paragraph —
   which called `StValue` "`Struct` + `Prim`" and then added a third
   family two lines later — was rewritten to match, and
   `SolJsonParserTest#arrayAndMappingSortsExtendStruct` pins it.

   **One correction to the report.** The `\hasSort` route was not the only
   latent binder of `alphaSt`: `findStValueCast` binds it by *matching* the
   cast `selectOnStore` inserts, with no varcond involved. That widens the
   exposure the finding describes, and it is the route item 9 below turned
   out to travel.

9. **`StValue`-instantiated delete reads.** ~~Open~~ **Fixed upstream on
   2026-09-10.** After the delete-family fix (`e67a0d7c48`) a
   delete-then-copy sequence on an `StValue` read is a stuck term. A gap,
   not an unsoundness (section below).
   The observed stuck term for `bob.account.balance = 10; delete
   bob.account; alice.account = bob.account;` was
   `cast<[Struct]>(delValue<[StValue]>(save(…)))` — note the cast *is*
   present, which is what made the fix cheap. solkey added one taclet,
   `delValueStValueCast` in `structRules.key`, the twin of `findStValueCast`
   for that shape:
   `cast<[alphaSt]>(delValue<[StValue]>(v))` ⇝
   `delValue<[alphaSt]>(cast<[alphaSt]>(v))`. The cast then meets
   `castDel`, and one of `delValueStruct` / `delValueDefault` fires, so the
   `Struct`/`Prim` split stays disjoint — widening `delValueDefault` back to
   `StValue` would have reintroduced exactly the overlap `e67a0d7c48`
   removed. Three new examples (`storageFieldDeleteThenCopy`,
   `storageFieldDeleteThenCopyDeep`, `storageRootDeleteThenCopy`) all fail
   without the rule and close with it.

   The parallel `selectSt<[StValue]>(delNode(…), f)` shape the analysis
   predicted turned out to be unreachable in the corpus: a
   `selectStStValueCast` twin was written, found to change nothing on any
   of the three traces, and dropped rather than shipped unused.

10. **Memory compound assignment and the small simplifiers.** ~~Open~~
    **Fixed upstream on 2026-09-10.** `mv.x += se`
    has no taclet; `ifElseTrue`/`ifElseFalse`/`ifElseNegated` only remove
    trivially closed goals. Convenience.
    solkey added the full memory matrix rather than the single rule: 44
    taclets, `memoryCompoundAssign` (`+= -= *= /= %=`) and `memoryIncDec`
    (pre/post × inc/dec, statement and `result = …` forms), each with a
    `_unfold_leftFst` twin, over `{field, indexArray}` — there is no root
    form (a memory root holds an `Identity`, never an int cell) and no
    mapping form (memory has no mappings). They are the storage rules with
    `find`/`save` replaced by `read`/`write`; no new capture rules were
    needed, since `addAssignValueRhsCapture` and friends already take a
    plain `Expression` target. The indexed terminals had to form their own
    `RuleGeneralizationTest` groups: memory states its bounds with
    `\sameUpdateLevel` + `\add`, storage with an implication inside
    `\replacewith`. 27 new examples.

    The five simplifiers are `ifTrue`/`ifFalse`/`ifElseTrue`/`ifElseFalse`
    (the Lean rules now carry the same names) and
    `ifElseNegated`, in the `concrete_solidity` rule set, which was declared
    and costed (−11000 in `SymExStrategy`) but had no members until now, so
    they outrank both `ifSplit` and `ifElseUnfold`.

    **One thing the proposal did not anticipate.** `ifElseTrue`/`ifElseFalse`
    were not writable as stated: `Literal#match` compares with `equals`,
    `BoolLiteral` overrode only `computeHashCode`, and the two parsers
    disagree on identity — the `.key` path builds a fresh `BoolLiteral`,
    the `.sol` path returns the `TRUE`/`FALSE` singletons. A taclet pattern
    `if (true) s#s0` compiled and matched nothing. `BoolLiteral` now
    overrides `equals`/`hashCode` as `Uint256Literal` already did.

11. **Housekeeping.** ~~Open~~ **Resolved on 2026-09-10 — two of the three
    items were stale in *this file*, not in solkey.**
    - `memoryToStorageIndexArrayCopyRoot` **does** exist upstream, at
      `solidityProgramRules.key:1014`, with exactly the `[slen, slen]`
      reads `TacletAnnotations.lean` records. It was neither renamed nor
      unmerged: it arrived in `4c486907c8`, and the `SolKey` reader's
      vendored pin was 12 commits behind at `e67a0d7c48`, so
      `check-solkey.sh` was reading a vendored corpus that predated it.
      The pin is now `beeb97d2b185fe70435c88865a31f20877c51ee6` and that
      row passes. (Note the pin does *not* yet include the items 8–10 work
      above, which is uncommitted upstream — one more
      `vendor-key.sh --update` is due once it lands.)
    - The claim that `docs/taclets-implementation.md` says the `net-*`
      starters were deleted is false at upstream HEAD: the doc describes
      them as present and driving `NetExamplesTest` (`:431-438`). The
      likely misreading is `:489-491`, about the removed end-to-end test
      `testStorageArrayPushPop`. `keyext.solidity.examples/net/` holds 23
      `.key` problems and 5 `.sol` contracts, not 20 `.key`.
    - The `solidity-key-taclets` skill was genuinely stale and has been
      rewritten: all five `keyext.solidity.examples/taclets/*.key` starters
      it named are gone, so is that directory's `README.md`, and
      `TacletStarterExamplesTest.examples()` is now a one-line enumeration
      with nothing to register.

    Also fixed while there, all found by reading rather than reported:
    `docs/taclet-ideas.md` and `docs/taclets-implementation.md` still
    listed `if` as unimplemented and named a `ternarySplit` rule that is
    now `ternaryToIf`/`ternaryToIfStorage`; the delete section claimed
    "any non-struct sort" where `delValueDefault` is `alphaPrim`-bounded;
    two places claimed `storageIndexWrite{Array,Mapping}CopySource` use
    `find<[alphaSt]>` + `\hasSort` where they use `find<[StValue]>`; and
    the starter count was 68 low.

    **Still open on the Lean side** (unrelated to the above, surfaced by
    re-running the check against the current corpus): 19 `MISSING TACLET`
    rows where `TacletAnnotations.lean` still names taclets upstream has
    since split or renamed — `storageIndex{Add,Sub,Mul,Div,Mod}Assign` and
    `storageIndex{Pre,Post}{in,de}crement*` are now `…Mapping…`/`…Array…`
    pairs, and the `*_root` / `*_decompose` suffixes are now
    `*_unfold_{leftFst,rightFst}`. Plus one `READ DRIFT`,
    `storageFieldWriteCopySource`, where the table says `Struct` and the
    rule says `StValue` — the table is behind, the rule is the sort-free
    copy described in item 9.

Two further ideas that are not gaps but would make the correspondence
cheaper to maintain:

- **Rule-parity as a CI test.** the `SolKey` reader already checks taclet
  names and read sorts against the `.key` corpus. The next step is to
  check *conditions*: the Lean `candidate` dispatch mirrors every
  taclet's guard, and `applicable_eq_candidate` is what makes
  exclusivity a theorem. Exporting the guards (or a hash of them) from
  solkey's test suite would catch an overlapping new taclet before it
  reaches a proof.
- **Terminal rules as updates.** Every terminal taclet (empty residual)
  now has an explicit state update in the interpreter's vocabulary
  (`Wp/TerminalUpdate.lean`) with `execStmt s stmt = terminalUpdate
  r stmt s` under the taclet's guard. Those updates are the KeY update
  algebra; the equations are a per-taclet test oracle solkey could run
  on its own `.key` examples.

## Candidate taclets

- **`unfoldArgument`** (Lean `functionCallArgCapture`): hoist the leftmost
  complex argument of a function call into a fresh `pv` before
  `functionBodyExpand`. Already on solkey's own backlog (`docs/net.md`
  §5.1); the Lean rule plus its soundness proof
  (`RuleSoundness.functionCallArgCapture_sound`) is a worked design.
- **Literal-condition if rules** (Lean `ifElseTrue` / `ifElseFalse`): ✅ implemented
  2026-09-10 as `ifTrue`/`ifFalse`/`ifElseTrue`/`ifElseFalse`, in
  `concrete_solidity` rather than `simplify_prog` so they outrank the split.
  Needed a `BoolLiteral.equals`/`hashCode` fix first — see ranked item 10.
- **`ifElseNegated`** (Lean `ifElseNegated`): ✅ implemented 2026-09-10, same
  rule set, so it outranks `ifElseUnfold`'s capture of the negation.
- **Memory compound assignment**: ✅ implemented in solkey 2026-09-10 as
  `memoryCompoundAssign` + `memoryIncDec` over `{field, indexArray}` (ranked
  item 10). Still absent on the Lean side.

## Semantics observations from the Lean proofs

- **Evaluation order / non-interference**: the Lean per-rule soundness
  proofs surfaced that the RHS-first `*ValueRhsCapture` rewrites are only
  meaning-preserving when the assignment target's index and the RHS do not
  interfere (the `hstable` hypothesis of
  `RuleSoundness.valueRhsCaptureAssign_sound`; cf. KeY's
  `testStorageEvaluationOrder`, `a[++i] = ++i`). Worth stating explicitly in
  `docs/storage.md` §evaluation-order.
- **The `*NonSimpleIndexCapture` taclets were unsound on an interfering
  impure index** (`storageIndexWriteNonSimpleIndexCapture` and its memory
  and depth-2 siblings): they captured the index into a fresh variable
  *before* the simple RHS was read, but solc — and the Lean interpreter —
  read the RHS first. On `values[i++] = i` with `i = 0` the program writes
  `0` and the residual wrote `1`. Lean-checked in
  `Counterexamples/EvaluationOrder.lean` (`indexWrite_not_sound`).
  **Fixed upstream 2026-09-09** by the `*ValueRhsCapture` order: bind the
  RHS first, then capture the index; see ranked item 1 for the full
  account, including why the `*_unfold_leftFst` family was never affected
  in solkey and why `fieldWrite_not_sound` refutes the calculus's rule rather
  than the taclet.
- **`commuteSimpleUpdates`** (commented-out in `updateRules.key`) is false
  as state equality on an assoc-list storage representation — only true
  pointwise. Keep it dead.

## Sort-level observations (from the shared `KeySort` lattice)

Collected on 2026-09-02 while making `Solidity`'s types the same
shape as solkey's sort model (`Solidity/KeySort.lean`, `Ty.keySort`,
`Field.sort` computed from the declared type; the `SolKey` reader's
`Decode/PathSort.lean` for the schema-variable sorts). Each item is a
Lean-checked fact about upstream at `e67a0d7c48`.

- **Array/mapping static sorts vs. their runtime nodes.** `SolJSONParser`
  gives an array type its own sort `T[]` and a mapping type
  `mapping(K => V)`, each `\extends StValue` *directly* — siblings of
  `Struct` (`SolJSONParser.java:1015-1030`, `valueSupersort("StValue")`).
  At runtime the value at such a path is a `Struct` node (built from
  `mtSt` with `at(i)` fields; the copy taclets read it `find<[Struct]>`).
  `Counterexamples/StaticRuntimeSort.lean` proves the two sorts are
  incomparable. Consequence: a `\hasSort(x, \sort(alphaSt))` on an
  array- or mapping-typed path binds `alphaSt := uint[]`, and the
  `find<[alphaSt]>` it produces is a term no `selectSt`/`find` rule (all
  stated on `Struct`) can consume. Latent today — `\hasSort` binds only
  `alphaPrim` in `solidityProgramRules.key` — but any future taclet
  binding `alphaSt` on an unconstrained `Path` would hit it. Either make
  the created sorts `\extends Struct` (then `docs/storage.md`'s "Struct
  (incl. the dynamically created array/mapping sorts)" becomes true of
  the lattice, not just of the prose) or keep `alphaSt` off value reads.
  ✅ **Fixed 2026-09-10** — solkey took the first option; `Decode/Sorts.lean`
  and `Solidity/KeySort.lean` now lag the upstream lattice and need the same
  edit. (Ranked item 8.)
- **`docs/taclets-implementation.md` / `docs/storage.md` describe the
  lattice as `Struct` including the array/mapping sorts**; the headers and
  `SolJSONParser` say otherwise (previous item). One of them should move.
  ✅ **Fixed 2026-09-10** — the parser moved, and
  `docs/taclets-implementation.md`'s paragraph (which contradicted itself)
  was rewritten to match.
- **`PathSVSort.createInstance` ignores the receiver's presets**: it
  builds `PathFilters` from scratch, so `StoragePath[memory]` is
  `Path[memory]` and `SimpleStoragePath[complex]` is `Path[complex]`. No
  corpus file parameterises a named variant, so nothing is wrong today;
  worth either refusing parameters on the named variants or seeding the
  filters from them. (`Decode/Sorts.lean` mirrors the current behaviour.)
- **`ProgramVariableSVSort.createInstance` matches the joined parameter**,
  so `Variable[storage,local]` is accepted and `Variable[local,storage]`
  is not, while `PathSVSort` accepts its flags in any order. Cosmetic.
- **`memory,global` is refused on `Path` but `memory` + `Origin.GLOBAL`
  cannot arise anyway** (`classify` gives a `FieldReference` storage,
  and every memory local `Origin.LOCAL`): the explicit check is dead but
  harmless.
- **`SimpleExpressionSVSort` excludes contract fields** (`Literal |
  ProgramVariable` only; a state variable is a `FieldReference`), so
  `NonSimpleExpression` admits a bare storage root. The Lean rules treat a
  storage root as *simple*; the difference is invisible in the corpus
  because every `SimpleExpression` position is value-typed there, but it
  is a real gap for any future taclet with `SimpleExpression` in a storage
  position. Recorded in `Decode/PathSort.lean`.

## Sorts vs. storage wellformedness (2026-09-02)

Asked whether `find(st, p)` on an int-declared field needs a storage
wellformedness ("wellfoundness") invariant to return an int. Split
answer, machine-checked in `Counterexamples/WellTypedNecessity.lean`:

- **Calculus soundness: no invariant needed.** `find<[int]>` is
  int-sorted by construction, and every mismatch degrades to an
  underspecified cast: `selectOnStore` emits `cast<[alpha]>(v)`,
  `castDel` fires only when the argument's static sort already fits,
  and `cast.key` gives the mismatch case no axioms. Underspecified
  values prove nothing false. Values written in-proof are recovered
  syntactically (read-over-write unfolds; `findStValueCast` pushes a
  read's cast onto the sort-free copy source), so the common
  write/copy/read patterns also need no invariant.
- **Faithfulness to the interpreter: indispensable.**
  `SortFaithfulUntyped` (= `SortFaithful` minus `wellTypedStorageB`) is
  refuted for the live `storageRootReadSelect` table row — the same row
  `sortFaithful_all` proves *with* the hypothesis. The invariant is
  exactly the boundary.
- **Completeness: a `wellFormed(storage)` assumption is needed where
  the underspecified value must be *constrained*, not just typed** —
  first of all `find<[int]>(storage, consr(sp, size)) >= 0` on a
  symbolic initial storage: without it `storagePopSave`'s "empty"
  branch and every bounds check downstream of an unknown `size` are
  unprovable. That means: a wellformedness predicate in the proof
  obligation plus preservation through every `save` the rules emit —
  the calculus twin of `wellTypedStorageB`.

Update 2026-09-02: that preservation theorem is now machine-checked —
`TypeSoundness.execStmt_sound`/`execBlock_sound` prove full type
soundness of the interpreter (storage + env + heap invariants, `StateWT`),
so `wellFormed(storage)` is a legitimate once-assumed PO hypothesis:
`execBlock_preserves_wellTyped` carries it to every reachable state and
`run_then_find_int` closes the original question end-to-end. The
"only with wellformed" boundary is drawn by six one-hypothesis-dropped
refutations in `Counterexamples/PreservationNecessity.lean`, two of
which carry calculus-side lessons for solkey: program-variable typing
(a lying stack binding breaks storage well-typedness from a well-typed
store — KeY's program-variable sorts are the calculus twin) and the
`checkArith`-passes-bools subtlety (a non-arithmetic `op=` slips a bool
into a `uint` cell — `op.isArith` is load-bearing in the compound
taclet family too).

## Is `wellFormed(storage)` complete? Tightness (2026-09-03)

Asked how to guarantee nothing is *missing* from the invariant — whether
`wellFormed` already carries every fact that can be inferred. The
question has a formal reading: "everything inferable" is exactly what
holds on every *reachable* storage, so the invariant is complete iff it
coincides with reachability from the contract's initial state. Both
directions are now machine-checked in `Reachability.lean`:

- `reachable_wellTyped` — reachable ⇒ well-typed (preservation from
  `initialState L`, whose `StateWT` proof `initialState_wt` is the
  base case "assume `wellFormed` once" was missing);
- `storage_tight` / `canonical_reachable` — canonical ⇒ reachable: a
  program `writeProg` (literal assignments, `push()`, `delete` to
  materialise mapping entries) builds any canonical storage;
- `no_hidden_invariant` — any storage property that holds initially and
  is preserved by every well-typed program already follows from
  `canonical`.

The exercise found that `wellTypedStorageB` is **not** tight: execution
maintains three facts `SVal.hasTy` forgets, and `SVal.canonical` adds
exactly those —

1. a mapping's default is the type's default (`save`/`defaultOf` never
   touch `dflt`; `hasTy` only asks `dflt.hasTy value`) — the
   `Witness.badDfltStorage` mapping with default `7` is well-typed, and
   a read of an unwritten key returns `7`, so any "read of an unwritten
   key is `defaultValue`" taclet is *unfaithful* on it;
2. mapping keys are unique (entries only grow by `setBy`);
3. a struct carries exactly its declared fields, in order
   (`defaultForTy` creates them, no operation removes one; `hasTy`
   checks only the fields present) — on `Witness.missingFieldStorage`
   a read of the declared `token` field is `.stuck`.

Conversely `uint` range is **not** an invariant of the model:
`Witness.uint_negative_reachable` runs `total = -5;` from the initial
state (literals and plain assignments are unchecked; only arithmetic
goes through `checkArith`). So the `find<[int]>(storage, consr(sp, size))
>= 0` fact `storagePopSave`'s non-empty branch needs does not come from
the *cell type*: it is the `size`-cell discipline (`push`/`pop` are the
only writers; in Lean the length is structural), which a KeY-side
`wellFormed(storage)` must state explicitly.

**Calculus-side proposal.** solkey has no `wellFormed(storage)` today
(only Java's `wellFormed(heap)` in `heapRules.key`). The Lean results
say what such a predicate must contain and how to keep it complete:

- shape it like `heapRules.key`'s two families — *proving* taclets, one
  per store constructor (`save`, `delAt`, the push/pop `save`s),
  mirroring `save_hasTy`/`save_canonical`, and *using* taclets, one per
  consumer row of `WellFormedConsumers.lean` (`size ≥ 0`; `0 ≤ i < size`
  ⇒ the `at(i)` read is typed; unwritten key ⇒ `defaultValue`; declared
  member ⇒ `selectSt` is defined);
- state explicitly what Lean's `SVal` datatype gives for free:
  `size ≥ 0`, `at(i)` present exactly for `0 ≤ i < size`, mapping
  default = `defaultValue`, exactly the declared members;
- the completeness check going forward is the consumer table: a new
  taclet that needs a storage fact its `\assumes(wellFormed(storage))`
  cannot deliver shows up as an unprovable row.

Open: the converse invariant "reachable ⇒ canonical" (needed to *refute*
reachability of the non-canonical witnesses) is a second
`TypeSoundness`-sized traversal of the interpreter, and env/heap
tightness (up to identity renaming) is likewise future work.

## Delete-family generic overlap (found at `0f9b99ad55`, fixed at `e67a0d7c48`)

`Counterexamples/DeleteFamilyGenericOverlap.lean` proves the
`0f9b99ad55` delete fallthroughs (`delValueDefault`,
`selectStDelNodeDefault`, both bounded `alphaSt \extends StValue`)
overlapped their dedicated `Struct` rules at `alphaSt := Struct` — two
first-order inconsistency theorems derive `5 = 7` from the taclet
equations alone (no ill-typed store required; reachable via
`delete s.member;` + any later `Struct`-sorted read through
`selectOnDelAtCons`). Generic-sort upper bounds admit everything below
them; they discriminate only when the bound *excludes* the special
case. `e67a0d7c48`'s re-bounding to `alphaPrim \extends Prim` (plus
`selectStDelNodeIndexStruct`) is exactly the fix the proofs demand —
same pattern as `memoryRules.key`'s `prim \extends Prim`.

**~~Still open there~~ Fixed 2026-09-10 by `delValueStValueCast`; ranked item 9
has the account. Original text: `StValue`-instantiated delete reads are stuck.**
`selectOnDelAtCons` instantiates `alpha` at the outer read's sort, and
the copy taclets read `find<[StValue]>`. On `delete s.p; x = s.p;`
(struct-typed `p`, root target, `storageRootWriteCopySource`) the
unfolding reaches `delValue<[StValue]>(selectSt<[StValue]>(node, p))` —
`StValue` is neither `Struct` nor `≤ Prim`, so no delete rule matches,
and no later cast revives it (`findStValueCast` needs the cast directly
on `find<[StValue]>`). Delete-then-copy fails to symbolically execute.
Candidate fixes: `delValueStValue` / `selectStDelNodeStValue` twins of
`findStValueCast` that re-sort through the declared type, or have the
copy rules avoid `StValue` reads over `delAt`/`delNode` terms.

## Housekeeping (stale solkey docs/tooling) — resolved 2026-09-10

- ~~`docs/taclets-implementation.md` claims the `net-*` starters were deleted,
  but 20 committed `.key` problems remain in `keyext.solidity.examples/net/`.~~
  **Not a real finding.** The doc says the opposite; see ranked item 11.
- ~~The `solidity-key-taclets` Claude skill still points at
  `keyext.solidity.examples/taclets/*.key` starter files and
  `TacletStarterExamplesTest.examples()`~~ — **fixed**: the skill now describes
  the `TestSuite.sol` workflow, the `test*`/non-`test*` suite split, the
  `RuleGeneralizationTest` step for operator families, and the three CI gates.

## Delete-then-copy, resolved (2026-09-10)

The "Still open there" note at the end of the delete-family section below is
closed by `delValueStValueCast`; see ranked item 9 for the fix and for why the
`selectSt<[StValue]>(delNode(…), f)` half of the prediction was dropped as
unreachable.

## `selectOnSaveEmpty` rewrites to a term its `\find` does not bind (2026-09-15)

`structRules.key`:

```
selectOnSaveEmpty {
    \find(selectSt<[alpha]>(save(st,nil,v), a))
    \replacewith(selectSt<[alpha]>(save(st,flds,v), a))
    \heuristics(simplify)
};
```

The `\find` binds `st`, `v` and `a`. It does not bind `flds` — that schema
variable is declared at the top of the file and left free by this taclet, so
the `\replacewith` names a list the match never determined. Read literally the
rule rewrites a closed term to one with an unconstrained subterm.

The intended reading is presumably `selectSt<[alpha]>(v, a)`: `saveOnEmpty`
already gives `save(st, nil, v) ⇝ v`, so the rule is subsumed by it and the
`flds` looks like an editing residue from `selectOnSaveCons` just below.

Lean's `Theory/Storage.lean` states the intended form
(`StValue.selectOnSaveEmpty : selectSt (save st [] v) a = selectSt v a`) and
records the difference in `docs/lean-key-rule-map.md`.

**Worth checking upstream** whether KeY's schema-variable well-formedness
check should reject a `\replacewith` that mentions a variable the `\find` does
not bind. If it should, this taclet is the witness; if it should not, the rule
is unsound as written rather than merely redundant.
