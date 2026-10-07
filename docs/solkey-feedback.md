# Improvement ideas flowing Lean → solkey

The only outbound document: what the Lean model shows solkey (`~/projects/solkey`,
<https://github.com/SolidiKeY/solkey>) could gain or should tighten. The reverse
direction, solkey rules the Lean calculus lacks, is tracked as `planned` rows in
`docs/lean-key-rule-map.md`.

**Pinned to solkey `1b4341a303`** (323 taclets, the `solkeycheck` baseline in
`AGENTS.md`). The items were checked against `f2eb3d98eb`; the commits since
add `try`/`catch` (`tryCallNoCallbackBox`, `tryCallWithCallbackBox`) and
rename memory's `default` to `init`, and touch no rule an item below is
about but item 3's, which `671f6762a9` partly resolves. `78f42fde33` adds `\sameUpdateLevel` to the four allocation taclets;
Lean needs no counterpart (`docs/lean-key-rule-map.md`, legend).
`b959555181`, `671f6762a9` and `1b4341a303` add `send`, internal calls with
return targets and the function frame (ten taclets; items 7 and 8).

**Ranking.** Items that let KeY close a goal that is false on the chain come
first, then missing rules and missing invariants, then refusals, then
simplifications, then hygiene and sort-level observations. Each item gives the
problem, the Lean evidence and the suggested fix. Items are numbered for
citation, not as a schedule.

## 1. Checked arithmetic (can close a false goal)

**Problem.** Solidity ≥ 0.8 reverts when `+`, `-`, `*`, unary `-` and the
compound forms leave the type's range. solkey's arithmetic taclets compute in
unbounded `int`, so a postcondition proved in KeY can be false on the chain when
a value wraps and the transaction reverts. `docs/taclet-ideas.md` (Tier 5) and
`docs/taclets-implementation.md` record it as a deliberate choice; it is still
the largest gap between a solkey proof and the chain.

The same choice reaches the specifications. A clause's `+`/`-` is solc's
checked arithmetic in Lean (`\old(balances[to]) + amount` overflowing makes the
equation false) and KeY's unbounded `int` in solkey. A parameter is a KeY `int`
with no range; Lean's obligation assumes `0 <= x <= 2^256 - 1` for a `uint`
(`rangeFml` in `Calculus/Spec.lean`), so a clause like `requires amount >= 0` is
redundant there and load-bearing in solkey.

**Lean evidence.** `Semantics.checkArith` (`Semantics.lean`); the EVM compiler
proves the guard: `checkArith_uint`, `checkArith_int`, `tail_sim`
(`Evm/Correctness.lean`), `overflow_run`/`overflow_interpreter`
(`Evm/Examples.lean`).

**Fix.** Either split each arithmetic taclet on the range (revert branch under
`\diamond`, closed branch under `\box`, as Java KeY's `inInt`/`expandInInt`), or
give the sort `uint` its range as an axiom every update re-establishes. In
either case add the range of each `uint` parameter to `specifiedProblemText`
rather than relying on the user's `require`.

## 2. A `wellFormed(storage)` beyond `size >= 0`

**Problem.** solkey has one storage fact, `sizeNotNegative` (`structRules.key`;
`docs/storage.md` §8b). The taclets consume more that nothing provides: an
`at(i)` read with `0 <= i < size` is typed, an unwritten mapping key reads
`defaultValue`, a declared struct member is never stuck, and a `uint` cell is in
range. This is a completeness and faithfulness gap, not an unsoundness: a read
on a mismatching store degrades to an underspecified cast and proves nothing
false (`WellTypedNecessity.readSelect_needs_storage` shows the interpreter-side
claim does need the invariant). A `\forall` clause over a mapping is provable
in Lean only under the layout premises `layoutAt` states (`Calculus/Spec.lean`);
solkey's obligation states none.

**Lean evidence.** `Prog.run_wt` (`Typing/Soundness.lean`) preserves
`RunWT`, so the invariant can be assumed once. It is not tight:
`SVal.canon` adds what `hasTy` forgets (mapping default is the type's default,
mapping keys are unique, a struct carries exactly its declared members), and
`Prog.run_canon`, `reachable_canon`, `map_default_not_reachable` and
`struct_missing_field_not_reachable` (`Typing/Reachability.lean`) prove that
canonical storage is what execution keeps. `SVal.tight`, `reachable_iff` and
`no_hidden_invariant` (`Typing/Constructibility.lean`) prove canonical and tight
is exactly reachable, so no hidden invariant is missing. `uint` range is not an
invariant of the model (literals and plain assignments are unchecked), which is
why item 1 owns it.

**Fix.** Shape it like `heapRules.key`'s `wellFormed(heap)`: *proving* taclets
per store constructor (`save`, `delAt`, the push/pop `save`s), *using* taclets
per consumer (`0 <= i < size` ⇒ the `at(i)` read is typed; unwritten key ⇒
`defaultValue`; declared member ⇒ `selectSt` is defined). A taclet that needs a
storage fact its `\assumes(wellFormed(storage))` cannot deliver then shows up as
an unprovable example.

## 3. `unfoldArgument` (Lean `functionCallArgCapture`): partly resolved upstream (`671f6762a9`)

**Upstream.** At `1b4341a303` an in-program call `f(args);` / `lhs = f(args);`
is `internalCallExpand`'s (`\program InternalCall ic`, any arguments), and
`expand_function_body` binds every argument as a fresh `T p = arg`, simple or
not, so a non-simple argument is no longer stuck.  Lean keeps its capture
rule (`functionCallArgCapture`), so that its call rules (`internalCallExpand`,
`functionBodyExpand`) take simple arguments only and every call has one rule.
What remains is the shape difference, recorded in `docs/lean-key-rule-map.md`;
the text below is the item as it stood at `f2eb3d98eb`.

**Problem.** `f(nse)@C` with a non-simple argument is stuck: `functionBodyExpand`
matches only the whole-program call statement, and no rule hoists the argument
into a fresh local. It is on solkey's own backlog (`docs/net.md` §4 item 1;
`docs/bugs.md`, "Internal calls are never inlined").

**Lean evidence.** The one rule of the Lean calculus solkey lacks:
`LeanTaclet.functionCallArgCapture` (`Calculus/Rules.lean`), proved
`LeanTaclet.sound` (`Calculus/RuleSoundness.lean`). Its hypotheses are the
taclet's side conditions: the captured argument mentions no callee parameter,
and the callee body and result are free of the fresh `pv`. On programs whose
calls take simple arguments and, under the diamond, pay no one (`Stmt.inSolkey m`, `Calculus/SolkeyFragment.lean`)
solkey's rules alone derive what the whole calculus does (`Proves.toSolkey`).

**Fix.** Add the rule with those side conditions. Until then a program with a complex
argument stays stuck, which is safe.

## 4. What solkey should refuse or leave stuck

The Lean syntax cannot write the programs below (each right column is the
constraint that excludes it). solkey is sound on them if it refuses them or has
no taclet for them; where it has a taclet, the taclet must agree with solc. Only
the first two rows are checked rejected in solkey (`MAPPING_COPY_ERROR`,
`MEMORY_MAPPING_ERROR` in `ParserUtils.java`); the rest were not re-tested
against the parser.

| solkey should refuse | Lean |
|---|---|
| a call whose argument reads an earlier parameter (sequential binding differs from solc) | `Arg.separatedFrom` |
| `delete` of a mapping or through a storage alias | `Stmt.delete` takes a `Loc` |
| `push`/`pop` on a memory or fixed-size array | `Stmt.push`/`pop` at `.array` |
| a storage reference copied into a memory member or element | `MSrc` has no copy form |
| a default (`push()`, `T memory m;`, `delete m`) of a type whose default is ill-formed | `defaultOkS` |
| `new` of anything but a dynamic array of mapping-free elements | `RefTy.newArrOk` |
| `op=`, `++`, `--` on a `bool` | `PrimTy.isNumeric` |
| effects inside a value (`++` under `&&`/`||`, in a conditional branch); a conditional of reference type | `Val` has no effect; the elaborator hoists the rest |
| recursion; reference parameters; a `return` before the end; a call inside an expression | the elaborator; `Arg`, `CallRet` |

A program no taclet matches (`**=` and other compound operators outside
`+= -= *= /= %=`, a compound target at a non-simple index, `y = nsp.f++;`) stays
stuck, which is safe. Three things are not syntax and a solkey proof can be
wrong on the chain without them: checked arithmetic (item 1), a `delete` that
keeps a struct's mapping members (`docs/solc-alignment.md`), and well-formed
storage (item 2). Rules whose premise differs from their taclet's without
changing the syntax (bounds as a revert inside the update) are in
`docs/lean-key-rule-map.md`.

## 5. The `save` leaf should collapse

**Problem.** `save(st, nil, v)` is a leaf every write leaves, read through by
member sort by six taclets (`saveOnEmptyPrim`, `selectOnSaveEmpty{Map,Ref,Fixed,
IndexStruct,Default}` in `structRules.key`), so that a struct written over a
location keeps the location's mapping members. That is the one case neither
side reaches: a storage-to-storage copy of a mapping-carrying type is rejected
by solc ≥ 0.7 and by `ParserUtils.parseAssignmentMaybe`, and Lean cannot build
it (`Src.copy`'s `mapFree`). On every program the two theories agree, and the
lazy leaf costs a term that grows with every write and six taclets where the
signature has one rule, `saveEmptyPath` (`save(st, ∅, v) = (Struct) v`).

**Lean evidence.** `Theory/Storage.lean` keeps the collapsing leaf
(`saveOnEmpty`, mirrored in `Theory/Rewrite.lean`) as the source of truth for
solkey; `docs/lean-key-rule-map.md` records the difference.

**Fix.** Revert to the collapsing leaf, or state the program on which the fold
is observable.

## 6. Sort-level and hygiene observations

None is wrong on the corpus; each matters for a future taclet.

- **The cast syntax `(S) t` is a no-op in solkey's taclets.** The Solidity DL
  grammar imports KeY's `cast_term` but `keyext.solidity.core`'s
  `ExpressionBuilder` has no `visitCast_term`, so a parenthesised cast is dropped
  and the rewrite executor inserts a `cast` only where the argument sort demands
  one. Three places still write the dropped form (`saveOnStoreCons`,
  `findDefinitionEmpty` and one `delAt` rule, `structRules.key:123,131,337`);
  the rules that need a cast write `cast<[S]>(t)` in full. Fix with a
  grammar-level visit or a lint.
- **`PathSVSort.createInstance` ignores the receiver's presets.** It builds
  `PathFilters` from scratch, so `StoragePath[memory]` is `Path[memory]` and
  `SimpleStoragePath[complex]` is `Path[complex]`. No corpus file parameterises a
  named variant. Refuse parameters on the named variants or seed the filters from
  them. (`Decode/Sorts.lean` of the `SolKey` reader mirrors the current
  behaviour.)
- **`SimpleExpressionSVSort` excludes contract fields** (`Literal |
  ProgramVariable` only; a state variable is a `FieldReference`), so
  `NonSimpleExpression` admits a bare storage root. The Lean rules treat a storage
  root as simple. Invisible today because every `SimpleExpression` position is
  value-typed; a real gap for a taclet with `SimpleExpression` in a storage
  position.
- **`ProgramVariableSVSort.createInstance` matches the joined parameter**:
  `Variable[storage,local]` is accepted and `Variable[local,storage]` is not,
  while `PathSVSort` accepts its flags in any order. Cosmetic.
- **`commuteSimpleUpdates`** (commented out in `updateRules.key`) is false as
  state equality on an assoc-list storage; it holds only pointwise. Keep it dead
  (`Semantics/Properties.lean`).
- **`requireSimple` states a branch in another form than its siblings.**
  `ifElseSplit` (`\find( ==> …)`) adds the condition to the antecedent on
  both goals (`\add(se = TRUE ==>)`, `\add(se = FALSE ==>)`); `assertSimple`
  (`\find(\modality…)`) does so on "Holds" only, its "Violated" goal being
  `\replacewith(se = TRUE)`; `requireSimple` writes each goal as a
  disjunction, `se = FALSE | ⟨…⟩post` and `se = TRUE | ⟨revert(); …⟩post`.
  The two agree on a `bool`, but the proof tree shows one idea in two shapes.
  Writing `requireSimple` as `ifElseSplit` is written, `"Holds": \add(se =
  TRUE ==>)` and `"Reverts": \add(se = FALSE ==>)`, is what Lean's
  `requireSimple` already states (a `.split` premise, as `ifElseSplit`'s).
- **`ifElseSplit`'s labels keep a stray `s`.** The labels are
  `"if s#se true"`/`"if s#se false"` (`solidityProgramRules.key`:5326, 5329),
  and `NodeInfo.setBranchLabel` replaces each `#\w+` by its instantiation, so
  the `s` of the program sigil `s#` stays: `if (b_1)` is labelled
  `"if sb_1 true"`. `"if #se true"` is what was meant. (The Solidity
  `Goal.setBranchLabel` is a TODO no-op today, `Goal.java`:280-282.) Lean's
  proof tree prints `if b_1 true`.
- **Overlapping taclets are separated by strategy cost, not by guards.** Lean's
  side conditions leave one rule per statement (`Rule.premise_unique`,
  `Calculus/Uniqueness.lean`); the cases where solkey leaves two taclets open
  (an unfold or capture against a terminal rule on a non-simple part, a
  conditional written to storage or memory, a copy between two storage members,
  a memory reference from a non-bindable source) are those its docstring lists.
  A test that exports each taclet's guard, or a hash of it, would catch an
  overlapping new taclet before it reaches a proof.

## 7. `send` (`b959555181`)

Lean ports `send_unfold_leftFstReceiver`, `send_unfold_rightSndArgument`,
`sendNoCallbackBox` and `sendNoCallbackDiamond` with solkey's shapes and
labels (`docs/lean-key-rule-map.md`, Payments), and proves them sound for an
interpreter whose `send` asks the transaction whether the recipient takes the
payment (`Semantics.sendAt`, `docs/solc-alignment.md`). Two observations:

- **The send diamond is sound where the transfer diamond is not.** On the
  EVM a refused `transfer` reverts, so `transferNoCallbackDiamond`'s one
  booking goal proves a payment terminates that the recipient (or the
  funds) may refuse; Lean has no diamond for `transfer`
  (`LeanTaclet.transferDiamond` closes it to `false`). A refused `send`
  returns `false`, which `sendNoCallbackDiamond`'s "send failed" goal covers,
  so its diamond needs no such assumption. If the transfer diamond is meant
  to assume a paying world, saying so next to the rule would keep it from
  being read as total correctness on the EVM.
- **"non-negative amount" is the only guard on the amount.** The box books
  `net(sadr) - se` for any `int` `se`, a negative amount crediting `sadr`;
  the EVM cannot send one. Lean's booking (`UpdElem.pay`) halts on a negative
  amount, so the box holds vacuously there; solkey's box proves the credit.
  Harmless for partial correctness, but a `0 <= se` assumption in the box
  (or a `uint`-sorted amount) would keep the two readings equal.

`(bool ok, ) = a.call{value: v}("")` lowered to a send ignores that solc
forwards all the gas there, so the callee may re-enter; under `noCallback`
that is solkey's stated choice, and the callback reading should treat the
lowered send as a point where control leaves. Lean's does (`ExecS`'s send
arms), and `sendWithCallbackBox` is ported as written, its three goals
`ProvesC.send`'s premises: sound for a reading in which every send may also
fail, whatever the world would say, since the callee may revert after
re-entering. One difference of form only: "send succeeded" is written
`{booking ‖ pv := true} {havoc} (I → …)`, as Lean writes the transfer's
resume, where KeY puts `pv := TRUE` into the anonymising update.

## 8. Returns and tuples (from the internal-call port)

- **Unconstrained returns.** `function g() returns (uint r) {}` followed by
  `assert(g() == 0)` holds in solc and is unprovable in KeY:
  `ExpandFunctionBody` declares `R ri;` with no value. Lean declares each
  return variable at its default (`CallRet.enter`).
- **Dropped tuple components (diamond).** `(uint x, ) = (1, arr[5]);` reverts
  in solc, but `ParserUtils.tupleAssignment` drops a component that is not a
  call, so `⟨…⟩ true` is provable. Category 4: keep the component (Lean
  evaluates it) or refuse.
- **Modifiers.** `InternalCall` refuses a callee with modifiers
  (`ExpandFunctionBody.asFunctionBody`), which leaves the call stuck; Lean
  inlines the modifiers around the body (`wrapMods`, first listed outermost).
- **`unfoldArgument` (item 3), partly resolved.** `ExpandFunctionBody` now
  binds each parameter to its argument as written (`T p = arg;`) and
  `InternalCall` matches `f(args);` / `lhs = f(args);` with any arguments, so a
  non-simple argument is no longer stuck. Lean still captures it first (`functionCallArgCapture`), for
  its separation condition (decision D3).

## 9. Loops (`ed7849d5b6`, past the pin)

- **Unwinding without a bound.** `whileUnwind` is sound (the loop and its
  unwinding run alike: Lean's `Stmt.loop_unwind_run`, from
  `Loop.run_unfold`), but the strategy applies it to every loop without a
  specification, so automatic proof search on a loop whose trip count is not
  a constant does not end. Lean bounds it by the loop's annotation
  (`/// @custom:key unwind k`, counted down by each unwinding, so the weight
  of `Calculus/Termination.lean` decreases) and closes the loop at the bound
  with a check, `loopExit`: "loop exited", the rest with the condition false
  assumed, and "unwound to the end", the condition false. Its soundness side
  condition is that the condition *returns* false (`Fml.eqD`, defined and
  equal), not only that it is not true: a condition that halts makes the
  loop halt, not exit. Suggested: an `unwind k` clause in `LoopSpecCompiler`
  and an exit taclet with these two goals, so that a bounded proof attempt
  ends in an open goal rather than running on.
- **`LoopLowering` skips a `try`.** With no enclosing loop
  (`flags == null`), `LoopLowering.lowerStatement` recurses only into a
  `Block` and a `ConditionStatement`; its `default` returns any other
  statement unchanged, a `TryStatement` included, and inside a loop a `try`
  with no jump is returned as is too.  So in
  `try … { while (c) { if (x) break; } } catch { }` the `break` reaches
  `whileUnwind` unlowered.  Lean's `lowerStmt` recurses into every clause of
  a `try` (and into `unchecked`) outside a loop, and through a `try` with no
  jump inside one (pinned in `Examples/Tactics/Loops.lean`).  Suggested:
  recurse into a `TryStatement`'s clauses, and any other statement holding
  blocks, with `flags == null`.
- **The exit is not an assertion.** Encoding the bound as `assert(!cond)`
  changes the program: it panics where the loop runs on, so the result is no
  longer an unwinding of the loop, and the bound reads as a failure of the
  contract. The bound belongs to the proof, as a goal.
- **Invariant rules ported (L4).** `whileInvariantBox` and
  `whileInvariantDiamond` are Lean's `LeanTaclet`s of those names, shape for
  shape, sound against `Loop.run` (`Calculus/SoundLoop.lean`). What Lean does
  differently, each a side condition KeY's types give for free:
  - *the cover.* Lean's locals are untyped, so `b` may be neither `TRUE` nor
    `FALSE`; under the diamond the premise also owes `b = TRUE ∨ b = FALSE`,
    as Lean's `ifElseSplit` does.
  - *the variant is read, not compared.* KeY's `dec = variant` is a total
    equation; Lean binds `variant := dec`, which under the diamond needs
    `dec` defined wherever the invariant holds (`n - i` with `i <= n` in the
    invariant). The checks `0 <= dec & dec < variant` after the body are
    KeY's, under `<b = cond;>(b = TRUE -> …)`, so the condition must also be
    defined after the body.
  - *the frame.* `{anon}` gives each local the body writes any binding, or
    none (`Fml.anon`), and anonymises storage and ledger together
    (`{havoc}`), where solkey anonymises storage for a non-local write and
    `net` for a call separately: Lean's is coarser where a body writes
    storage but pays nothing. A body that pushes, pops or rebinds an alias
    has no frame in Lean (`Prog.loopFrame` reuses `Stmt.within`), where
    solkey refuses only memory.
  - *the flags are typed by the invariant.* A loop's `brk`, `ret` and
    `first` are anonymised locals; the lowering conjoins `f || !f` (defined
    exactly when `f` is a `bool`) to an invariant for each flag the
    condition reads. KeY's `boolean` type says this.
  - *a loop with an invariant and no frame, or no variant under the
    diamond,* closes to `false` (`whileClose`, `whileNoVariantDiamond`),
    where solkey unwinds it: in Lean the annotation chooses the rule.

## Resolved (kept for orientation)

Each was found by the Lean side and is fixed in solkey; git has the details.

- Evaluation order of the `*NonSimpleIndexCapture` taclets: `8ba30fd742`
  (storage), `63c38cfaf6` (memory, recursion). The freeze applies to primitive
  sources only; a struct source is target-first in solc, which is the Lean
  interpreter's open gap (`Counterexamples/RefSourceOrder`, removed with the
  untyped layer).
- Delete-family generic overlap (`delValueDefault` at `alphaSt := Struct`):
  `e67a0d7c48`; `delValueStValueCast` closes delete-then-copy (`444f029579`).
- Array and mapping sorts now `\extends Struct` in `SolJSONParser`, so the two
  `SortFaithfulness` findings are closed.
- `selectOnSaveEmpty` rewriting to an unbound `flds`, and the reflexive last two
  conjuncts of `copyKeepsMapping.key`: `c80a54494c`, and the `copyAt` fold that
  followed.
- Memory compound assignment, the `if` simplifiers (`ifTrue`, `ifElseTrue`,
  `ifElseNegated`), and `BoolLiteral.equals`/`hashCode`: `444f029579`.
- Balance-checked `transfer`: `transferNoCallbackDiamond` and the callback
  diamond owe `0 <= se & se <= selfBalance`; the boxes book unconditionally,
  which is sound for partial correctness (`333cc7b353`).  Then `100f7f24c3`
  removed `selfBalance` from every transfer rule (no debit, no
  `selfBalanceSk` after a callback), added the `\if(sadr = self)` booking, and
  left the diamonds owing `0 <= se` only; Lean has no diamond rule for a
  payment (`LeanTaclet.transferDiamond`), and its callback leaves the funds as
  they were (`State.havoc`).  `0b885c229d` dropped the last `selfBalanceSk`:
  `tryCallWithCallbackBox`'s "call succeeded" no longer havocs `selfBalance`,
  which is what `State.havoc` does (storage and ledger only).
- The four `*IndexedReceiver_unfold_leftFst` taclets that did not fire (a null
  proposal in `VariableNamer`).
- Determinism under the block modality: no box/diamond twin pairs remain.
- `sizeNotNegative` (`8a977688dc`) covers `size >= 0`; the rest is item 2.
