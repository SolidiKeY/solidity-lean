# Improvement ideas flowing Lean → solkey

The only outbound document: what the Lean model shows solkey
(<https://github.com/SolidiKeY/solkey>) could gain or should tighten. The
reverse direction, solkey rules the Lean calculus lacks, is the `planned`
rows of `docs/lean-key-rule-map.md`.

**Checked against solkey `473da8944c`**, the frozen snapshot in
`tests/migration/solkey` (`docs/solkey-migration.md`). On a re-pin, re-check
each item against the new snapshot and move what upstream fixed to
"Resolved".

Items are ranked: those that let KeY close a goal false on the chain first,
then missing rules, refusals, simplifications and hygiene. They are numbered
for citation (code and other docs cite "item 9", "§10"); a resolved item
keeps its number.

## 1. Checked arithmetic (can close a false goal)

**Problem.** Solidity ≥ 0.8 reverts when `+`, `-`, `*`, unary `-` and the
compound forms leave the type's range. solkey's arithmetic taclets compute in
unbounded `int`, so a postcondition proved in KeY can be false on the chain
when a value wraps and the transaction reverts (upstream's own
`unprovable/Unprovable.sol` says so; seven of its boxes are valid in Lean,
which reverts before the `assert(false)`).

The same choice reaches the specifications: a clause's `+`/`-` is checked in
Lean and unbounded in solkey. solkey now assumes `x >= 0` for a `uint`
parameter (`SolidityProblemSynthesizer.parameterFacts`) but no upper bound;
Lean's obligation assumes `0 <= x <= 2^256 - 1` (`rangeFml`,
`Calculus/SurfaceSpec.lean`).

**Lean evidence.** `BinOp.evalT`, range-checked by `PrimTy.ofInt?`
(`Semantics/Ops.lean`); the EVM compiler proves the guard (`tail_simT`,
`Evm/SimLemmas.lean`; `overflow_run`, `Evm/Examples.lean`).

**Fix.** Split each arithmetic taclet on the range (revert branch under
`\diamond`, closed branch under `\box`, as Java KeY's `inInt`/`expandInInt`),
or give `uint` its range as an axiom every update re-establishes; add the
upper bound to `parameterFacts`.

## 2. A `wellFormed(storage)`: resolved (`048a74de51`)

See "Resolved". What it left (a `uint` cell in range) is item 1's.

## 3. `unfoldArgument`: resolved (`671f6762a9`)

See "Resolved". The remaining difference in shape is recorded in
`docs/lean-key-rule-map.md` (`functionCallArgCapture`).

## 4. What solkey should refuse or leave stuck

The Lean syntax cannot write the programs below (the right column is the
constraint that excludes it). solkey is sound on them if it refuses them or
has no taclet for them; where it has a taclet, the taclet must agree with
solc. Only the first two rows are checked rejected in solkey
(`MAPPING_COPY_ERROR`, `MEMORY_MAPPING_ERROR` in `ParserUtils.java`).

| solkey should refuse | Lean |
|---|---|
| a call whose argument reads an earlier parameter (sequential binding differs from solc) | `Args.separated` (`Syntax/Elab/Context.lean`, an elaboration error) |
| `delete` of a mapping or through a storage alias | `Stmt.delete` takes a `Loc` |
| `push`/`pop` on a memory or fixed-size array | `Stmt.push`/`pop` at `.array` |
| a storage reference copied into a memory member or element | `MSrc` has no copy form |
| a default (`push()`, `T memory m;`, `delete m`) of a type whose default is ill-formed | `defaultOkS` |
| `new` of anything but a dynamic array of mapping-free elements | `RefTy.newArrOk` |
| `op=`, `++`, `--` on a `bool` | `PrimTy.isNumeric` |
| effects inside a value (`++` under `&&`/`||`, in a conditional branch); a conditional of reference type | `Val` has no effect; the elaborator hoists the rest |
| recursion; a call inside an expression | the elaborator; `Arg`, `CallRet` |

A program no taclet matches stays stuck, which is safe. Rules whose premise
differs from their taclet's without changing the syntax are in
`docs/lean-key-rule-map.md`.

## 5. The `save` leaf should collapse

**Problem.** `save(st, nil, v)` is a leaf every write leaves, read through by
member sort by `saveOnEmptyPrim` and the `selectOnSaveEmpty*` taclets
(`structRules.key`), so that a struct written over a location keeps the
location's mapping members. That is the one case neither side reaches: a
storage-to-storage copy of a mapping-carrying type is rejected by solc ≥ 0.7
and by `ParserUtils.parseAssignmentMaybe`, and Lean cannot build it
(`Src.copy`'s `mapFree`). The lazy leaf costs a term that grows with every
write and several taclets where the signature needs one,
`save(st, ∅, v) = (Struct) v`.

**Lean evidence.** The typed Theory has no leaf: a copy is one `save` of the
new value laid over the old one, computed from the type (`Obs.copyTo`,
`TVal.overlay`, `Theory/Typed/Obs.lean`).

**Fix.** Revert to the collapsing leaf, or state the program on which the
fold is observable.

## 6. Sort-level and hygiene observations

None is wrong on the corpus; each matters for a future taclet.

- **The cast syntax `(S) t` is a no-op in solkey's taclets.** The grammar
  imports KeY's `cast_term`, but `keyext.solidity.core`'s `ExpressionBuilder`
  has no `visitCast_term`, so a parenthesised cast is dropped. Still written
  in `saveOnStoreCons` and `findDefinitionEmpty` (`structRules.key`); the
  rules that need a cast write `cast<[S]>(t)`. Fix with a grammar-level visit
  or a lint.
- **`PathSVSort.createInstance` ignores the receiver's presets**: it builds
  `PathFilters` from scratch, so `StoragePath[memory]` is `Path[memory]`.
  Refuse parameters on the named variants or seed the filters from them.
- **`SimpleExpressionSVSort` excludes contract fields** (`Literal |
  ProgramVariable` only), so `NonSimpleExpression` admits a bare storage
  root; the Lean rules treat a root as simple. A real gap for a taclet with
  `SimpleExpression` in a storage position.
- **`ProgramVariableSVSort.createInstance` matches the joined parameter**:
  `Variable[storage,local]` is accepted, `Variable[local,storage]` is not,
  while `PathSVSort` accepts its flags in any order. Cosmetic.
- **`commuteSimpleUpdates`** (commented out in `updateRules.key`) is false as
  state equality on an assoc-list storage; it holds only pointwise. Keep it
  dead.
- **`requireSimple` states a branch in another form than its siblings**:
  `se = FALSE | ⟨…⟩post` and `se = TRUE | ⟨revert(); …⟩post`, where
  `ifElseSplit` adds the condition to the antecedent (`\add(se = TRUE ==>)`).
  The two agree on a `bool`, but the proof tree shows one idea in two shapes;
  Lean's `requireSimple` is written as `ifElseSplit` is.
- **`ifElseSplit`'s labels keep a stray `s`.** `"if s#se true"`
  (`solidityProgramRules.key`) and `NodeInfo.setBranchLabel` replaces only
  `#\w+`, so `if (b_1)` is labelled `"if sb_1 true"`; `"if #se true"` was
  meant (`Goal.setBranchLabel` is still a TODO no-op). Lean's proof tree
  prints `if b_1 true`.
- **Overlapping taclets are separated by strategy cost, not by guards.**
  Lean's side conditions leave one rule per statement (`Rule.premise_unique`,
  `Calculus/Taclet.lean`). A test that exports each taclet's guard would
  catch an overlapping new taclet before it reaches a proof.

## 7. `send`

Lean ports the `send` taclets with solkey's shapes and labels
(`docs/lean-key-rule-map.md`, Payments), sound for an interpreter whose
`send` asks the transaction whether the recipient takes the payment
(`TRun.send`). Two observations:

- **The send diamond is sound where the transfer diamond is not.** On the
  EVM a refused `transfer` reverts, so `transferNoCallbackDiamond`'s booking
  goal proves termination of a payment the recipient may refuse; Lean has no
  diamond for `transfer` (`LeanTaclet.transferDiamond` closes it to `false`).
  A refused `send` returns `false`, which "send failed" covers. If the
  transfer diamond assumes a paying world, say so next to the rule.
- **The box books any amount.** `sendNoCallbackBox` books `net(sadr) - se`
  for any `int` `se`, a negative amount crediting `sadr`; Lean's booking
  (`UpdElem.pay`) halts on one. A `0 <= se` assumption in the box would keep
  the two readings equal.

`(bool ok, ) = a.call{value: v}("")` lowered to a send ignores that solc
forwards all the gas, so the callee may re-enter; the callback reading
should treat it as a point where control leaves, as Lean's does
(`ProvesC.send`).

## 8. Tuples

- **Dropped tuple components (diamond).** `(uint x, ) = (1, arr[5]);`
  reverts in solc, but `ParserUtils.tupleAssignment` drops a component that
  is not a call, so `⟨…⟩ true` is provable. Keep the component (Lean
  evaluates it) or refuse.

## 9. Constructors

- **The precondition is read before `storage := mtSt`.** A constructor's
  `requires` and the `msgSender != self` fact are outside the update, so a
  `requires` that reads state talks about a storage the deployment
  discards. Refuse it, as Lean does (a constructor `requires` that reads a
  state variable, `net(…)` or `this.balance`).
- **Initializers without a constructor are never checked.** A contract with
  `uint x = 5;` and no `constructor` gets no obligation. Suggest
  synthesizing `constructor()` when a contract has initializers.
- **Immutables are storage fields**, so an `immutable` is unconstrained in a
  function's obligation. Suggest a field the invariant fixes after
  deployment.
- **The unspecified obligation does not set `selfBalance`** and books no
  payment: `{storage := … || net := mtSt}`, where the specified one writes
  `net := storeSt(mtSt, at(msgSender), msgValue)` and
  `selfBalance := msgValue`. Lean states both with the specified one's
  update (`Problem.deployUpd`).
- **`selfBalance := msgValue` ignores a pre-funded address**
  (`docs/solc-alignment.md`, "Constructors"). Lean follows solkey.

## 10. Loops

- **Unwinding without a bound.** `whileUnwind` is sound, but the strategy
  applies it to every loop without a specification, so automatic search on a
  loop whose trip count is not a constant does not end. Lean bounds it by the
  annotation (`/// @custom:key unwind k`) and closes the loop at the bound
  with `loopExit`: "loop exited" (the rest, the condition false assumed) and
  "unwound to the end" (the condition false). The side condition is that the
  condition *returns* false (`{ b := cond } (b = FALSE)` under the diamond),
  not only that it is not true. Suggested: an `unwind k` clause in
  `LoopSpecCompiler` and an exit taclet with these two goals.
- **The exit is not an assertion.** Encoding the bound as `assert(!cond)`
  changes the program: it panics where the loop runs on. The bound belongs to
  the proof, as a goal.
- **`LoopLowering` skips a `try`.** With no enclosing loop (`flags == null`)
  `lowerStatement` recurses only into a `Block` and a `ConditionStatement`,
  so in `try … { while (c) { if (x) break; } } catch { }` the `break` reaches
  `whileUnwind` unlowered. Lean's `lowerStmt` recurses into every clause of a
  `try` (pinned in `Examples/Tactics/Loops.lean`). Suggested: recurse into a
  `TryStatement`'s clauses, and any statement holding blocks, with
  `flags == null`.

How Lean's invariant rules differ from `whileInvariantBox`/`Diamond` (frame,
variant, flags) is `docs/loops.md`'s.

## Resolved

Found by the Lean side and fixed in solkey; git has the details.

- `wellFormed(storage)` (item 2): the `wf`/`selectOnShape*`/`fixed*` theory
  (`048a74de51`) and the `wellformed(storage)` premise of the synthesized
  obligation; Lean's typed `Storage C` subsumes it.
- `unfoldArgument` (item 3): `InternalCall` takes any arguments and
  `ExpandFunctionBody` binds each (`671f6762a9`).
- Returns: every return variable, `address` included, starts at its default
  (`ParserUtils.defaultValue`); modifiers are inlined (`ModifierInlining`).
- Constants: `SolJSONParser` inlines a `constant`'s value.
- Evaluation order of the `*NonSimpleIndexCapture` taclets: `8ba30fd742`,
  `63c38cfaf6`.
- Delete-family generic overlap (`delValueDefault` at `alphaSt := Struct`):
  `e67a0d7c48`, `444f029579`.
- Array and mapping sorts `\extends Struct` in `SolJSONParser` (the two
  `SortFaithfulness` findings).
- `selectOnSaveEmpty` rewriting to an unbound `flds`; `copyKeepsMapping.key`'s
  reflexive conjuncts: `c80a54494c`.
- Memory compound assignment, the `if` simplifiers, `BoolLiteral.equals`:
  `444f029579`.
- Balance-checked `transfer` and `selfBalance` after a callback: `333cc7b353`,
  `100f7f24c3`, `0b885c229d`.
- The four `*IndexedReceiver_unfold_leftFst` taclets that did not fire.
- Determinism under the block modality: no box/diamond twin pairs remain.
