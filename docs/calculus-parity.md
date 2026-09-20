# Calculus parity: what `Calculus/Rules.lean` alone proves of `TestSuite.sol`

Can solkey's taclet suite be proved by the rule table, with no weakest
precondition?

## Why `docs/solkey-parity.md` does not already answer this

That file reports 325 of 416 obligations proved by `sol_wp`. But `sol_wp`
(`Wp/Verifier.lean`) is symbolic execution *by the interpreter*; it never
reads `Calculus/Rules.lean`. So it says the interpreter agrees with solkey, and says
nothing about the calculus — which is the artefact solkey's taclets
correspond to. The two corpora are generated from one pass of
`scripts/solkey-port.mjs` so they cannot drift, and this is the other half.

## What a row here claims

A `proved` row is one `sol_calculus` (`Examples/Common.lean`):

```
sol_calculus solkey_TestSuite_storageRootReadWrite from State.testSuiteStore
  { age = 34; uint r = age; assert((r == 34)) }
```

which states `CalculusHolds` (`Update/Step.lean`) — there is a frontier `f`
with

- `[⟹ ⟨program⟩true] ⇝ᵘ* f`, every step a pinned taclet application chosen
  by `UniquenessAux.candidate` and proved to apply by `find_pinned_step`;
- `Frontier.isClosed f`, so no line has a statement left. This is the
  conjunct that makes it a claim: `⇝ᵘ*` is reflexive, and without it the
  start frontier is its own witness;
- `f.Holds State.testSuiteStore`.

What is left at the end is first-order: the accumulated update applied to the
store, plus one obligation line per `assert`, because `Rules.assertGoals`
leaves the violated branch as an obligation rather than a revert. That is
KeY's own proof shape.

## Result

| | obligations | proved | open | unsupported |
|---|---:|---:|---:|---:|
| `TestSuite.sol` | 278 | **201** | 44 | 33 |

**201 of the 245 obligations that are expressible in this fragment are proved
from the rule table alone**, against 225 for `sol_wp` on the same 245. So the
answer to the question is *no, not all of them* — and the 44 that fail split
into three groups, two of which are not gaps at all.

## Where the rules stop

The 44 open rows, by cause.

| group | rows | is it a gap in the calculus? |
|---|---:|---|
| the proof-level split | 9 | no — by design, KeY stops here too |
| `binopUnfold{Left,Right}` share a scratch name | 5 | **yes, a defect** |
| closed frontier, endpoint false, not yet diagnosed | 27 | unknown |
| the porter emits something the grammar rejects | 2 | no — open on the `sol_wp` side too |
| `testDeepPopDoesNotResetMappingMember` stuck at step 6 | 1 | unknown |

### 1. The proof-level split — 9 rows, by design

`ifUnfold`, `ifElseUnfold`, `ifSplit`, `ifElseSplit`, `ifElseNegated`,
`logicalAndShortCircuitRhs`, `logicalOrShortCircuitRhs`, `ternaryToIf`,
`ternaryCaptureCond`.

`ifElseUnfold` hoists a complex condition into `pv@bool`, and the resulting
`if (pv@bool) …` matches **no rewrite rule, deliberately**. KeY stops in the
same place: its program rules end and the sequent rule `ifthenelse_split`
takes over. The Lean counterpart is `SolidityJudgment.ite_split`
(`Examples/Derivations/DynamicLogic.lean`), which is a theorem and not a
`RuleName`, so `seq_closes` reports `stuck` and is right to.

Closing these needs a frontier-level case split, not a rule.

The two ternary rows reach the same place by a longer road, and getting them
there fixed a real gap: `SoliditySyntax.ternaryExpr` was missing from the
`attribute [reducible]` and `[rule_simp_set]` lists of `Examples/Common.lean`
while `binopExpr`, `unopExpr` and `incDecExpr` were all present, so the
`Decidable` instance for the ternary condition could not be synthesised and
the derivation died before it started. `.claude/rules/rule-table.md` names
this trap exactly — "a new `*Effect` builder has to be declared twice more" —
and the symptom is as advertised: a failure with no hint that a list is where
to look. With the registration in place `ternaryToIf` fires and the chain
stops at `if (b) …`, a symbolic condition, which is §1's stop.

### 2. A real defect in the rule table — 5 rows

`additionBothStorage`, `additionBothOperandsImpure`,
`additionLeftImpureRightReadFirst`, `subtractionLeftImpureRightReadFirst`,
`lessThanLeftImpureRightReadFirst` — every obligation whose binary operation
has **two** nonsimple operands, and no other.

`binopUnfoldLeft` and `binopUnfoldRight` both bind the single scratch name
`pv`, so the second capture takes the first, and the operation is computed
from the right operand twice.
`Counterexamples/BinopOperandCapture.lean` pins it: the rule table proves
`r == 10` of a program that computes `10 + 5`, and the interpreter refutes
it.

KeY does not have this. `lessThanCaptureLhs` takes a `SimpleExpression` on
the right — so the Rhs rule goes first — and introduces **two** `\new`
variables, `pv1` and `pv2`, in one step. Either difference alone would
prevent it.

This is the finding the exercise was worth. `sol_wp` proves all five of these
programs and cannot see the defect, because it never reads the rule table.

### 3. Closed frontier, endpoint false — 27 rows, not yet diagnosed

The rules drove these to closure and the frontier reached does not hold at
the store. That is the *same signature* as §2, so the natural guess is more
scratch-name reuse — 15 of the 27 are solkey's `*Impure{Receiver,Index}`
group, where a receiver and an index are captured in the same statement, and
the capture rules draw their alias names from the same fixed table
(`Rules.storagePathAliasName`, `indexAliasName`, `valueAliasName`).

That is a guess, and it is recorded as one. Each row needs the treatment §2
got — a trace, a minimal program, and a counterexample — before anything is
claimed about it. They are:

- receiver/index capture (15): `storageFieldWrite{RefSource,StorageRef,RootRef}ImpureReceiver`,
  `storageIndexWrite{RootRef,StorageRef}ImpureReceiver`,
  `memoryToStorageIndexImpureReceiver`, `indexWriteBothImpure{StorageRef,MemToStorage}`,
  `testNestedIndex{Read,Write}Impure*` (four),
  `test{Storage{Delete,Push},CompoundAssign}ImpureReceiver`;
- push, pop and alias binding (6): `storageLocalDeclSkip`, `storagePushLocalBind`,
  `testStoragePush{ReturnAlias,FieldLvalue}`,
  `testStorageComplexReceiverPushFieldLvalue`, `storageIndexDeleteMappingStruct`;
- memory and cross-domain (4): `memoryDeepField`,
  `memoryField{AddAssign,Preincrement}Unfold`,
  `testMemoryToStorageCopyComplexSource`;
- the two `sol_wp` also leaves open (2): `testStorageMapStructCopy`,
  `storageMatrixNseIndex`.

### 4. The remainder — 3 rows

`storageIndexCopysourceAfterPush` and `testStorageNestedPushReturnAlias` fail
identically on both sides: the porter emits something the grammar does not
accept, so neither corpus has a proof of them.

`testDeepPopDoesNotResetMappingMember` goes stuck after six steps, with no
candidate rule for the statement it reaches. It is open on the `sol_wp` side
too.

## What this does *not* establish

Two limits, both deliberate and both worth knowing before quoting the number.

1. **`CalculusHolds` does not imply `SolidityJudgment.Holds`.** That needs
   `FrontierStep a b → (a.Holds s ↔ b.Holds s)`, which needs the per-rule
   bridges of `Update/TacletTable.lean` — 21 of the 83 rules with an update —
   and `Rules.assertGoals` is deliberately not exhaustive
   (`Update/Wp.lean`). The two corpora are proved of the same programs side
   by side instead of one being derived from the other.
2. **The endpoint is `native_decide`.** `Frontier.Holds` runs the accumulated
   update through the interpreter's readers, and the WF-recursive interpreter
   does not kernel-reduce, so `decide` fails on it — the same reason
   `Examples/Derivations/Paper.lean` checks its chains' endpoints that way.
   The *derivation* adds no axiom; the endpoint adds `Lean.ofReduceBool` and
   `Lean.trustCompiler`. So the symbolic execution is by the rules and the
   arithmetic at the end is by the interpreter, which is exactly the division
   §1 has not yet closed.

## Reproducing

```bash
node scripts/solkey-port.mjs                   # regenerate both corpora
./scripts/check-calculus-parity.sh             # vs expected-calculus.tsv
./scripts/check-calculus-parity.sh --update    # re-pin it
```

The corpus is `Solidity/Examples/Derivations/Solkey/TestSuite/PartNN.lean`,
its own Lake target (`SolidityCalculus`), split into parts only so the parts
elaborate concurrently — one module of a whole contract is a single-threaded
run of tens of thousands of pinned taclet applications. Extend it to another
contract by adding a name to `CALCULUS_CONTRACTS` in the porter.
