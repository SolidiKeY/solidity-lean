# The hypotheses of the unfold-rule soundness theorems

`#soundness_ledger` in `Solidity/Calculus/SoundnessLedger.lean` is the
count: which `<rule>_sound` carries which hypothesis beyond `hcond`/`hfresh`,
which rules have no theorem, and which depend on a `sorry`. It is pinned by
`#guard_msgs`, so this file holds no numbers. What it does hold, one section
per family of hypotheses, is:

- **Says**: the hypothesis, in one line.
- **Kind**: its `hypKind` in the ledger.
- **Enters at**: the shared lemma it comes in through. Removing it there is
  what frees the rules.
- **Frees it**: what would have to change.
- **Attempts**: dated, with the approach and where it stuck (the goal, or
  the lemma that was missing). Record a failed attempt too. That record is
  what keeps the next session from repeating it.

The loop that works through these sections is
`.claude/skills/discharge-hypothesis/SKILL.md`.

## Target pre-resolves: `hlhs`, `hplhs`

- **Says**: `resolveLoc s lhs.expr = .ok (s, loc)` and `pureExpr lhs.expr`.
  The assignment target resolves, without effects, in the initial state.
- **Kind**: residue. The `RuleSoundness` docstring says these residuals
  hoist a right-hand side that the interpreter evaluates first anyway. No
  evaluation order is swapped.
- **Enters at**: `locAfter{Eval,SVal,MVal}_of_pure`,
  `execAssign*_storageRhsErr`, `execAssign_memoryRhsErr`.
- **Frees it**: a congruence lemma that relates target resolution before and
  after the right-hand side is evaluated. The error branch
  (`resolveLoc s lhs.expr = .error _`) has to be proved separately.
- **Attempts**: none recorded.

## Reference source ahead of the interpreter: `hprim`

- **Says**: `rhs.ty.isPrimitive = true`.
- **Kind**: semantic, refuted by `RefSourceOrder.refSource_disagrees`.
- **Frees it**: an interpreter change, not a proof. `execAssignNested` is
  value-first for every source, but the EVM is target-first for reference
  sources. Once assignment is target-first for those, `hprim` can go. See
  `docs/solc-alignment.md` § "Known divergence".
- **Attempts**: none. This one waits on the interpreter.

## The mapping guard: `hnm`

- **Says**: `tyHasMapping rhs.ty = false`.
- **Kind**: semantic, refuted by `MappingSideConditions.m3_refutes` (a
  pure path) and `m4_refutes` (a simple index).
- **Frees it**: narrowing `isSimple` to KeY's `SimpleExpression` (a stack
  variable or a literal).
- **Attempts**: in the four `execAssign*_storageRhsErr` helpers it was
  weakened to `hsafe : tyHasMapping rhs.ty = true -> err = Halt.stuck`. A
  rule on a `SimpleExpression` path discharges that
  (`resolveS_simple_err_stuck`), which is why
  `storageFieldReadUnfoldRightSndResult` no longer carries `hnm`.

## Unfrozen reference sources: `hev`, `hstable`, `hstableI`, `hold`, `hstableOld`

- **Says**: the right-hand side succeeds (`rhsToSVal s rhs = .ok (s, sv)`),
  and it gives the same value after the target path is resolved.
- **Kind**: unclassified. `freezeRhs` freezes only primitives, so the `*Ref*`
  rules alias the source instead of reading it. `ErrorOrder.unfrozen_not_sound`
  shows that an *unfrozen* residual is wrong on a value source. There is no
  refutation for a reference source yet.
- **Enters at**: `fieldWriteResolve{Storage,Memory}_ref_sound`,
  `indexWriteResolve{Storage,Memory}_ref_sound`,
  `indexWriteTailPlain[Memory]_ref_agree`.
- **Frees it**: first settle whether it is semantic. Try the
  `people[1 / 0].age = ghost` shape of `ErrorOrder` with a reference-typed
  `ghost`. If that refutes it, add the refutation and mark it `semantic`.
- **Attempts**: gone for value sources. `freezeRhs` binds the value before
  any target capture, so the `*WriteUnfoldLeft*` family no longer carries
  them.

## Typing-shaped: `hnsl`, `hnmr`, `hnst`, `hkp`, `hkpm`, `hml`, `hwf`, `htye`, `htyE`, `hasgn`, `hkm`, `horig`, `hself`

- **Says**: facts the surface language guarantees but the untyped statement
  model does not. Examples: the target's location shape matches its kind
  (`loc ≠ Loc.storageLocal _`), a memory path has memory kind, a ternary's
  arms have one type, a declaration's initializer does not mention the name
  it declares.
- **Kind**: typing.
- **Frees it**: one well-typedness premise from `Typing/**` in place of the
  group, plus one lemma per hypothesis that derives it from that premise.
  That trades many hypotheses for one that the calculus can justify.
  `RuleStep.complete_of_wellTyped` in `Calculus/Coverage.lean` already takes
  that shape of premise.
- **Attempts**: none recorded.

## Sub-expression purity: `hppath`, `hpidx`, `hpi`, `hprhs`, `hpr`, `hpure`, `hpamt`, `hpt`, `hptgt`

- **Says**: `pureExpr` of a path, index or operand.
- **Kind**: unclassified. For write rules, an impure path is fine
  (`EvaluationOrder`). For read rules and operands, nobody has checked.
- **Attempts**: none recorded.

## Operand pre-evaluates: `hlv`, `hrb`, `hrec`, `hbase`, `harr`, `hevalEq`, `hcap`

- **Says**: an operand or path evaluates, in the initial state, to a named
  value. The residual re-reads it after a capture.
- **Kind**: unclassified. The docstring says the operand must not depend on
  the capture's effects. Whether that is semantic has not been checked.
- **Enters at**: `hbase` through `resolveS_transport`,
  `rhsToSVal_transport{Ok,Err}`, `rhsToMVal_transportOk`,
  `resolveLoc_transport`.
- **Attempts**: none recorded.

## Case restrictions: `hnp`, `hprimF`

- **Says**: the source is *not* primitive. These are the complements of
  `hprim` on the rules that split on it.
- **Kind**: unclassified.
- **Attempts**: none recorded.

## No theorem, or a `sorry`

- The four memory `*OpAssignUnfoldLeftFst`/`*IncrementUnfoldLeftFst` rules
  have no `_sound` theorem.
- `functionCallArgCapture_sound_inlined` (`hcallee`) and the non-stack branch
  of `storagePushValueUnfoldRightSndArgument_sound`: the plan for each is
  documented at its site.
