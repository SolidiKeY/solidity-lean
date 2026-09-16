import Solidity.Uniqueness
import Solidity.TypeSoundness

/-!
# Coverage: every well-typed statement is claimed by a rule of the calculus or is
explicitly listed residue

`Uniqueness.applicable_eq_candidate` proves the *converse* discipline of
the dispatch function: whenever a rule of the calculus applies, `candidate` names
exactly that rule.  This module supplies the missing forward half and
turns Progress.lean's informal residue claim into a theorem:

* `candidate_applies`: whenever `UniquenessAux.candidate` answers
  `some rule`, that rule is a rule of the calculus whose mode gate and condition
  really hold — so `candidate` never bluffs (on the `pushRhsStorageB`
  fragment; see the caveat below).
* `ResidueShape`: an explicit, human-readable, mode-independent syntactic
  characterization of the statements no rule of the calculus covers, one documented
  constructor per residue family (symbolic `if`, the storage/stack↔memory
  copy holes, `**=`, a memory *root* compound assignment — a root binds an
  identity, not a value cell — …).  Memory *field* and *index* arithmetic
  used to be residue too; it is covered since the memory-target arithmetic
  family was ported (`Rules.memory{Field,Index}CompoundAssign`).
* `coverage_residue`: every `stmtWt`-well-typed statement is either
  covered (`Rules.ruleApplies`) or has a `ResidueShape`; with
  `residue_not_covered` the two cases are exclusive
  (`not_covered_iff_residue`).  This is the rule-independent fragment
  the completeness theorem `RuleStep.complete_of_wellTyped` (at the end
  of this file) is stated over: well-typed and not listed residue.  The
  calculus has no catch-all tier; a residue statement is simply stuck
  (`Progress.lean`).

## The `pushRhsStorageB` caveat

`candidate`'s docstring warns that its value is unconstrained where no
rule applies, and there is exactly one place where it exercises that
freedom: an assignment whose right-hand side is a `pushPlace` with a
*non-storage* inner target (`x = mv.push()` for a memory array `mv`).
There `candidate` answers `some storageLocalRootPushBind`/
`…UnfoldLeftFstReceiver` although those rules require a storage-kind
receiver, so the statement is uncovered residue with a non-`none`
candidate.  `stmtWt` admits the shape (`wtExpr` checks only the array
type of a push receiver), so it cannot be typed away.  Consequently
`candidate_applies` and the `candidate`-vs-coverage equivalences carry
the syntactic side condition `pushRhsStorageB stmt = true`, the residue
gets its own honest constructor (`assignPushRhsNonStorage`), and the
headline `coverage_residue` — which never mentions `candidate` — needs
no side condition at all.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Solidity
namespace Coverage

open Rules
open UniquenessAux

/-! ## Boolean bridges (converses of the Uniqueness.lean helpers) -/

theorem and_true_of {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by simp [ha, hb]

theorem simple_of_not_complex {e : WrappedExpr} (h : ¬ e.complex = true) :
    e.simple = true := by
  cases hs : e.simple with
  | true => rfl
  | false => exact absurd (by simp [Typed.WrappedExpr.complex, hs]) h

theorem complex_of_not_simple {e : WrappedExpr} (h : ¬ e.simple = true) :
    e.complex = true := by
  cases hs : e.simple with
  | true => exact absurd hs h
  | false => simp [Typed.WrappedExpr.complex, hs]

theorem complex_eq_false_of_simple {e : WrappedExpr} (h : e.simple = true) :
    e.complex = false := by
  simp [Typed.WrappedExpr.complex, h]

theorem isArray_of_arrayTyB {e : WrappedExpr} (h : arrayTyB e = true) :
    Rules.isArray e := by
  unfold arrayTyB at h
  split at h
  · next elem hty => exact ⟨_, hty⟩
  · exact Bool.noConfusion h

theorem isMapping_of_mappingTyB {e : WrappedExpr} (h : mappingTyB e = true) :
    Rules.isMapping e := by
  unfold mappingTyB at h
  split at h
  · next key value hty => exact ⟨_, _, hty⟩
  · exact Bool.noConfusion h

/-- Every expression kind is storage, memory, or stack. -/
theorem kind_trichotomy (e : WrappedExpr) :
    e.isStorage = true ∨ e.isMemory = true ∨ e.isStack = true := by
  unfold Typed.WrappedExpr.isStorage Typed.WrappedExpr.isMemory
    Typed.WrappedExpr.isStack
  cases e.kind <;> simp

theorem field_prim_or_identity (f : Field) :
    f.isPrimitive = true ∨ f.isIdentity = true := by
  cases hp : f.isPrimitive with
  | true => exact Or.inl rfl
  | false => exact Or.inr (by simp [Field.isIdentity, hp])

theorem ty_prim_or_ref (ty : Ty) :
    ty.isPrimitive = true ∨ ty.isReference = true := by
  cases hp : ty.isPrimitive with
  | true => exact Or.inl rfl
  | false => exact Or.inr (by simp [Ty.isReference, hp])

/-! ## Membership of the parameterized rule families

`ruleNames` lists every instance of an op-indexed family, so
membership of the family under a variable op is a finite case split.
`simp [ruleNames]` exceeds the recursion limit; `decide` is the
repo-wide idiom. -/

theorem mem_binopUnfoldLeft (op : BinOp) :
    RuleName.binopUnfoldLeft op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_binopUnfoldRight (op : BinOp) :
    RuleName.binopUnfoldRight op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_binopUnfoldResult (op : BinOp) :
    RuleName.binopUnfoldResult op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_binopAssignment (op : BinOp) :
    RuleName.binopAssignment op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_unopCapture (op : UnOp) :
    RuleName.unopCapture op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_unopAssignment (op : UnOp) :
    RuleName.unopAssignment op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageRootCompoundAssign (op : BinOp) :
    RuleName.storageRootCompoundAssign op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageFieldCompoundAssign (op : BinOp) :
    RuleName.storageFieldCompoundAssign op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageIndexCompoundAssign (op : BinOp) :
    RuleName.storageIndexCompoundAssign op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageFieldCompoundAssignUnfoldLeftFst (op : BinOp) :
    RuleName.storageFieldCompoundAssignUnfoldLeftFst op ∈
      Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageIndexCompoundAssignUnfoldLeftFst (op : BinOp) :
    RuleName.storageIndexCompoundAssignUnfoldLeftFst op ∈
      Rules.ruleNames := by
  cases op <;> decide

theorem mem_memoryFieldCompoundAssign (op : BinOp) :
    RuleName.memoryFieldCompoundAssign op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_memoryIndexCompoundAssign (op : BinOp) :
    RuleName.memoryIndexCompoundAssign op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_memoryFieldCompoundAssignUnfoldLeftFst (op : BinOp) :
    RuleName.memoryFieldCompoundAssignUnfoldLeftFst op ∈
      Rules.ruleNames := by
  cases op <;> decide

theorem mem_memoryIndexCompoundAssignUnfoldLeftFst (op : BinOp) :
    RuleName.memoryIndexCompoundAssignUnfoldLeftFst op ∈
      Rules.ruleNames := by
  cases op <;> decide

theorem mem_localCompoundAssign (op : BinOp) :
    RuleName.localCompoundAssign op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_compoundAssignValueRhsCapture (op : BinOp) :
    RuleName.compoundAssignValueRhsCapture op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageRootIncDec (op : IncDec) :
    RuleName.storageRootIncDec op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageFieldIncDec (op : IncDec) :
    RuleName.storageFieldIncDec op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageIndexIncDec (op : IncDec) :
    RuleName.storageIndexIncDec op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageFieldIncDecUnfoldLeftFst (op : IncDec) :
    RuleName.storageFieldIncDecUnfoldLeftFst op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageIndexIncDecUnfoldLeftFst (op : IncDec) :
    RuleName.storageIndexIncDecUnfoldLeftFst op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageRootIncDecAssignment (op : IncDec) :
    RuleName.storageRootIncDecAssignment op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageFieldIncDecAssignment (op : IncDec) :
    RuleName.storageFieldIncDecAssignment op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_storageIndexIncDecAssignment (op : IncDec) :
    RuleName.storageIndexIncDecAssignment op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_memoryFieldIncDec (op : IncDec) :
    RuleName.memoryFieldIncDec op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_memoryIndexIncDec (op : IncDec) :
    RuleName.memoryIndexIncDec op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_memoryFieldIncDecUnfoldLeftFst (op : IncDec) :
    RuleName.memoryFieldIncDecUnfoldLeftFst op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_memoryIndexIncDecUnfoldLeftFst (op : IncDec) :
    RuleName.memoryIndexIncDecUnfoldLeftFst op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_memoryFieldIncDecAssignment (op : IncDec) :
    RuleName.memoryFieldIncDecAssignment op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_memoryIndexIncDecAssignment (op : IncDec) :
    RuleName.memoryIndexIncDecAssignment op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_localAssignIncDec (op : IncDec) :
    RuleName.localAssignIncDec op ∈ Rules.ruleNames := by
  cases op <;> decide

theorem mem_localIncDec (op : IncDec) :
    RuleName.localIncDec op ∈ Rules.ruleNames := by
  cases op <;> decide

/-! ## `candidate` never bluffs: per-helper forward lemmas

One lemma per `UniquenessAux` dispatch helper: whenever the helper
answers `some rule`, the rule is a rule of the calculus whose mode gate and
condition hold on the dispatched statement.  Mirror image of
`applicable_eq_candidate`, organized by statement shape. -/

/-- Package the three obligations for an assignment statement. -/
private def AppliesTo (m : Modality) (stmt : Stmt) (r : RuleName) : Prop :=
  r ∈ Rules.ruleNames ∧
    ((Rules.ruleEffect r).mode stmt).applies m = true ∧
    (Rules.ruleEffect r).cond stmt

theorem valueRhsCaptureCandidate_applies {m : Modality} {le rhs : WrappedExpr}
    (hass : le.assignable = true) {r : RuleName}
    (hrhs : Rules.valueRhsCaptureRhs rhs)
    (h : valueRhsCaptureCandidate le = some r) :
    AppliesTo m (Stmt.assign ⟨le, hass⟩ rhs) r := by
  cases le with
  | var k ty fld =>
      cases k with
      | storage =>
          simp only [valueRhsCaptureCandidate] at h
          split at h
          · next hglob =>
              cases Option.some.inj h
              exact ⟨by decide, rfl,
                by simp [Rules.isGlobal, Typed.WrappedExpr.isGlobal, hglob],
                hrhs⟩
          · exact nomatch h
      | memory => exact nomatch h
      | stack => exact nomatch h
  | field k ty base fld =>
      cases k with
      | storage => cases Option.some.inj h; exact ⟨by decide, rfl, hrhs⟩
      | memory => exact nomatch h
      | stack => exact nomatch h
  | index k ty base idx =>
      cases k with
      | storage => cases Option.some.inj h; exact ⟨by decide, rfl, hrhs⟩
      | memory => exact nomatch h
      | stack => exact nomatch h
  | pushPlace t => exact nomatch h
  | bool b => exact Bool.noConfusion hass
  | intLit t v => exact Bool.noConfusion hass
  | mkCall k t n args => exact Bool.noConfusion hass
  | mkBinop op l rr => exact Bool.noConfusion hass
  | mkUnop op a => exact Bool.noConfusion hass
  | mkIncDec op t => exact Bool.noConfusion hass
  | mkTernary c t e => exact Bool.noConfusion hass

theorem assignSimpleCandidate_applies {m : Modality} {le rhs : WrappedExpr}
    (hass : le.assignable = true) {r : RuleName}
    (hs : rhs.simple = true)
    (h : assignSimpleCandidate m le rhs = some r) :
    AppliesTo m (Stmt.assign ⟨le, hass⟩ rhs) r := by
  cases le with
  | var k ty fld =>
      cases k with
      | storage =>
          simp only [assignSimpleCandidate] at h
          split at h
          · next hloc =>
              split at h
              · next hsto =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl,
                    by simp [Rules.isLocal, Typed.WrappedExpr.isLocal, hloc],
                    hsto, hs⟩
              · split at h
                · next hmem =>
                    cases Option.some.inj h
                    exact ⟨by decide, rfl, rfl, rfl, hmem, hs⟩
                · exact nomatch h
          · next hnloc =>
              split at h
              · next hglob =>
                  split at h
                  · next hsto =>
                      cases Option.some.inj h
                      exact ⟨by decide, rfl,
                        by simp [Rules.isGlobal, Typed.WrappedExpr.isGlobal,
                          hglob],
                        hsto, hs⟩
                  · split at h
                    · next hstk =>
                        cases Option.some.inj h
                        exact ⟨by decide, rfl,
                          by simp [Rules.isGlobal, Typed.WrappedExpr.isGlobal,
                            hglob],
                          hstk, hs⟩
                    · split at h
                      · next hmem =>
                          cases Option.some.inj h
                          exact ⟨by decide, rfl, rfl, rfl, hmem, hs⟩
                      · exact nomatch h
              · split at h
                · next hmem =>
                    cases Option.some.inj h
                    exact ⟨by decide, rfl, rfl, rfl, hmem, hs⟩
                · exact nomatch h
      | memory =>
          simp only [assignSimpleCandidate] at h
          split at h
          · next hmem =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, rfl, rfl, hmem, hs⟩
          · split at h
            · next hsto =>
                cases Option.some.inj h
                exact ⟨by decide, rfl, rfl, rfl, hsto, hs⟩
            · exact nomatch h
      | stack =>
          simp only [assignSimpleCandidate] at h
          split at h
          · next hb =>
              simp only [Bool.and_eq_true] at hb
              obtain ⟨h1, h2⟩ := hb
              cases Option.some.inj h
              exact ⟨by decide, rfl, h1, h2, hs⟩
          · split at h
            · next hb =>
                simp only [Bool.and_eq_true] at hb
                obtain ⟨⟨h1, h2⟩, h3⟩ := hb
                cases Option.some.inj h
                exact ⟨by decide, rfl, ⟨h1, h2⟩, h3, hs⟩
            · exact nomatch h
  | field k ty path fld =>
      cases k with
      | storage =>
          simp only [assignSimpleCandidate] at h
          split at h
          · next hpc =>
              split at h
              · next hmem =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, hpc, hmem, hs⟩
              · next hnmem =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, hpc, hs, hnmem⟩
          · next hnpc =>
              split at h
              · next hsto =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, simple_of_not_complex hnpc, hsto, hs⟩
              · split at h
                · next hstk =>
                    cases Option.some.inj h
                    exact ⟨by decide, rfl, simple_of_not_complex hnpc, hstk, hs⟩
                · split at h
                  · next hmem =>
                      cases Option.some.inj h
                      exact ⟨by decide, rfl, simple_of_not_complex hnpc, hmem, hs⟩
                  · exact nomatch h
      | memory =>
          simp only [assignSimpleCandidate] at h
          split at h
          · next hpc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hpc, hs⟩
          · next hnpc =>
              split at h
              · next hmem =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, simple_of_not_complex hnpc, hmem, hs⟩
              · split at h
                · next hstk =>
                    cases Option.some.inj h
                    exact ⟨by decide, rfl, simple_of_not_complex hnpc, hstk, hs⟩
                · exact nomatch h
      | stack =>
          simp only [assignSimpleCandidate] at h
          split at h
          · next hb =>
              simp only [Bool.and_eq_true] at hb
              obtain ⟨h1, h2⟩ := hb
              cases Option.some.inj h
              exact ⟨by decide, rfl, h1, h2, hs⟩
          · split at h
            · next hb =>
                simp only [Bool.and_eq_true] at hb
                obtain ⟨⟨h1, h2⟩, h3⟩ := hb
                cases Option.some.inj h
                exact ⟨by decide, rfl, ⟨h1, h2⟩, h3, hs⟩
            · exact nomatch h
  | index k ty path idx =>
      cases k with
      | storage =>
          simp only [assignSimpleCandidate] at h
          split at h
          · next hpc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hpc, hs⟩
          · next hnpc =>
              split at h
              · next hic =>
                  split at h
                  · next hmem =>
                      cases Option.some.inj h
                      exact ⟨by decide, rfl, simple_of_not_complex hnpc, hic,
                        hmem, hs⟩
                  · next hnmem =>
                      cases Option.some.inj h
                      exact ⟨by decide, rfl, simple_of_not_complex hnpc, hic,
                        hs, hnmem⟩
              · next hnic =>
                  split at h
                  · next hsto =>
                      split at h
                      · next harr =>
                          cases m <;>
                            (cases Option.some.inj h
                             exact ⟨by decide, rfl,
                               simple_of_not_complex hnpc,
                               simple_of_not_complex hnic, hsto, hs,
                               isArray_of_arrayTyB harr⟩)
                      · split at h
                        · next hmap =>
                            cases Option.some.inj h
                            exact ⟨by decide, rfl,
                              simple_of_not_complex hnpc,
                              simple_of_not_complex hnic, hsto, hs,
                              isMapping_of_mappingTyB hmap⟩
                        · exact nomatch h
                  · split at h
                    · next hstk =>
                        split at h
                        · next harr =>
                            cases m <;>
                              (cases Option.some.inj h
                               exact ⟨by decide, rfl,
                                 simple_of_not_complex hnpc,
                                 simple_of_not_complex hnic, hstk, hs,
                                 isArray_of_arrayTyB harr⟩)
                        · split at h
                          · next hmap =>
                              cases Option.some.inj h
                              exact ⟨by decide, rfl,
                                simple_of_not_complex hnpc,
                                simple_of_not_complex hnic, hstk, hs,
                                isMapping_of_mappingTyB hmap⟩
                          · exact nomatch h
                    · split at h
                      · next hmem =>
                          split at h
                          · next harr =>
                              cases m <;>
                                (cases Option.some.inj h
                                 exact ⟨by decide, rfl,
                                   simple_of_not_complex hnpc,
                                   simple_of_not_complex hnic, hmem, hs,
                                   isArray_of_arrayTyB harr⟩)
                          · split at h
                            · next hmap =>
                                cases Option.some.inj h
                                exact ⟨by decide, rfl,
                                  simple_of_not_complex hnpc,
                                  simple_of_not_complex hnic, hmem, hs,
                                  isMapping_of_mappingTyB hmap⟩
                            · exact nomatch h
                      · exact nomatch h
      | memory =>
          simp only [assignSimpleCandidate] at h
          split at h
          · next hpc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hpc, hs⟩
          · next hnpc =>
              split at h
              · next hic =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, simple_of_not_complex hnpc, hic, hs⟩
              · next hnic =>
                  split at h
                  · next hmem =>
                      cases m <;>
                        (cases Option.some.inj h
                         exact ⟨by decide, rfl,
                           simple_of_not_complex hnpc,
                           simple_of_not_complex hnic, hmem, hs⟩)
                  · split at h
                    · next hstk =>
                        cases m <;>
                          (cases Option.some.inj h
                           exact ⟨by decide, rfl,
                             simple_of_not_complex hnpc,
                             simple_of_not_complex hnic, hstk, hs⟩)
                    · exact nomatch h
      | stack =>
          simp only [assignSimpleCandidate] at h
          split at h
          · next hb =>
              simp only [Bool.and_eq_true] at hb
              obtain ⟨h1, h2⟩ := hb
              cases Option.some.inj h
              exact ⟨by decide, rfl, h1, h2, hs⟩
          · split at h
            · next hb =>
                simp only [Bool.and_eq_true] at hb
                obtain ⟨⟨h1, h2⟩, h3⟩ := hb
                cases Option.some.inj h
                exact ⟨by decide, rfl, ⟨h1, h2⟩, h3, hs⟩
            · exact nomatch h
  | pushPlace t =>
      simp only [assignSimpleCandidate] at h
      split at h
      · next hk =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hk, hs⟩
      · exact nomatch h
  | bool b => exact Bool.noConfusion hass
  | intLit t v => exact Bool.noConfusion hass
  | mkCall k t n args => exact Bool.noConfusion hass
  | mkBinop op l rr => exact Bool.noConfusion hass
  | mkUnop op a => exact Bool.noConfusion hass
  | mkIncDec op t => exact Bool.noConfusion hass
  | mkTernary c t e => exact Bool.noConfusion hass

theorem assignComplexCandidate_applies {m : Modality} {le rhs : WrappedExpr}
    (hass : le.assignable = true) {r : RuleName}
    (hcx : rhs.complex = true)
    (hpush : ∀ t, rhs = WrappedExpr.pushPlace t -> t.kind = Kind.storage)
    (h : assignComplexCandidate m le rhs = some r) :
    AppliesTo m (Stmt.assign ⟨le, hass⟩ rhs) r := by
  cases rhs with
  | var k ty fld => exact Bool.noConfusion hcx
  | bool b => exact Bool.noConfusion hcx
  | intLit ty v => exact Bool.noConfusion hcx
  | field k ty path fld =>
      cases k with
      | memory =>
          simp only [assignComplexCandidate] at h
          split at h
          · next hmc =>
              split at h
              · next hpc =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, hpc,
                    fun hsto => absurd hmc.1 (by simp [kind_of_isStorage hsto])⟩
              · next hnpc =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl,
                    by simp [Rules.isMemory, Typed.WrappedExpr.isMemory, hmc.1],
                    hmc.2, simple_of_not_complex hnpc⟩
          · next hn1 =>
              split at h
              · next h2 =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, h2.1, h2.2, hcx⟩
              · next hn2 =>
                  split at h
                  · next hpc =>
                      cases Option.some.inj h
                      exact ⟨by decide, rfl, hpc,
                        fun hsto => hn2 ⟨kind_of_isStorage hsto, rfl⟩⟩
                  · next hnpc =>
                      split at h
                      · next hstk =>
                          cases Option.some.inj h
                          exact ⟨by decide, rfl, hstk, simple_of_not_complex hnpc⟩
                      · split at h
                        · next hk =>
                            cases Option.some.inj h
                            exact ⟨by decide, rfl, hk,
                              simple_of_not_complex (fun hc => hn1 ⟨hk, hc⟩),
                              simple_of_not_complex hnpc⟩
                        · exact nomatch h
      | storage =>
          simp only [assignComplexCandidate] at h
          split at h
          · next hmc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hmc.1, hmc.2, hcx, trivial⟩
          · next hn1 =>
              split at h
              · next h2 => exact Bool.noConfusion h2.2
              · next hn2 =>
                  split at h
                  · next hpc =>
                      cases Option.some.inj h
                      exact ⟨by decide, rfl, hpc, hn1⟩
                  · next hnpc =>
                      split at h
                      · next hsto =>
                          split at h
                          · next hlc =>
                              cases Option.some.inj h
                              exact ⟨by decide, rfl, hsto, hlc,
                                simple_of_not_complex hnpc⟩
                          · next hnlc =>
                              split at h
                              · next hloc =>
                                  cases Option.some.inj h
                                  exact ⟨by decide, rfl, hloc,
                                    simple_of_not_complex hnpc⟩
                              · split at h
                                · next hglob =>
                                    cases Option.some.inj h
                                    exact ⟨by decide, rfl, hglob,
                                      simple_of_not_complex hnpc,
                                      simple_of_not_complex hnlc⟩
                                · exact nomatch h
                      · next hnsto =>
                          split at h
                          · next hstk =>
                              cases Option.some.inj h
                              exact ⟨by decide, rfl, hstk,
                                simple_of_not_complex hnpc⟩
                          · split at h
                            · next hk =>
                                cases Option.some.inj h
                                exact ⟨by decide, rfl, hk,
                                  simple_of_not_complex (fun hc => hn1 ⟨hk, hc⟩),
                                  simple_of_not_complex hnpc⟩
                            · exact nomatch h
      | stack =>
          simp only [assignComplexCandidate] at h
          split at h
          · next hmc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hmc.1, hmc.2, hcx, trivial⟩
          · next hn1 =>
              split at h
              · next h2 => exact Bool.noConfusion h2.2
              · exact nomatch h
  | index k ty path idx =>
      cases k with
      | memory =>
          simp only [assignComplexCandidate] at h
          split at h
          · next hmc =>
              split at h
              · next hpc =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, hpc,
                    fun hsto => absurd hmc.1 (by simp [kind_of_isStorage hsto])⟩
              · next hnpc =>
                  split at h
                  · next hic =>
                      cases Option.some.inj h
                      exact ⟨by decide, rfl, simple_of_not_complex hnpc, hic,
                        fun hsto => absurd hmc.1 (by simp [kind_of_isStorage hsto])⟩
                  · next hnic =>
                      cases Option.some.inj h
                      exact ⟨by decide, rfl,
                        by simp [Rules.isMemory, Typed.WrappedExpr.isMemory, hmc.1],
                        hmc.2, simple_of_not_complex hnpc,
                        simple_of_not_complex hnic⟩
          · next hn1 =>
              split at h
              · next h2 =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, h2.1, h2.2, hcx⟩
              · next hn2 =>
                  split at h
                  · next hpc =>
                      cases Option.some.inj h
                      exact ⟨by decide, rfl, hpc,
                        fun hsto => hn2 ⟨kind_of_isStorage hsto, rfl⟩⟩
                  · next hnpc =>
                      split at h
                      · next hic =>
                          cases Option.some.inj h
                          exact ⟨by decide, rfl, simple_of_not_complex hnpc, hic,
                            fun hsto => hn2 ⟨kind_of_isStorage hsto, rfl⟩⟩
                      · next hnic =>
                          split at h
                          · next hstk =>
                              cases m <;>
                                (cases Option.some.inj h
                                 exact ⟨by decide, rfl, hstk,
                                   simple_of_not_complex hnpc,
                                   simple_of_not_complex hnic⟩)
                          · split at h
                            · next hk =>
                                cases m <;>
                                  (cases Option.some.inj h
                                   exact ⟨by decide, rfl, hk,
                                     simple_of_not_complex
                                       (fun hc => hn1 ⟨hk, hc⟩),
                                     simple_of_not_complex hnpc,
                                     simple_of_not_complex hnic⟩)
                            · exact nomatch h
      | storage =>
          simp only [assignComplexCandidate] at h
          split at h
          · next hmc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hmc.1, hmc.2, hcx, trivial⟩
          · next hn1 =>
              split at h
              · next h2 => exact Bool.noConfusion h2.2
              · next hn2 =>
                  split at h
                  · next hpc =>
                      cases Option.some.inj h
                      exact ⟨by decide, rfl, hpc, hn1⟩
                  · next hnpc =>
                      split at h
                      · next hic =>
                          cases Option.some.inj h
                          exact ⟨by decide, rfl, simple_of_not_complex hnpc,
                            hic, hn1⟩
                      · next hnic =>
                          split at h
                          · next hsto =>
                              split at h
                              · next hlc =>
                                  cases Option.some.inj h
                                  exact ⟨by decide, rfl, hsto, hlc,
                                    simple_of_not_complex hnpc,
                                    simple_of_not_complex hnic⟩
                              · next hnlc =>
                                  split at h
                                  · next hloc =>
                                      split at h
                                      · next harr =>
                                          cases m <;>
                                            (cases Option.some.inj h
                                             exact ⟨by decide, rfl, hloc,
                                               simple_of_not_complex hnpc,
                                               simple_of_not_complex hnic,
                                               isArray_of_arrayTyB harr⟩)
                                      · split at h
                                        · next hmap =>
                                            cases Option.some.inj h
                                            exact ⟨by decide, rfl, hloc,
                                              simple_of_not_complex hnpc,
                                              simple_of_not_complex hnic,
                                              isMapping_of_mappingTyB hmap⟩
                                        · exact nomatch h
                                  · split at h
                                    · next hglob =>
                                        split at h
                                        · next harr =>
                                            cases m <;>
                                              (cases Option.some.inj h
                                               exact ⟨by decide, rfl, hglob,
                                                 simple_of_not_complex hnpc,
                                                 simple_of_not_complex hnic,
                                                 isArray_of_arrayTyB harr,
                                                 simple_of_not_complex hnlc⟩)
                                        · split at h
                                          · next hmap =>
                                              cases Option.some.inj h
                                              exact ⟨by decide, rfl, hglob,
                                                simple_of_not_complex hnpc,
                                                simple_of_not_complex hnic,
                                                isMapping_of_mappingTyB hmap,
                                                simple_of_not_complex hnlc⟩
                                          · exact nomatch h
                                    · exact nomatch h
                          · split at h
                            · next hstk =>
                                split at h
                                · next harr =>
                                    cases m <;>
                                      (cases Option.some.inj h
                                       exact ⟨by decide, rfl, hstk,
                                         simple_of_not_complex hnpc,
                                         simple_of_not_complex hnic,
                                         isArray_of_arrayTyB harr⟩)
                                · split at h
                                  · next hmap =>
                                      cases Option.some.inj h
                                      exact ⟨by decide, rfl, hstk,
                                        simple_of_not_complex hnpc,
                                        simple_of_not_complex hnic,
                                        isMapping_of_mappingTyB hmap⟩
                                  · exact nomatch h
                            · split at h
                              · next hk =>
                                  cases Option.some.inj h
                                  exact ⟨by decide, rfl, hk,
                                    simple_of_not_complex
                                      (fun hc => hn1 ⟨hk, hc⟩),
                                    simple_of_not_complex hnpc,
                                    simple_of_not_complex hnic⟩
                              · exact nomatch h
      | stack =>
          simp only [assignComplexCandidate] at h
          split at h
          · next hmc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hmc.1, hmc.2, hcx, trivial⟩
          · next hn1 =>
              split at h
              · next h2 => exact Bool.noConfusion h2.2
              · exact nomatch h
  | pushPlace target =>
      have hk := hpush target rfl
      simp only [assignComplexCandidate] at h
      split at h
      · next hmc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hmc.1, hmc.2, hcx, trivial⟩
      · next hn1 =>
          split at h
          · next h2 => exact Bool.noConfusion h2.2
          · next hn2 =>
              split at h
              · next htc =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, hk, htc, hn1⟩
              · next hntc =>
                  split at h
                  · next hloc =>
                      cases Option.some.inj h
                      exact ⟨by decide, rfl, hloc, hk,
                        simple_of_not_complex hntc⟩
                  · exact nomatch h
  | mkCall k ty fn args =>
      simp only [assignComplexCandidate] at h
      split at h
      · next hmc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hmc.1, hmc.2, hcx, trivial⟩
      · next hn1 =>
          split at h
          · next h2 =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, h2.1, h2.2, hcx⟩
          · exact nomatch h
  | mkBinop op l rr =>
      simp only [assignComplexCandidate] at h
      split at h
      · next hmc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hmc.1, hmc.2, hcx, trivial⟩
      · next hn1 =>
          split at h
          · next h2 => exact Bool.noConfusion h2.2
          · next hn2 =>
              split at h
              · next hsv =>
                  simp only [Bool.and_eq_true] at hsv
                  obtain ⟨hstk, hsimp⟩ := hsv
                  split at h
                  · next hlc =>
                      cases Option.some.inj h
                      exact ⟨mem_binopUnfoldLeft op, rfl, rfl, ⟨hstk, hsimp⟩,
                        hlc⟩
                  · next hnlc =>
                      split at h
                      · next hrc =>
                          cases op <;> cases Option.some.inj h <;>
                            first
                              | exact ⟨by decide, rfl, rfl, ⟨hstk, hsimp⟩,
                                  simple_of_not_complex hnlc, hrc⟩
                              | exact ⟨by decide, rfl, rfl, rfl,
                                  ⟨hstk, hsimp⟩,
                                  simple_of_not_complex hnlc, hrc⟩
                      · next hnrc =>
                          cases Option.some.inj h
                          exact ⟨mem_binopAssignment op, rfl, rfl,
                            ⟨hstk, hsimp⟩, simple_of_not_complex hnlc,
                            simple_of_not_complex hnrc⟩
              · next hnsv =>
                  split at h
                  · next hb =>
                      simp only [Bool.and_eq_true] at hb
                      obtain ⟨⟨hop, hl⟩, hr2⟩ := hb
                      cases Option.some.inj h
                      exact ⟨mem_binopUnfoldResult op, rfl, rfl, hop, hl, hr2,
                        fun ⟨ha, hb2⟩ => hnsv (and_true_of ha hb2), hn1⟩
                  · next hnb =>
                      exact valueRhsCaptureCandidate_applies hass
                        (fun ⟨ha, hb2, hc2⟩ => hnb (and_true_of (and_true_of ha hb2) hc2)) h
  | mkUnop op arg =>
      simp only [assignComplexCandidate] at h
      split at h
      · next hmc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hmc.1, hmc.2, hcx, trivial⟩
      · next hn1 =>
          split at h
          · next h2 => exact Bool.noConfusion h2.2
          · next hn2 =>
              split at h
              · next hsv =>
                  simp only [Bool.and_eq_true] at hsv
                  obtain ⟨hstk, hsimp⟩ := hsv
                  split at h
                  · next hac =>
                      cases Option.some.inj h
                      exact ⟨mem_unopCapture op, rfl, rfl, ⟨hstk, hsimp⟩, hac⟩
                  · next hnac =>
                      cases Option.some.inj h
                      exact ⟨mem_unopAssignment op, rfl, rfl, ⟨hstk, hsimp⟩,
                        simple_of_not_complex hnac⟩
              · exact valueRhsCaptureCandidate_applies hass trivial h
  | mkIncDec op target =>
      simp only [assignComplexCandidate] at h
      split at h
      · next hmc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hmc.1, hmc.2, hcx, trivial⟩
      · next hn1 =>
          split at h
          · next h2 => exact Bool.noConfusion h2.2
          · next hn2 =>
              split at h
              · next hsv =>
                  simp only [Bool.and_eq_true] at hsv
                  obtain ⟨hstk, hsimp⟩ := hsv
                  split at h
                  · next htv =>
                      simp only [Bool.and_eq_true] at htv
                      obtain ⟨ht1, ht2⟩ := htv
                      cases Option.some.inj h
                      exact ⟨mem_localAssignIncDec op, rfl, rfl,
                        ⟨hstk, hsimp⟩, ht1, ht2⟩
                  · next hntv =>
                      split at h
                      · next ty2 fld2 =>
                          split at h
                          · next hglob =>
                              cases Option.some.inj h
                              exact ⟨mem_storageRootIncDecAssignment op,
                                rfl, rfl, ⟨hstk, hsimp⟩,
                                by simp [Rules.isGlobal,
                                  Typed.WrappedExpr.isGlobal, hglob]⟩
                          · exact nomatch h
                      · next ty2 path2 fld2 =>
                          split at h
                          · exact nomatch h
                          · next hnpc =>
                              cases Option.some.inj h
                              exact ⟨mem_storageFieldIncDecAssignment op,
                                rfl, rfl, ⟨hstk, hsimp⟩,
                                simple_of_not_complex hnpc⟩
                      · next ty2 path2 idx2 =>
                          split at h
                          · exact nomatch h
                          · next hno =>
                              simp only [Bool.or_eq_true, not_or] at hno
                              obtain ⟨hnp, hni⟩ := hno
                              cases Option.some.inj h
                              exact ⟨mem_storageIndexIncDecAssignment op,
                                rfl, rfl, ⟨hstk, hsimp⟩,
                                simple_of_not_complex hnp,
                                simple_of_not_complex hni⟩
                      · next ty2 path2 fld2 =>
                          split at h
                          · exact nomatch h
                          · next hnpc =>
                              cases Option.some.inj h
                              exact ⟨mem_memoryFieldIncDecAssignment op,
                                rfl, rfl, ⟨hstk, hsimp⟩,
                                simple_of_not_complex hnpc⟩
                      · next ty2 path2 idx2 =>
                          split at h
                          · exact nomatch h
                          · next hno =>
                              simp only [Bool.or_eq_true, not_or] at hno
                              obtain ⟨hnp, hni⟩ := hno
                              cases Option.some.inj h
                              exact ⟨mem_memoryIndexIncDecAssignment op,
                                rfl, rfl, ⟨hstk, hsimp⟩,
                                simple_of_not_complex hnp,
                                simple_of_not_complex hni⟩
                      · exact nomatch h
              · exact valueRhsCaptureCandidate_applies hass trivial h
  | mkTernary c thn els =>
      simp only [assignComplexCandidate] at h
      split at h
      · next hmc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hmc.1, hmc.2, hcx, trivial⟩
      · next hn1 =>
          split at h
          · next h2 => exact Bool.noConfusion h2.2
          · next hn2 =>
              split at h
              · next hcc =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, hcc, hn1⟩
              · next hncc =>
                  split at h
                  · next hsv =>
                      simp only [Bool.and_eq_true] at hsv
                      cases Option.some.inj h
                      exact ⟨by decide, rfl, simple_of_not_complex hncc,
                        hsv.1, hsv.2⟩
                  · split at h
                    · next hsto =>
                        cases Option.some.inj h
                        exact ⟨by decide, rfl, simple_of_not_complex hncc,
                          hsto⟩
                    · exact nomatch h

theorem assignCandidate_applies {m : Modality} {le rhs : WrappedExpr}
    (hass : le.assignable = true) {r : RuleName}
    (hpush : ∀ t, rhs = WrappedExpr.pushPlace t -> t.kind = Kind.storage)
    (h : assignCandidate m le rhs = some r) :
    AppliesTo m (Stmt.assign ⟨le, hass⟩ rhs) r := by
  unfold assignCandidate at h
  split at h
  · next hs => exact assignSimpleCandidate_applies hass hs h
  · next hns =>
      exact assignComplexCandidate_applies hass (complex_of_not_simple hns)
        hpush h

theorem eq_false_of_not_eq_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b with
  | true => exact absurd rfl h
  | false => rfl

theorem all_simple_of_not_any_complex {args : List WrappedExpr}
    (h : args.any (·.complex) = false) : args.all (·.simple) = true := by
  simp only [List.any_eq_false] at h
  simp only [List.all_eq_true]
  intro x hx
  exact simple_of_not_complex (h x hx)

theorem memoryDeclCandidate_applies {m : Modality} {ty : Ty} {name : Name}
    {init : Option WrappedExpr} {r : RuleName}
    (h : memoryDeclCandidate init = some r) :
    AppliesTo m (Stmt.memoryDecl ty name init) r := by
  cases init with
  | none => cases Option.some.inj h; exact ⟨by decide, rfl, rfl⟩
  | some rhs =>
      simp only [memoryDeclCandidate] at h
      split at h
      · next hmem => cases Option.some.inj h; exact ⟨by decide, rfl, hmem⟩
      · next hnmem =>
          split at h
          · next rhsTy path fld =>
              split at h
              · next hpc =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, hpc⟩
              · next hnpc =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, simple_of_not_complex hnpc⟩
          · split at h
            · next hb =>
                simp only [Bool.and_eq_true] at hb
                cases Option.some.inj h
                exact ⟨by decide, rfl, hb.1, hb.2⟩
            · exact nomatch h

theorem deleteCandidate_applies {m : Modality} {te : WrappedExpr}
    (hass : te.assignable = true) {r : RuleName}
    (h : deleteCandidate te = some r) :
    AppliesTo m (Stmt.delete ⟨te, hass⟩) r := by
  cases te with
  | var k ty fld =>
      cases k with
      | storage =>
          simp only [deleteCandidate] at h
          split at h
          · next hglob =>
              cases Option.some.inj h
              refine ⟨by decide, rfl, ?_⟩
              show (WrappedExpr.var Kind.storage ty fld).isGlobal = true
              simp [Typed.WrappedExpr.isGlobal, hglob]
          · exact nomatch h
      | memory =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, rfl⟩
      | stack => exact nomatch h
  | field k ty path fld =>
      cases k with
      | storage =>
          simp only [deleteCandidate] at h
          split at h
          · next hpc => cases Option.some.inj h; exact ⟨by decide, rfl, hpc⟩
          · next hnpc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, simple_of_not_complex hnpc⟩
      | memory =>
          simp only [deleteCandidate] at h
          split at h
          · next hpc => cases Option.some.inj h; exact ⟨by decide, rfl, hpc⟩
          · next hnpc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, simple_of_not_complex hnpc,
                field_prim_or_identity fld⟩
      | stack => exact nomatch h
  | index k ty path idx =>
      cases k with
      | storage =>
          simp only [deleteCandidate] at h
          split at h
          · next hpc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, Or.inl hpc⟩
          · next hnpc =>
              split at h
              · next hic =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl,
                    Or.inr ⟨simple_of_not_complex hnpc, hic⟩⟩
              · next hnic =>
                  split at h
                  · next hcont =>
                      simp only [Bool.or_eq_true] at hcont
                      cases Option.some.inj h
                      refine ⟨by decide, rfl, simple_of_not_complex hnpc,
                        simple_of_not_complex hnic, ?_⟩
                      cases hcont with
                      | inl harr => exact Or.inl (isArray_of_arrayTyB harr)
                      | inr hmap =>
                          exact Or.inr (isMapping_of_mappingTyB hmap)
                  · exact nomatch h
      | memory =>
          simp only [deleteCandidate] at h
          split at h
          · next hpc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, Or.inl hpc⟩
          · next hnpc =>
              split at h
              · next hic =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl,
                    Or.inr ⟨simple_of_not_complex hnpc, hic⟩⟩
              · next hnic =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, simple_of_not_complex hnpc,
                    simple_of_not_complex hnic, ty_prim_or_ref ty⟩
      | stack => exact nomatch h
  | pushPlace p =>
      simp only [deleteCandidate] at h
      split at h
      · next hk =>
          split at h
          · next hpc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hk, hpc⟩
          · next hnpc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hk, simple_of_not_complex hnpc⟩
      · exact nomatch h
  | bool b => exact Bool.noConfusion hass
  | intLit t v => exact Bool.noConfusion hass
  | mkCall k t n args => exact Bool.noConfusion hass
  | mkBinop op l rr => exact Bool.noConfusion hass
  | mkUnop op a => exact Bool.noConfusion hass
  | mkIncDec op t => exact Bool.noConfusion hass
  | mkTernary c t e => exact Bool.noConfusion hass

theorem pushCandidate_applies {m : Modality} {te : WrappedExpr}
    (hass : te.assignable = true) {value : Option WrappedExpr} {r : RuleName}
    (h : pushCandidate te value = some r) :
    AppliesTo m (Stmt.push ⟨te, hass⟩ value) r := by
  cases value with
  | none =>
      simp only [pushCandidate] at h
      split at h
      · next hk =>
          split at h
          · next htc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hk, htc, rfl⟩
          · next hntc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hk, simple_of_not_complex hntc, rfl⟩
      · exact nomatch h
  | some rhs =>
      simp only [pushCandidate] at h
      split at h
      · next hk =>
          split at h
          · next htc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hk, htc, rfl⟩
          · next hntc =>
              split at h
              · next hrc =>
                  cases Option.some.inj h
                  exact ⟨by decide, rfl, hk, simple_of_not_complex hntc, hrc⟩
              · next hnrc =>
                  split at h
                  · next hsto =>
                      cases Option.some.inj h
                      exact ⟨by decide, rfl, hk, simple_of_not_complex hntc,
                        hsto, simple_of_not_complex hnrc⟩
                  · split at h
                    · next hstk =>
                        cases Option.some.inj h
                        exact ⟨by decide, rfl, hk,
                          simple_of_not_complex hntc, hstk,
                          simple_of_not_complex hnrc⟩
                    · exact nomatch h
      · exact nomatch h

theorem popCandidate_applies {m : Modality} {te : WrappedExpr}
    (hass : te.assignable = true) {r : RuleName}
    (h : popCandidate m te = some r) :
    AppliesTo m (Stmt.pop ⟨te, hass⟩) r := by
  simp only [popCandidate] at h
  split at h
  · next hk =>
      split at h
      · next htc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hk, htc⟩
      · next hntc =>
          cases m <;>
            (cases Option.some.inj h
             exact ⟨by decide, rfl, hk, simple_of_not_complex hntc⟩)
  · exact nomatch h

theorem compoundAssignCandidate_applies {m : Modality} {op : BinOp}
    {le rhs : WrappedExpr} (hass : le.assignable = true) {r : RuleName}
    (h : compoundAssignCandidate op le rhs = some r) :
    AppliesTo m (Stmt.compoundAssign op ⟨le, hass⟩ rhs) r := by
  simp only [compoundAssignCandidate] at h
  split at h
  · next hca =>
      split at h
      · next hb =>
          simp only [Bool.and_eq_true] at hb
          obtain ⟨hr1, hr2⟩ := hb
          split at h
          · next hsv =>
              simp only [Bool.and_eq_true] at hsv
              cases Option.some.inj h
              exact ⟨mem_localCompoundAssign op, rfl, rfl, hca,
                ⟨hsv.1, hsv.2⟩, hr1, hr2⟩
          · next hnsv =>
              split at h
              · next ty fld =>
                  split at h
                  · next hglob =>
                      cases Option.some.inj h
                      exact ⟨mem_storageRootCompoundAssign op, rfl, rfl, hca,
                        by simp [Rules.isGlobal, Typed.WrappedExpr.isGlobal,
                          hglob],
                        hr1, hr2⟩
                  · exact nomatch h
              · next ty path fld =>
                  split at h
                  · next hpc =>
                      cases Option.some.inj h
                      exact ⟨mem_storageFieldCompoundAssignUnfoldLeftFst op,
                        rfl, rfl, hca, hpc, hr1, hr2⟩
                  · next hnpc =>
                      cases Option.some.inj h
                      exact ⟨mem_storageFieldCompoundAssign op, rfl, rfl,
                        hca, simple_of_not_complex hnpc, hr1, hr2⟩
              · next ty path idx =>
                  split at h
                  · exact nomatch h
                  · next hnic =>
                      split at h
                      · next hpc =>
                          cases Option.some.inj h
                          exact ⟨mem_storageIndexCompoundAssignUnfoldLeftFst
                              op,
                            rfl, rfl, hca, hpc, simple_of_not_complex hnic,
                            hr1, hr2⟩
                      · next hnpc =>
                          cases Option.some.inj h
                          exact ⟨mem_storageIndexCompoundAssign op, rfl, rfl,
                            hca, simple_of_not_complex hnpc,
                            simple_of_not_complex hnic, hr1, hr2⟩
              · next ty path fld =>
                  split at h
                  · next hpc =>
                      cases Option.some.inj h
                      exact ⟨mem_memoryFieldCompoundAssignUnfoldLeftFst op,
                        rfl, rfl, hca, hpc, hr1, hr2⟩
                  · next hnpc =>
                      cases Option.some.inj h
                      exact ⟨mem_memoryFieldCompoundAssign op, rfl, rfl,
                        hca, simple_of_not_complex hnpc, hr1, hr2⟩
              · next ty path idx =>
                  split at h
                  · exact nomatch h
                  · next hnic =>
                      split at h
                      · next hpc =>
                          cases Option.some.inj h
                          exact ⟨mem_memoryIndexCompoundAssignUnfoldLeftFst
                              op,
                            rfl, rfl, hca, hpc, simple_of_not_complex hnic,
                            hr1, hr2⟩
                      · next hnpc =>
                          cases Option.some.inj h
                          exact ⟨mem_memoryIndexCompoundAssign op, rfl, rfl,
                            hca, simple_of_not_complex hnpc,
                            simple_of_not_complex hnic, hr1, hr2⟩
              · exact nomatch h
      · next hnb =>
          cases Option.some.inj h
          exact ⟨mem_compoundAssignValueRhsCapture op, rfl, rfl, hca,
            fun ⟨ha, hb2⟩ => hnb (and_true_of ha hb2)⟩
  · exact nomatch h

theorem incDecStmtCandidate_applies {m : Modality} {op : IncDec}
    {target : WrappedExpr} {r : RuleName}
    (h : incDecStmtCandidate op target = some r) :
    AppliesTo m (Stmt.expr (WrappedExpr.incDec op target)) r := by
  simp only [incDecStmtCandidate] at h
  split at h
  · next htv =>
      simp only [Bool.and_eq_true] at htv
      cases Option.some.inj h
      exact ⟨mem_localIncDec op, rfl, rfl, htv.1, htv.2⟩
  · next hntv =>
      split at h
      · next ty fld =>
          split at h
          · next hglob =>
              cases Option.some.inj h
              exact ⟨mem_storageRootIncDec op, rfl, rfl,
                by simp [Rules.isGlobal, Typed.WrappedExpr.isGlobal, hglob]⟩
          · exact nomatch h
      · next ty path fld =>
          split at h
          · next hpc =>
              cases Option.some.inj h
              exact ⟨mem_storageFieldIncDecUnfoldLeftFst op, rfl, rfl, hpc⟩
          · next hnpc =>
              cases Option.some.inj h
              exact ⟨mem_storageFieldIncDec op, rfl, rfl,
                simple_of_not_complex hnpc⟩
      · next ty path idx =>
          split at h
          · exact nomatch h
          · next hnic =>
              split at h
              · next hpc =>
                  cases Option.some.inj h
                  exact ⟨mem_storageIndexIncDecUnfoldLeftFst op, rfl, rfl,
                    hpc, simple_of_not_complex hnic⟩
              · next hnpc =>
                  cases Option.some.inj h
                  exact ⟨mem_storageIndexIncDec op, rfl, rfl,
                    simple_of_not_complex hnpc, simple_of_not_complex hnic⟩
      · next ty path fld =>
          split at h
          · next hpc =>
              cases Option.some.inj h
              exact ⟨mem_memoryFieldIncDecUnfoldLeftFst op, rfl, rfl, hpc⟩
          · next hnpc =>
              cases Option.some.inj h
              exact ⟨mem_memoryFieldIncDec op, rfl, rfl,
                simple_of_not_complex hnpc⟩
      · next ty path idx =>
          split at h
          · exact nomatch h
          · next hnic =>
              split at h
              · next hpc =>
                  cases Option.some.inj h
                  exact ⟨mem_memoryIndexIncDecUnfoldLeftFst op, rfl, rfl,
                    hpc, simple_of_not_complex hnic⟩
              · next hnpc =>
                  cases Option.some.inj h
                  exact ⟨mem_memoryIndexIncDec op, rfl, rfl,
                    simple_of_not_complex hnpc, simple_of_not_complex hnic⟩
      · exact nomatch h

theorem exprCandidate_applies {m : Modality} {e : WrappedExpr} {r : RuleName}
    (h : exprCandidate e = some r) :
    AppliesTo m (Stmt.expr e) r := by
  cases e <;>
    first
      | exact incDecStmtCandidate_applies h
      | (cases Option.some.inj h; exact ⟨by decide, rfl, trivial⟩)

theorem assertCandidate_applies {m : Modality} {c : WrappedExpr}
    {r : RuleName} (h : assertCandidate c = some r) :
    AppliesTo m (Stmt.assertStmt c) r := by
  simp only [assertCandidate] at h
  split at h
  · next hcc => cases Option.some.inj h; exact ⟨by decide, rfl, hcc⟩
  · next hnc =>
      cases Option.some.inj h
      exact ⟨by decide, rfl, simple_of_not_complex hnc⟩

theorem requireCandidate_applies {m : Modality} {c : WrappedExpr}
    {r : RuleName} (h : requireCandidate c = some r) :
    AppliesTo m (Stmt.requireStmt c) r := by
  simp only [requireCandidate] at h
  split at h
  · next hcc => cases Option.some.inj h; exact ⟨by decide, rfl, hcc⟩
  · next hnc =>
      cases Option.some.inj h
      exact ⟨by decide, rfl, simple_of_not_complex hnc⟩

theorem iteCandidate_applies {m : Modality} {c : WrappedExpr}
    {thn els : List Stmt} {r : RuleName}
    (h : iteCandidate c = some r) :
    AppliesTo m (Stmt.ite c thn els) r := by
  cases c with
  | bool b =>
      cases b with
      | true => cases Option.some.inj h; exact ⟨by decide, rfl, trivial⟩
      | false => cases Option.some.inj h; exact ⟨by decide, rfl, trivial⟩
  | mkUnop op inner =>
      cases op with
      | not =>
          simp only [iteCandidate] at h
          split at h
          · next hic =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, rfl,
                fun inner' hEq => by cases hEq; exact hic⟩
          · next hnic =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, simple_of_not_complex hnic⟩
      | neg =>
          simp only [iteCandidate] at h
          split at h
          · next hcc =>
              cases Option.some.inj h
              exact ⟨by decide, rfl, hcc, fun inner' hEq => by cases hEq⟩
          · exact nomatch h
  | var k ty fld =>
      simp only [iteCandidate] at h
      split at h
      · next hcc => exact Bool.noConfusion hcc
      · exact nomatch h
  | intLit ty v =>
      simp only [iteCandidate] at h
      split at h
      · next hcc => exact Bool.noConfusion hcc
      · exact nomatch h
  | field k ty base fld =>
      simp only [iteCandidate] at h
      split at h
      · next hcc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hcc, fun inner' hEq => by cases hEq⟩
      · exact nomatch h
  | index k ty base idx =>
      simp only [iteCandidate] at h
      split at h
      · next hcc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hcc, fun inner' hEq => by cases hEq⟩
      · exact nomatch h
  | pushPlace t =>
      simp only [iteCandidate] at h
      split at h
      · next hcc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hcc, fun inner' hEq => by cases hEq⟩
      · exact nomatch h
  | mkCall k ty fn args =>
      simp only [iteCandidate] at h
      split at h
      · next hcc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hcc, fun inner' hEq => by cases hEq⟩
      · exact nomatch h
  | mkBinop op l rr =>
      simp only [iteCandidate] at h
      split at h
      · next hcc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hcc, fun inner' hEq => by cases hEq⟩
      · exact nomatch h
  | mkIncDec op t =>
      simp only [iteCandidate] at h
      split at h
      · next hcc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hcc, fun inner' hEq => by cases hEq⟩
      · exact nomatch h
  | mkTernary c2 t2 e2 =>
      simp only [iteCandidate] at h
      split at h
      · next hcc =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hcc, fun inner' hEq => by cases hEq⟩
      · exact nomatch h

theorem transferCandidate_applies {m : Modality}
    {recipient amount : WrappedExpr} {r : RuleName}
    (h : transferCandidate recipient amount = some r) :
    AppliesTo m (Stmt.transfer recipient amount) r := by
  simp only [transferCandidate] at h
  split at h
  · next hrc => cases Option.some.inj h; exact ⟨by decide, rfl, hrc⟩
  · next hnrc =>
      split at h
      · next hac =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, simple_of_not_complex hnrc, hac⟩
      · next hnac =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, simple_of_not_complex hnrc,
            simple_of_not_complex hnac⟩

/-- The syntactic fragment on which `candidate`'s `some` answers are
trustworthy: the inner target of a `pushPlace` assignment right-hand
side must be storage-kind (see the module docstring — outside this
fragment `candidate` names push rules whose receiver condition fails). -/
def pushRhsStorageB : Stmt -> Bool
  | Stmt.assign _ rhs =>
      match rhs with
      | WrappedExpr.pushPlace t => t.kind == Kind.storage
      | _ => true
  | _ => true

/-- **`candidate` never bluffs** (deliverable 1): a `some rule` answer of
the dispatch function names a rule of the calculus that really applies. -/
theorem candidate_applies {m : Modality} {stmt : Stmt} {r : RuleName}
    (hp : pushRhsStorageB stmt = true)
    (h : UniquenessAux.candidate m stmt = some r) :
    r ∈ Rules.ruleNames ∧
      ((Rules.ruleEffect r).mode stmt).applies m = true ∧
      (Rules.ruleEffect r).cond stmt := by
  cases stmt with
  | expr e => exact exprCandidate_applies h
  | assign lhs rhs =>
      obtain ⟨le, hass⟩ := lhs
      refine assignCandidate_applies hass ?_ h
      intro t hEq
      subst hEq
      simpa [pushRhsStorageB] using hp
  | compoundAssign op lhs rhs =>
      obtain ⟨le, hass⟩ := lhs
      exact compoundAssignCandidate_applies hass h
  | storageDecl ty name init =>
      cases init with
      | none => cases Option.some.inj h; exact ⟨by decide, rfl, rfl⟩
      | some rhs => cases Option.some.inj h; exact ⟨by decide, rfl, rfl⟩
  | storagePlaceAlias ty name init =>
      cases Option.some.inj h
      exact ⟨by decide, rfl, trivial⟩
  | stackDecl ty name init =>
      cases init with
      | none => cases Option.some.inj h; exact ⟨by decide, rfl, rfl⟩
      | some rhs => cases Option.some.inj h; exact ⟨by decide, rfl, rfl⟩
  | memoryDecl ty name init => exact memoryDeclCandidate_applies h
  | «delete» target =>
      obtain ⟨te, hass⟩ := target
      exact deleteCandidate_applies hass h
  | push target value =>
      obtain ⟨te, hass⟩ := target
      exact pushCandidate_applies hass h
  | pushAssign target value =>
      cases Option.some.inj h
      exact ⟨by decide, rfl, trivial⟩
  | pushFieldAssign target fld value =>
      cases Option.some.inj h
      exact ⟨by decide, rfl, trivial⟩
  | pop target =>
      obtain ⟨te, hass⟩ := target
      exact popCandidate_applies hass h
  | «revert» msg =>
      cases m <;> (cases Option.some.inj h; exact ⟨by decide, rfl, trivial⟩)
  | assertStmt c => exact assertCandidate_applies h
  | requireStmt c => exact requireCandidate_applies h
  | ite c thn els => exact iteCandidate_applies h
  | transfer recipient amount => exact transferCandidate_applies h
  | callStmt res fn args =>
      simp only [UniquenessAux.candidate] at h
      split at h
      · next hcap =>
          cases Option.some.inj h
          exact ⟨by decide, rfl, hcap⟩
      · next hncap =>
          split at h
          · next hexp =>
              cases Option.some.inj h
              refine ⟨by decide, rfl, ?_, hexp⟩
              refine all_simple_of_not_any_complex ?_
              rw [<- Rules.captureFirstComplexArg_isSome]
              exact eq_false_of_not_eq_true hncap
          · exact nomatch h

/-- Coverage is equivalent to a `some` answer of the dispatch function
(on the trustworthy fragment). -/
theorem ruleApplies_iff_candidate {m : Modality} {stmt : Stmt}
    (hp : pushRhsStorageB stmt = true) :
    Rules.ruleApplies m stmt ↔
      (UniquenessAux.candidate m stmt).isSome := by
  constructor
  · rintro ⟨rule, hmem, hmode, hcond⟩
    rw [UniquenessAux.applicable_eq_candidate hmem hmode hcond]
    rfl
  · intro hsome
    cases hcand : UniquenessAux.candidate m stmt with
    | none => rw [hcand] at hsome; exact Bool.noConfusion hsome
    | some rule =>
        obtain ⟨h1, h2, h3⟩ := candidate_applies hp hcand
        exact ⟨rule, h1, h2, h3⟩

/-! ## Boolean helpers for the residue characterization -/

theorem eq_false_of_bnot {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact Bool.noConfusion h

theorem bnot_eq_true_of_eq_false {b : Bool} (h : b = false) : (!b) = true := by
  rw [h]; rfl

theorem beq_eq_false_of_ne {α : Type _} [BEq α] [LawfulBEq α] {x y : α}
    (h : ¬ x = y) : (x == y) = false := by
  cases hx : x == y with
  | false => rfl
  | true => exact absurd (eq_of_beq hx) h

theorem not_and_of_andB_eq_false {α β : Type _} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β] {x X : α} {y Y : β}
    (h : ((x == X) && (y == Y)) = false) : ¬ (x = X ∧ y = Y) :=
  fun ⟨h1, h2⟩ => by rw [h1, h2] at h; simp at h

theorem memComplexB_eq_false {e : WrappedExpr}
    (h : ¬ (e.kind = Kind.memory ∧ e.complex = true)) :
    ((e.kind == Kind.memory) && e.complex) = false := by
  cases hk : e.kind == Kind.memory with
  | false => rfl
  | true =>
      cases hc : e.complex with
      | false => rfl
      | true => exact absurd ⟨eq_of_beq hk, hc⟩ h

theorem not_memComplex_of_B_eq_false {e : WrappedExpr}
    (h : ¬ ((e.kind == Kind.memory) && e.complex) = true) :
    ¬ (e.kind = Kind.memory ∧ e.complex = true) :=
  fun ⟨h1, h2⟩ => h (by rw [h1, h2]; rfl)

/-! ## The residue characterization (deliverable 2)

Boolean vocabulary first: each `…OkB` predicate names the family of
shapes the corresponding rule tier *does* support, so a residue
constructor can carry the single fact "the shape is outside the
supported family". -/

/-- Bool-literal conditions (they go to `ifElseTrue`/`ifElseFalse`). -/
def boolLitB : WrappedExpr -> Bool
  | WrappedExpr.bool _ => true
  | _ => false

/-- Targets the *statement-level* `++`/`--` and the compound-assignment
rules support: a stack simple variable, a global storage root, a storage
field, or a storage index with a simple index expression. -/
def compoundTargetOkB (t : WrappedExpr) : Bool :=
  (t.isStack && t.simple) ||
    (match t with
     | WrappedExpr.var Kind.storage _ fld =>
         fld.origin == some StorageOrigin.global
     | WrappedExpr.field Kind.storage _ _ _ => true
     | WrappedExpr.index Kind.storage _ _ index => !index.complex
     -- The memory twins of the two storage rows. There is no memory *root*
     -- row: a memory root is an identity, not a value cell, so `mv += se`
     -- stays residue (the rule set, "Memory-target arithmetic").
     | WrappedExpr.field Kind.memory _ _ _ => true
     | WrappedExpr.index Kind.memory _ _ index => !index.complex
     | _ => false)

/-- Targets the *assignment-form* `v = ++t;` rules support (narrower
than the statement form: the assignment tier has no complex-path unfold
twins). -/
def incDecAssignTargetOkB (t : WrappedExpr) : Bool :=
  (t.isStack && t.simple) ||
    (match t with
     | WrappedExpr.var Kind.storage _ fld =>
         fld.origin == some StorageOrigin.global
     | WrappedExpr.field Kind.storage _ path _ => !path.complex
     | WrappedExpr.index Kind.storage _ path index =>
         !(path.complex || index.complex)
     | WrappedExpr.field Kind.memory _ path _ => !path.complex
     | WrappedExpr.index Kind.memory _ path index =>
         !(path.complex || index.complex)
     | _ => false)

/-- Left-hand sides the `*ValueRhsCapture` trio covers: a global storage
root, a storage field, or a storage index. -/
def valueCaptureLhsOkB : WrappedExpr -> Bool
  | WrappedExpr.var Kind.storage _ fld =>
      fld.origin == some StorageOrigin.global
  | WrappedExpr.field Kind.storage _ _ _ => true
  | WrappedExpr.index Kind.storage _ _ _ => true
  | _ => false

/-- Boolean mirror of `Rules.valueRhsCaptureRhs`: operator right-hand
sides the capture trio claims (an arithmetic operator over simple
operands is excluded — `binopUnfoldResult` owns that cell). -/
def valueRhsCaptureRhsB : WrappedExpr -> Bool
  | WrappedExpr.binop op l r => !(op.isArith && l.simple && r.simple)
  | WrappedExpr.unop _ _ => true
  | WrappedExpr.incDec _ _ => true
  | _ => false

/-- Initializers `T memory x = rhs;` has a rule for: a memory rhs, a
storage field read, or a simple storage root read. -/
def memoryDeclInitOkB (rhs : WrappedExpr) : Bool :=
  rhs.isMemory ||
    (match rhs with
     | WrappedExpr.field Kind.storage _ _ _ => true
     | _ => rhs.isStorage && rhs.simple)

/-- Boolean mirror of the assignment residue, simple-rhs tier (see the
`ResidueShape` constructors for the reading of each arm). -/
def assignSimpleResidueB (le rhs : WrappedExpr) : Bool :=
  match le with
  | WrappedExpr.field Kind.memory _ path _ =>
      !path.complex && rhs.isStorage
  | WrappedExpr.index Kind.memory _ path index =>
      !path.complex && !index.complex && rhs.isStorage
  | WrappedExpr.pushPlace t => !(t.kind == Kind.storage)
  | WrappedExpr.var Kind.storage _ fld =>
      (fld.origin == some StorageOrigin.local) && rhs.isStack
  | WrappedExpr.var Kind.memory _ _ => rhs.isStack
  | WrappedExpr.var Kind.stack _ _ => rhs.isMemory
  | WrappedExpr.field Kind.stack _ _ _ => !rhs.isStorage
  | WrappedExpr.index Kind.stack _ _ _ => !rhs.isStorage
  | _ => false

/-- Boolean mirror of the assignment residue, complex-rhs tier, past
the memory-complex-lhs gate. -/
def assignComplexResidueRhsB (le rhs : WrappedExpr) : Bool :=
  match rhs with
  | WrappedExpr.pushPlace t =>
      !(t.kind == Kind.storage) || (!t.complex && !le.isLocal)
  | WrappedExpr.binop _ _ _ =>
      valueRhsCaptureRhsB rhs && !(le.isStack && le.simple) &&
        !valueCaptureLhsOkB le
  | WrappedExpr.unop _ _ =>
      !(le.isStack && le.simple) && !valueCaptureLhsOkB le
  | WrappedExpr.incDec _ t =>
      if le.isStack && le.simple then !incDecAssignTargetOkB t
      else !valueCaptureLhsOkB le
  | WrappedExpr.ternary c _ _ =>
      !c.complex && !(le.isStack && le.simple) && !le.isStorage
  | Typed.WrappedExpr.mkCall k _ _ _ =>
      !((le.kind == Kind.storage) && (k == Kind.memory))
  | WrappedExpr.field Kind.stack _ _ _ => true
  | WrappedExpr.index Kind.stack _ _ _ => true
  | _ => false

/-- Complex-rhs tier: a memory-complex lhs is always covered
(`memoryWriteUnfoldRightSndResult` and friends). -/
def assignComplexResidueB (le rhs : WrappedExpr) : Bool :=
  if (le.kind == Kind.memory) && le.complex then false
  else assignComplexResidueRhsB le rhs

/-- Boolean mirror of the assignment residue. -/
def assignResidueB (le rhs : WrappedExpr) : Bool :=
  if rhs.simple then assignSimpleResidueB le rhs
  else assignComplexResidueB le rhs

def deleteResidueB : WrappedExpr -> Bool
  | WrappedExpr.var Kind.storage _ fld =>
      !(fld.origin == some StorageOrigin.global)
  | WrappedExpr.pushPlace p => !(p.kind == Kind.storage)
  | _ => false

def pushResidueB (te : WrappedExpr) : Option WrappedExpr -> Bool
  | some rhs =>
      if te.kind == Kind.storage then
        !te.complex && !rhs.complex && rhs.isMemory
      else true
  | none => !(te.kind == Kind.storage)

/-- **The residue** (deliverable 2): an explicit, mode-independent
syntactic characterization of the well-formed statements no rule of the calculus
covers.  One constructor per family; each carries the syntactic
components and the Boolean side conditions that place the statement in
the uncovered cell.  The correspondence with the dispatch function is
`candidate_none_iff_residue`; non-coverage is `residue_not_covered`;
the well-typed dichotomy is `coverage_residue`.

Families (constructors in order):

1. symbolic `if` conditions;
2. bare `++`/`--` statements on unsupported targets (memory places,
   storage *local* roots, complex storage indices, operator artifacts);
3.–4. storage-value writes into memory field/index places
   (`mv.f = se;`, `mv[i] = se;` with a storage rhs);
5. push-place *assignment target* with a non-storage receiver
   (`mv.push() = e;` artifact);
6. stack value into a storage local root (`sp = x;`);
7. stack value into a memory root (`mv = x;`);
8. memory value into a stack variable (`x = mv;`);
9. simple non-storage value into a stack-kind field/index place
   (wt artifact — `wtExpr` does not pin a field's kind);
10. `… = t.push()` with a non-storage receiver (the `candidate`
    overshoot cell, see the module docstring);
11. `… = arr.push()` whose lhs is not a storage-local root;
12. operator rhs whose lhs no capture rule reaches (memory root,
    storage local root, stack place, push place);
13. `v = ++t;` with an unsupported inc/dec target;
14. ternary with simple condition into an unsupported lhs
    (memory root, stack place);
15. call rhs (`v = net(a);`) outside the memory-copy cells;
16. a stack-kind field/index place as rhs (wt artifact, the read twin
    of 9);
17. `**=` (pow has no compound-assignment taclet);
18. compound assignment onto an unsupported target;
19. `T memory x = rhs;` with an unsupported initializer
    (notably a storage *index* read: `Person memory p = people[i];`);
20. `delete` on a storage *local* root;
21. `delete` on a push place with non-storage receiver (artifact;
    unreachable under `stmtWt`, which requires a storage-kind target);
22. `push` on a non-storage receiver (memory arrays; likewise
    unreachable under `stmtWt`);
23. `arr.push(mv)` — pushing a memory value into a storage array;
24. `pop` on a non-storage receiver. -/
inductive ResidueShape : Stmt -> Prop where
  | iteSymbolicCond (cond : WrappedExpr) (thn els : List Stmt)
      (hsimple : cond.simple = true) (hlit : boolLitB cond = false) :
      ResidueShape (Stmt.ite cond thn els)
  | incDecStmt (op : IncDec) (target : WrappedExpr)
      (hbad : compoundTargetOkB target = false) :
      ResidueShape (Stmt.expr (WrappedExpr.incDec op target))
  | assignMemFieldFromStorage (lhs : PlaceExpr) (rhs : WrappedExpr)
      (ty : Ty) (path : WrappedExpr) (fld : Field)
      (hl : lhs.expr = WrappedExpr.field Kind.memory ty path fld)
      (hpath : path.complex = false)
      (hr : rhs.simple = true) (hk : rhs.isStorage = true) :
      ResidueShape (Stmt.assign lhs rhs)
  | assignMemIndexFromStorage (lhs : PlaceExpr) (rhs : WrappedExpr)
      (ty : Ty) (path idx : WrappedExpr)
      (hl : lhs.expr = WrappedExpr.index Kind.memory ty path idx)
      (hpath : path.complex = false) (hidx : idx.complex = false)
      (hr : rhs.simple = true) (hk : rhs.isStorage = true) :
      ResidueShape (Stmt.assign lhs rhs)
  | assignPushPlaceLhsNonStorage (lhs : PlaceExpr) (rhs : WrappedExpr)
      (t : WrappedExpr)
      (hl : lhs.expr = WrappedExpr.pushPlace t)
      (hk : ¬ t.kind = Kind.storage) (hr : rhs.simple = true) :
      ResidueShape (Stmt.assign lhs rhs)
  | assignStorageLocalRootFromStack (lhs : PlaceExpr) (rhs : WrappedExpr)
      (ty : Ty) (fld : Field)
      (hl : lhs.expr = WrappedExpr.var Kind.storage ty fld)
      (horigin : fld.origin = some StorageOrigin.local)
      (hr : rhs.simple = true) (hk : rhs.isStack = true) :
      ResidueShape (Stmt.assign lhs rhs)
  | assignMemoryRootFromStack (lhs : PlaceExpr) (rhs : WrappedExpr)
      (ty : Ty) (fld : Field)
      (hl : lhs.expr = WrappedExpr.var Kind.memory ty fld)
      (hr : rhs.simple = true) (hk : rhs.isStack = true) :
      ResidueShape (Stmt.assign lhs rhs)
  | assignStackVarFromMemory (lhs : PlaceExpr) (rhs : WrappedExpr)
      (ty : Ty) (fld : Field)
      (hl : lhs.expr = WrappedExpr.var Kind.stack ty fld)
      (hr : rhs.simple = true) (hk : rhs.isMemory = true) :
      ResidueShape (Stmt.assign lhs rhs)
  | assignStackPlace (lhs : PlaceExpr) (rhs : WrappedExpr)
      (hshape :
        (∃ ty base fld,
          lhs.expr = WrappedExpr.field Kind.stack ty base fld) ∨
        (∃ ty base idx,
          lhs.expr = WrappedExpr.index Kind.stack ty base idx))
      (hr : rhs.simple = true) (hk : rhs.isStorage = false) :
      ResidueShape (Stmt.assign lhs rhs)
  | assignPushRhsNonStorage (lhs : PlaceExpr) (t : WrappedExpr)
      (hk : ¬ t.kind = Kind.storage)
      (hnm : ¬ (lhs.expr.kind = Kind.memory ∧ lhs.expr.complex = true)) :
      ResidueShape (Stmt.assign lhs (WrappedExpr.pushPlace t))
  | assignPushRhsNonLocalLhs (lhs : PlaceExpr) (t : WrappedExpr)
      (hk : t.kind = Kind.storage) (htc : t.complex = false)
      (hloc : lhs.expr.isLocal = false)
      (hnm : ¬ (lhs.expr.kind = Kind.memory ∧ lhs.expr.complex = true)) :
      ResidueShape (Stmt.assign lhs (WrappedExpr.pushPlace t))
  | assignOperatorRhsBadLhs (lhs : PlaceExpr) (rhs : WrappedExpr)
      (hrhs : valueRhsCaptureRhsB rhs = true)
      (hnsv : (lhs.expr.isStack && lhs.expr.simple) = false)
      (hbad : valueCaptureLhsOkB lhs.expr = false)
      (hnm : ¬ (lhs.expr.kind = Kind.memory ∧ lhs.expr.complex = true)) :
      ResidueShape (Stmt.assign lhs rhs)
  | assignIncDecBadTarget (lhs : PlaceExpr) (op : IncDec)
      (t : WrappedExpr)
      (hsv : (lhs.expr.isStack && lhs.expr.simple) = true)
      (hbad : incDecAssignTargetOkB t = false) :
      ResidueShape (Stmt.assign lhs (WrappedExpr.incDec op t))
  | assignTernaryBadLhs (lhs : PlaceExpr) (c thn els : WrappedExpr)
      (hcs : c.complex = false)
      (hnsv : (lhs.expr.isStack && lhs.expr.simple) = false)
      (hnsto : lhs.expr.isStorage = false)
      (hnm : ¬ (lhs.expr.kind = Kind.memory ∧ lhs.expr.complex = true)) :
      ResidueShape (Stmt.assign lhs (WrappedExpr.ternary c thn els))
  | assignCallRhs (lhs : PlaceExpr) (k : Kind) (ty : Ty) (fn : Name)
      (args : List WrappedExpr)
      (hnm : ¬ (lhs.expr.kind = Kind.memory ∧ lhs.expr.complex = true))
      (hns : ¬ (lhs.expr.kind = Kind.storage ∧ k = Kind.memory)) :
      ResidueShape (Stmt.assign lhs (Typed.WrappedExpr.mkCall k ty fn args))
  | assignStackPlaceRhs (lhs : PlaceExpr) (rhs : WrappedExpr)
      (hshape :
        (∃ ty base fld,
          rhs = WrappedExpr.field Kind.stack ty base fld) ∨
        (∃ ty base idx,
          rhs = WrappedExpr.index Kind.stack ty base idx))
      (hnm : ¬ (lhs.expr.kind = Kind.memory ∧ lhs.expr.complex = true)) :
      ResidueShape (Stmt.assign lhs rhs)
  | compoundAssignPow (lhs : PlaceExpr) (rhs : WrappedExpr) :
      ResidueShape (Stmt.compoundAssign BinOp.pow lhs rhs)
  | compoundAssignBadTarget (op : BinOp) (lhs : PlaceExpr)
      (rhs : WrappedExpr)
      (hca : op.hasCompoundAssign = true)
      (hr : (rhs.isStack && rhs.simple) = true)
      (hbad : compoundTargetOkB lhs.expr = false) :
      ResidueShape (Stmt.compoundAssign op lhs rhs)
  | memoryDeclBadInit (ty : Ty) (name : Name) (rhs : WrappedExpr)
      (hbad : memoryDeclInitOkB rhs = false) :
      ResidueShape (Stmt.memoryDecl ty name (some rhs))
  | deleteStorageLocalRoot (target : PlaceExpr) (ty : Ty) (fld : Field)
      (hl : target.expr = WrappedExpr.var Kind.storage ty fld)
      (hng : (fld.origin == some StorageOrigin.global) = false) :
      ResidueShape (Stmt.delete target)
  | deletePushPlaceNonStorage (target : PlaceExpr) (p : WrappedExpr)
      (hl : target.expr = WrappedExpr.pushPlace p)
      (hk : ¬ p.kind = Kind.storage) :
      ResidueShape (Stmt.delete target)
  | pushNonStorageTarget (target : PlaceExpr) (value : Option WrappedExpr)
      (hk : ¬ target.expr.kind = Kind.storage) :
      ResidueShape (Stmt.push target value)
  | pushMemoryValue (target : PlaceExpr) (rhs : WrappedExpr)
      (hk : target.expr.kind = Kind.storage)
      (htc : target.expr.complex = false)
      (hrc : rhs.complex = false) (hrm : rhs.isMemory = true) :
      ResidueShape (Stmt.push target (some rhs))
  | popNonStorageTarget (target : PlaceExpr)
      (hk : ¬ target.expr.kind = Kind.storage) :
      ResidueShape (Stmt.pop target)

/-- Computable mirror of `ResidueShape`; concrete witnesses go through
`decide`/`native_decide` (see `residueShape_iff_residueShapeB`). -/
def residueShapeB : Stmt -> Bool
  | Stmt.expr (WrappedExpr.incDec _ target) => !compoundTargetOkB target
  | Stmt.assign lhs rhs => assignResidueB lhs.expr rhs
  | Stmt.compoundAssign op lhs rhs =>
      (op == BinOp.pow) ||
        (op.hasCompoundAssign && (rhs.isStack && rhs.simple) &&
          !compoundTargetOkB lhs.expr)
  | Stmt.memoryDecl _ _ (some rhs) => !memoryDeclInitOkB rhs
  | Stmt.delete target => deleteResidueB target.expr
  | Stmt.push target value => pushResidueB target.expr value
  | Stmt.pop target => !(target.expr.kind == Kind.storage)
  | Stmt.ite cond _ _ => cond.simple && !boolLitB cond
  | _ => false

/-! ## `ResidueShape` ↔ `residueShapeB` -/

theorem ne_of_beqB_eq_false {α : Type _} [BEq α] [LawfulBEq α] {x y : α}
    (h : (x == y) = false) : ¬ x = y := fun he => by rw [he] at h; simp at h

theorem kind_mkCall (k : Kind) (t : Ty) (n : Name)
    (args : List WrappedExpr) :
    (Typed.WrappedExpr.mkCall k t n args).kind = k := rfl

theorem simple_mkCall (k : Kind) (t : Ty) (n : Name)
    (args : List WrappedExpr) :
    (Typed.WrappedExpr.mkCall k t n args).simple = false := rfl

theorem complex_mkCall (k : Kind) (t : Ty) (n : Name)
    (args : List WrappedExpr) :
    (Typed.WrappedExpr.mkCall k t n args).complex = true := rfl

attribute [local simp] UniquenessAux.kind_var UniquenessAux.kind_field
  UniquenessAux.kind_index UniquenessAux.kind_pushPlace
  UniquenessAux.kind_bool UniquenessAux.simple_var UniquenessAux.simple_field
  UniquenessAux.simple_index UniquenessAux.simple_pushPlace
  UniquenessAux.simple_bool UniquenessAux.complex_var
  UniquenessAux.complex_field UniquenessAux.complex_index
  UniquenessAux.complex_pushPlace UniquenessAux.complex_bool
  UniquenessAux.isLocal_var UniquenessAux.isGlobal_var
  UniquenessAux.kind_intLit UniquenessAux.kind_binop UniquenessAux.kind_unop
  UniquenessAux.kind_incDec UniquenessAux.simple_intLit
  UniquenessAux.simple_binop UniquenessAux.simple_unop
  UniquenessAux.simple_incDec UniquenessAux.complex_intLit
  UniquenessAux.complex_binop UniquenessAux.complex_unop
  UniquenessAux.complex_incDec UniquenessAux.kind_ternary
  UniquenessAux.simple_ternary UniquenessAux.complex_ternary
  kind_mkCall simple_mkCall complex_mkCall

theorem memComplexB_eq_false_of_stackvar {e : WrappedExpr}
    (h : (e.isStack && e.simple) = true) :
    ((e.kind == Kind.memory) && e.complex) = false := by
  simp only [Bool.and_eq_true] at h
  have hk := kind_of_isStack h.1
  simp [hk]

theorem kindPairB_eq_false {e : WrappedExpr} {k : Kind}
    (h : ¬ (e.kind = Kind.storage ∧ k = Kind.memory)) :
    ((e.kind == Kind.storage) && (k == Kind.memory)) = false := by
  cases h1 : e.kind == Kind.storage with
  | false => rfl
  | true =>
      cases h2 : k == Kind.memory with
      | false => rfl
      | true => exact absurd ⟨eq_of_beq h1, eq_of_beq h2⟩ h

theorem residueShapeB_of_residueShape {stmt : Stmt}
    (h : ResidueShape stmt) : residueShapeB stmt = true := by
  cases h with
  | iteSymbolicCond cond thn els hsimple hlit =>
      simp [residueShapeB, hsimple, hlit]
  | incDecStmt op target hbad =>
      simp [residueShapeB, hbad]
  | assignMemFieldFromStorage lhs rhs ty path fld hl hpath hr hk =>
      simp [residueShapeB, assignResidueB, assignSimpleResidueB, hl, hr,
        hpath, hk]
  | assignMemIndexFromStorage lhs rhs ty path idx hl hpath hidx hr hk =>
      simp [residueShapeB, assignResidueB, assignSimpleResidueB, hl, hr,
        hpath, hidx, hk]
  | assignPushPlaceLhsNonStorage lhs rhs t hl hk hr =>
      simp [residueShapeB, assignResidueB, assignSimpleResidueB, hl, hr,
        beq_eq_false_of_ne hk]
  | assignStorageLocalRootFromStack lhs rhs ty fld hl horigin hr hk =>
      simp [residueShapeB, assignResidueB, assignSimpleResidueB, hl, hr,
        horigin, hk]
  | assignMemoryRootFromStack lhs rhs ty fld hl hr hk =>
      simp [residueShapeB, assignResidueB, assignSimpleResidueB, hl, hr, hk]
  | assignStackVarFromMemory lhs rhs ty fld hl hr hk =>
      simp [residueShapeB, assignResidueB, assignSimpleResidueB, hl, hr, hk]
  | assignStackPlace lhs rhs hshape hr hk =>
      cases hshape with
      | inl hex =>
          obtain ⟨ty, base, fld, hl⟩ := hex
          simp [residueShapeB, assignResidueB, assignSimpleResidueB, hl, hr,
            hk]
      | inr hex =>
          obtain ⟨ty, base, idx, hl⟩ := hex
          simp [residueShapeB, assignResidueB, assignSimpleResidueB, hl, hr,
            hk]
  | assignPushRhsNonStorage lhs t hk hnm =>
      simp [residueShapeB, assignResidueB, assignComplexResidueB,
        assignComplexResidueRhsB, memComplexB_eq_false hnm,
        beq_eq_false_of_ne hk]
  | assignPushRhsNonLocalLhs lhs t hk htc hloc hnm =>
      simp [residueShapeB, assignResidueB, assignComplexResidueB,
        assignComplexResidueRhsB, memComplexB_eq_false hnm, htc, hloc]
  | assignOperatorRhsBadLhs lhs rhs hrhs hnsv hbad hnm =>
      cases rhs with
      | mkBinop op l r =>
          simp [residueShapeB, assignResidueB, assignComplexResidueB,
            assignComplexResidueRhsB, memComplexB_eq_false hnm, hrhs, hnsv,
            hbad]
      | mkUnop op arg =>
          simp [residueShapeB, assignResidueB, assignComplexResidueB,
            assignComplexResidueRhsB, memComplexB_eq_false hnm, hnsv, hbad]
      | mkIncDec op t =>
          simp [residueShapeB, assignResidueB, assignComplexResidueB,
            assignComplexResidueRhsB, memComplexB_eq_false hnm, hnsv, hbad]
      | var k ty fld => exact Bool.noConfusion hrhs
      | field k ty base fld => exact Bool.noConfusion hrhs
      | index k ty base idx => exact Bool.noConfusion hrhs
      | pushPlace t => exact Bool.noConfusion hrhs
      | bool b => exact Bool.noConfusion hrhs
      | intLit ty v => exact Bool.noConfusion hrhs
      | mkCall k ty fn args => exact Bool.noConfusion hrhs
      | mkTernary c t e => exact Bool.noConfusion hrhs
  | assignIncDecBadTarget lhs op t hsv hbad =>
      simp [residueShapeB, assignResidueB, assignComplexResidueB,
        assignComplexResidueRhsB, memComplexB_eq_false_of_stackvar hsv, hsv,
        hbad]
  | assignTernaryBadLhs lhs c thn els hcs hnsv hnsto hnm =>
      simp [residueShapeB, assignResidueB, assignComplexResidueB,
        assignComplexResidueRhsB, memComplexB_eq_false hnm, hcs, hnsv,
        hnsto]
  | assignCallRhs lhs k ty fn args hnm hns =>
      simp [residueShapeB, assignResidueB, assignComplexResidueB,
        assignComplexResidueRhsB, memComplexB_eq_false hnm,
        kindPairB_eq_false hns]
  | assignStackPlaceRhs lhs rhs hshape hnm =>
      cases hshape with
      | inl hex =>
          obtain ⟨ty, base, fld, hrx⟩ := hex
          simp [residueShapeB, assignResidueB, assignComplexResidueB,
            assignComplexResidueRhsB, hrx, memComplexB_eq_false hnm]
      | inr hex =>
          obtain ⟨ty, base, idx, hrx⟩ := hex
          simp [residueShapeB, assignResidueB, assignComplexResidueB,
            assignComplexResidueRhsB, hrx, memComplexB_eq_false hnm]
  | compoundAssignPow lhs rhs =>
      simp [residueShapeB]
  | compoundAssignBadTarget op lhs rhs hca hr hbad =>
      simp [residueShapeB, hca, hr, hbad]
  | memoryDeclBadInit ty name rhs hbad =>
      simp [residueShapeB, hbad]
  | deleteStorageLocalRoot target ty fld hl hng =>
      simp [residueShapeB, deleteResidueB, hl, hng]
  | deletePushPlaceNonStorage target p hl hk =>
      simp [residueShapeB, deleteResidueB, hl, beq_eq_false_of_ne hk]
  | pushNonStorageTarget target value hk =>
      cases value with
      | none => simp [residueShapeB, pushResidueB, beq_eq_false_of_ne hk]
      | some rhs => simp [residueShapeB, pushResidueB, beq_eq_false_of_ne hk]
  | pushMemoryValue target rhs hk htc hrc hrm =>
      simp [residueShapeB, pushResidueB, hk, htc, hrc, hrm]
  | popNonStorageTarget target hk =>
      simp [residueShapeB, beq_eq_false_of_ne hk]

theorem residueShape_of_residueShapeB {stmt : Stmt}
    (hb : residueShapeB stmt = true) : ResidueShape stmt := by
  cases stmt with
  | expr e =>
      cases e with
      | mkIncDec op target =>
          exact ResidueShape.incDecStmt op target (eq_false_of_bnot hb)
      | var k ty fld => exact Bool.noConfusion hb
      | field k ty base fld => exact Bool.noConfusion hb
      | index k ty base idx => exact Bool.noConfusion hb
      | pushPlace t => exact Bool.noConfusion hb
      | bool b => exact Bool.noConfusion hb
      | intLit ty v => exact Bool.noConfusion hb
      | mkCall k ty fn args => exact Bool.noConfusion hb
      | mkBinop op l r => exact Bool.noConfusion hb
      | mkUnop op arg => exact Bool.noConfusion hb
      | mkTernary c t e => exact Bool.noConfusion hb
  | assign lhs rhs =>
      have hb' : assignResidueB lhs.expr rhs = true := hb
      rw [assignResidueB.eq_def] at hb'
      split at hb'
      · next hs =>
          rw [assignSimpleResidueB.eq_def] at hb'
          split at hb'
          · next ty path fld heq =>
              simp only [Bool.and_eq_true] at hb'
              exact ResidueShape.assignMemFieldFromStorage _ rhs ty path fld
                heq (eq_false_of_bnot hb'.1) hs hb'.2
          · next ty path idx heq =>
              simp only [Bool.and_eq_true] at hb'
              exact ResidueShape.assignMemIndexFromStorage _ rhs ty path idx
                heq (eq_false_of_bnot hb'.1.1) (eq_false_of_bnot hb'.1.2)
                hs hb'.2
          · next t heq =>
              exact ResidueShape.assignPushPlaceLhsNonStorage _ rhs t heq
                (ne_of_beqB_eq_false (eq_false_of_bnot hb')) hs
          · next ty fld heq =>
              simp only [Bool.and_eq_true] at hb'
              exact ResidueShape.assignStorageLocalRootFromStack _ rhs ty fld
                heq (eq_of_beq hb'.1) hs hb'.2
          · next ty fld heq =>
              exact ResidueShape.assignMemoryRootFromStack _ rhs ty fld heq
                hs hb'
          · next ty fld heq =>
              exact ResidueShape.assignStackVarFromMemory _ rhs ty fld heq
                hs hb'
          · next ty base fld heq =>
              exact ResidueShape.assignStackPlace _ rhs
                (Or.inl ⟨ty, base, fld, heq⟩) hs (eq_false_of_bnot hb')
          · next ty base idx heq =>
              exact ResidueShape.assignStackPlace _ rhs
                (Or.inr ⟨ty, base, idx, heq⟩) hs (eq_false_of_bnot hb')
          · exact Bool.noConfusion hb'
      · next hns =>
          rw [assignComplexResidueB.eq_def] at hb'
          split at hb'
          · exact Bool.noConfusion hb'
          · next hnmB =>
              have hnm := not_memComplex_of_B_eq_false hnmB
              rw [assignComplexResidueRhsB.eq_def] at hb'
              split at hb'
              · next t =>
                  cases hkb : t.kind == Kind.storage with
                  | false =>
                      exact ResidueShape.assignPushRhsNonStorage _ t
                        (ne_of_beqB_eq_false hkb) hnm
                  | true =>
                      rw [hkb] at hb'
                      simp only [Bool.not_true, Bool.false_or,
                        Bool.and_eq_true] at hb'
                      exact ResidueShape.assignPushRhsNonLocalLhs _ t
                        (eq_of_beq hkb) (eq_false_of_bnot hb'.1)
                        (eq_false_of_bnot hb'.2) hnm
              · next op l r =>
                  simp only [Bool.and_eq_true] at hb'
                  exact ResidueShape.assignOperatorRhsBadLhs _ _
                    hb'.1.1 (eq_false_of_bnot hb'.1.2)
                    (eq_false_of_bnot hb'.2) hnm
              · next op arg =>
                  simp only [Bool.and_eq_true] at hb'
                  exact ResidueShape.assignOperatorRhsBadLhs _ _
                    rfl (eq_false_of_bnot hb'.1) (eq_false_of_bnot hb'.2)
                    hnm
              · next op t =>
                  split at hb'
                  · next hsv =>
                      exact ResidueShape.assignIncDecBadTarget _ op t hsv
                        (eq_false_of_bnot hb')
                  · next hnsv =>
                      exact ResidueShape.assignOperatorRhsBadLhs _ _
                        rfl (eq_false_of_not_eq_true hnsv)
                        (eq_false_of_bnot hb') hnm
              · next c thn els =>
                  simp only [Bool.and_eq_true] at hb'
                  exact ResidueShape.assignTernaryBadLhs _ c thn els
                    (eq_false_of_bnot hb'.1.1) (eq_false_of_bnot hb'.1.2)
                    (eq_false_of_bnot hb'.2) hnm
              · next k ty fn args =>
                  exact ResidueShape.assignCallRhs _ k ty fn args hnm
                    (not_and_of_andB_eq_false (eq_false_of_bnot hb'))
              · next ty base fld =>
                  exact ResidueShape.assignStackPlaceRhs _ _
                    (Or.inl ⟨ty, base, fld, rfl⟩) hnm
              · next ty base idx =>
                  exact ResidueShape.assignStackPlaceRhs _ _
                    (Or.inr ⟨ty, base, idx, rfl⟩) hnm
              · exact Bool.noConfusion hb'
  | compoundAssign op lhs rhs =>
      have hb' : ((op == BinOp.pow) ||
          (op.hasCompoundAssign && (rhs.isStack && rhs.simple) &&
            !compoundTargetOkB lhs.expr)) = true := hb
      simp only [Bool.or_eq_true] at hb'
      cases hb' with
      | inl hpow =>
          have hop := eq_of_beq hpow
          subst hop
          exact ResidueShape.compoundAssignPow _ _
      | inr hrest =>
          simp only [Bool.and_eq_true] at hrest
          exact ResidueShape.compoundAssignBadTarget op _ rhs hrest.1.1
            (and_true_of hrest.1.2.1 hrest.1.2.2)
            (eq_false_of_bnot hrest.2)
  | memoryDecl ty name init =>
      cases init with
      | none => exact Bool.noConfusion hb
      | some rhs =>
          exact ResidueShape.memoryDeclBadInit ty name rhs
            (eq_false_of_bnot hb)
  | «delete» target =>
      have hb' : deleteResidueB target.expr = true := hb
      rw [deleteResidueB.eq_def] at hb'
      split at hb'
      · next ty fld heq =>
          exact ResidueShape.deleteStorageLocalRoot _ ty fld heq
            (eq_false_of_bnot hb')
      · next p heq =>
          exact ResidueShape.deletePushPlaceNonStorage _ p heq
            (ne_of_beqB_eq_false (eq_false_of_bnot hb'))
      · exact Bool.noConfusion hb'
  | push target value =>
      have hb' : pushResidueB target.expr value = true := hb
      cases value with
      | none =>
          exact ResidueShape.pushNonStorageTarget _ none
            (ne_of_beqB_eq_false (eq_false_of_bnot hb'))
      | some rhs =>
          simp only [pushResidueB] at hb'
          split at hb'
          · next hkb =>
              simp only [Bool.and_eq_true] at hb'
              exact ResidueShape.pushMemoryValue _ rhs (eq_of_beq hkb)
                (eq_false_of_bnot hb'.1.1) (eq_false_of_bnot hb'.1.2)
                hb'.2
          · next hnkb =>
              refine ResidueShape.pushNonStorageTarget _ (some rhs) ?_
              intro he
              exact hnkb (by rw [he]; rfl)
  | pop target =>
      refine ResidueShape.popNonStorageTarget _ ?_
      exact ne_of_beqB_eq_false (eq_false_of_bnot hb)
  | ite cond thn els =>
      have hb' : (cond.simple && !boolLitB cond) = true := hb
      simp only [Bool.and_eq_true] at hb'
      exact ResidueShape.iteSymbolicCond cond thn els hb'.1
        (eq_false_of_bnot hb'.2)
  | storageDecl ty name init => exact Bool.noConfusion hb
  | storagePlaceAlias ty name init => exact Bool.noConfusion hb
  | stackDecl ty name init => exact Bool.noConfusion hb
  | pushAssign target value => exact Bool.noConfusion hb
  | pushFieldAssign target fld value => exact Bool.noConfusion hb
  | «revert» msg => exact Bool.noConfusion hb
  | assertStmt c => exact Bool.noConfusion hb
  | requireStmt c => exact Bool.noConfusion hb
  | transfer recipient amount => exact Bool.noConfusion hb
  | callStmt res fn args => exact Bool.noConfusion hb

/-- The residue characterization is decidable: `ResidueShape` and its
Boolean mirror agree (concrete witnesses go through `decide`). -/
theorem residueShape_iff_residueShapeB {stmt : Stmt} :
    ResidueShape stmt ↔ residueShapeB stmt = true :=
  ⟨residueShapeB_of_residueShape, residueShape_of_residueShapeB⟩

/-! ## From residue shapes to the dispatch function -/

theorem or_false_left {a b : Bool} (h : (a || b) = false) : a = false := by
  cases a with
  | false => rfl
  | true => exact Bool.noConfusion h

theorem or_false_right {a b : Bool} (h : (a || b) = false) : b = false := by
  cases a with
  | false => exact h
  | true => exact Bool.noConfusion h

theorem eq_true_of_bnot_false {b : Bool} (h : (!b) = false) : b = true := by
  cases b with
  | true => rfl
  | false => exact Bool.noConfusion h

theorem not_memComplex_of_stackvar {e : WrappedExpr}
    (h : (e.isStack && e.simple) = true) :
    ¬ (e.kind = Kind.memory ∧ e.complex = true) := by
  simp only [Bool.and_eq_true] at h
  intro hx
  rw [kind_of_isStack h.1] at hx
  exact Kind.noConfusion hx.1

theorem simple_eq_false_of_captureRhs {rhs : WrappedExpr}
    (h : valueRhsCaptureRhsB rhs = true) : rhs.simple = false := by
  cases rhs <;> first | rfl | exact Bool.noConfusion h

theorem valueRhsCaptureCandidate_none {le : WrappedExpr}
    (h : valueCaptureLhsOkB le = false) :
    valueRhsCaptureCandidate le = none := by
  cases le with
  | var k ty fld =>
      cases k with
      | storage =>
          have h' : (fld.origin == some StorageOrigin.global) = false := h
          simp [valueRhsCaptureCandidate, ne_of_beqB_eq_false h']
      | memory => rfl
      | stack => rfl
  | field k ty base fld =>
      cases k with
      | storage => exact Bool.noConfusion h
      | memory => rfl
      | stack => rfl
  | index k ty base idx =>
      cases k with
      | storage => exact Bool.noConfusion h
      | memory => rfl
      | stack => rfl
  | pushPlace t => rfl
  | bool b => rfl
  | intLit t v => rfl
  | mkCall k t n args => rfl
  | mkBinop op l r => rfl
  | mkUnop op a => rfl
  | mkIncDec op t => rfl
  | mkTernary c t e => rfl

theorem assignComplexCandidate_operator_none {m : Modality}
    {le rhs : WrappedExpr}
    (hrhs : valueRhsCaptureRhsB rhs = true)
    (hnsv : (le.isStack && le.simple) = false)
    (hbad : valueCaptureLhsOkB le = false)
    (hnm : ¬ (le.kind = Kind.memory ∧ le.complex = true)) :
    assignComplexCandidate m le rhs = none := by
  cases rhs with
  | mkBinop op l r =>
      simp [assignComplexCandidate, hnm, hnsv, Typed.WrappedExpr.isMemory,
        eq_false_of_bnot hrhs, valueRhsCaptureCandidate_none hbad]
  | mkUnop op arg =>
      simp [assignComplexCandidate, hnm, hnsv, Typed.WrappedExpr.isMemory,
        valueRhsCaptureCandidate_none hbad]
  | mkIncDec op t =>
      simp [assignComplexCandidate, hnm, hnsv, Typed.WrappedExpr.isMemory,
        valueRhsCaptureCandidate_none hbad]
  | var k ty fld => exact Bool.noConfusion hrhs
  | field k ty base fld => exact Bool.noConfusion hrhs
  | index k ty base idx => exact Bool.noConfusion hrhs
  | pushPlace t => exact Bool.noConfusion hrhs
  | bool b => exact Bool.noConfusion hrhs
  | intLit ty v => exact Bool.noConfusion hrhs
  | mkCall k ty fn args => exact Bool.noConfusion hrhs
  | mkTernary c t e => exact Bool.noConfusion hrhs

theorem assignComplexCandidate_incDec_none {m : Modality}
    {le : WrappedExpr} {op : IncDec} {t : WrappedExpr}
    (hsv : (le.isStack && le.simple) = true)
    (hbad : incDecAssignTargetOkB t = false) :
    assignComplexCandidate m le (WrappedExpr.incDec op t) = none := by
  have hnm := not_memComplex_of_stackvar hsv
  unfold incDecAssignTargetOkB at hbad
  have htsv := or_false_left hbad
  have hrest := or_false_right hbad
  cases t with
  | var k ty fld =>
      cases k with
      | storage =>
          have h' : (fld.origin == some StorageOrigin.global) = false := hrest
          have hts : (WrappedExpr.var Kind.storage ty fld).isStack = false :=
            rfl
          simp [assignComplexCandidate, hnm, hsv, hts,
            Typed.WrappedExpr.isMemory, ne_of_beqB_eq_false h']
      | memory =>
          have hts : (WrappedExpr.var Kind.memory ty fld).isStack = false :=
            rfl
          simp [assignComplexCandidate, hnm, hsv, hts,
            Typed.WrappedExpr.isMemory]
      | stack => exact Bool.noConfusion htsv
  | field k ty path fld =>
      cases k with
      | storage =>
          have h' : (!path.complex) = false := hrest
          have hpc : path.complex = true := eq_true_of_bnot_false h'
          simp [assignComplexCandidate, hnm, hsv, hpc,
            Typed.WrappedExpr.isMemory]
      | memory =>
          have h' : (!path.complex) = false := hrest
          have hpc : path.complex = true := eq_true_of_bnot_false h'
          simp [assignComplexCandidate, hnm, hsv, hpc,
            Typed.WrappedExpr.isMemory]
      | stack =>
          simp [assignComplexCandidate, hnm, hsv,
            Typed.WrappedExpr.isMemory]
  | index k ty path idx =>
      cases k with
      | storage =>
          have h' : (!(path.complex || idx.complex)) = false := hrest
          have hpc : (path.complex || idx.complex) = true :=
            eq_true_of_bnot_false h'
          simp [assignComplexCandidate, hnm, hsv, hpc,
            Typed.WrappedExpr.isMemory]
      | memory =>
          have h' : (!(path.complex || idx.complex)) = false := hrest
          have hpc : (path.complex || idx.complex) = true :=
            eq_true_of_bnot_false h'
          simp [assignComplexCandidate, hnm, hsv, hpc,
            Typed.WrappedExpr.isMemory]
      | stack =>
          simp [assignComplexCandidate, hnm, hsv,
            Typed.WrappedExpr.isMemory]
  | pushPlace p =>
      simp [assignComplexCandidate, hnm, hsv, Typed.WrappedExpr.isMemory]
  | bool b => exact Bool.noConfusion htsv
  | intLit ty v => exact Bool.noConfusion htsv
  | mkCall k ty fn args =>
      simp [assignComplexCandidate, hnm, hsv, Typed.WrappedExpr.isMemory]
  | mkBinop op2 l r =>
      simp [assignComplexCandidate, hnm, hsv, Typed.WrappedExpr.isMemory]
  | mkUnop op2 arg =>
      simp [assignComplexCandidate, hnm, hsv, Typed.WrappedExpr.isMemory]
  | mkIncDec op2 t2 =>
      simp [assignComplexCandidate, hnm, hsv, Typed.WrappedExpr.isMemory]
  | mkTernary c t2 e2 =>
      simp [assignComplexCandidate, hnm, hsv, Typed.WrappedExpr.isMemory]

theorem compoundAssignCandidate_none {op : BinOp} {le rhs : WrappedExpr}
    (hr : (rhs.isStack && rhs.simple) = true)
    (hbad : compoundTargetOkB le = false) :
    compoundAssignCandidate op le rhs = none := by
  by_cases hca : op.hasCompoundAssign = true
  case neg => simp [compoundAssignCandidate, hca]
  unfold compoundTargetOkB at hbad
  have hsv := or_false_left hbad
  have hrest := or_false_right hbad
  cases le with
  | var k ty fld =>
      cases k with
      | storage =>
          have h' : (fld.origin == some StorageOrigin.global) = false := hrest
          have hts : (WrappedExpr.var Kind.storage ty fld).isStack = false :=
            rfl
          simp [compoundAssignCandidate, hca, hr, hts,
            ne_of_beqB_eq_false h']
      | memory =>
          have hts : (WrappedExpr.var Kind.memory ty fld).isStack = false :=
            rfl
          simp [compoundAssignCandidate, hca, hr, hts]
      | stack => exact Bool.noConfusion hsv
  | field k ty path fld =>
      cases k with
      | storage => exact Bool.noConfusion hrest
      | memory => exact Bool.noConfusion hrest
      | stack => simp [compoundAssignCandidate, hca, hr, hsv]
  | index k ty path idx =>
      cases k with
      | storage =>
          have h' : (!idx.complex) = false := hrest
          have hic : idx.complex = true := eq_true_of_bnot_false h'
          simp [compoundAssignCandidate, hca, hr, hsv, hic]
      | memory =>
          have h' : (!idx.complex) = false := hrest
          have hic : idx.complex = true := eq_true_of_bnot_false h'
          simp [compoundAssignCandidate, hca, hr, hsv, hic]
      | stack => simp [compoundAssignCandidate, hca, hr, hsv]
  | pushPlace t => simp [compoundAssignCandidate, hca, hr, hsv]
  | bool b => exact Bool.noConfusion hsv
  | intLit ty v => exact Bool.noConfusion hsv
  | mkCall k ty fn args => simp [compoundAssignCandidate, hca, hr, hsv]
  | mkBinop op2 l r => simp [compoundAssignCandidate, hca, hr, hsv]
  | mkUnop op2 arg => simp [compoundAssignCandidate, hca, hr, hsv]
  | mkIncDec op2 t => simp [compoundAssignCandidate, hca, hr, hsv]
  | mkTernary c t e => simp [compoundAssignCandidate, hca, hr, hsv]

theorem memoryDeclCandidate_none {rhs : WrappedExpr}
    (hbad : memoryDeclInitOkB rhs = false) :
    memoryDeclCandidate (some rhs) = none := by
  unfold memoryDeclInitOkB at hbad
  have hnmem := or_false_left hbad
  have hrest := or_false_right hbad
  cases rhs with
  | var k ty fld =>
      cases k with
      | storage => exact Bool.noConfusion hrest
      | memory => exact Bool.noConfusion hnmem
      | stack =>
          simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.isStorage,
            Typed.WrappedExpr.kind]
  | field k ty base fld =>
      cases k with
      | storage => exact Bool.noConfusion hrest
      | memory => exact Bool.noConfusion hnmem
      | stack =>
          simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.isStorage,
            Typed.WrappedExpr.kind]
  | index k ty base idx =>
      cases k with
      | storage =>
          simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.simple]
      | memory => exact Bool.noConfusion hnmem
      | stack =>
          simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.isStorage,
            Typed.WrappedExpr.kind]
  | pushPlace t =>
      simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.simple]
  | bool b =>
      simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.isStorage,
        Typed.WrappedExpr.kind]
  | intLit ty v =>
      simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.isStorage,
        Typed.WrappedExpr.kind]
  | mkCall k ty fn args =>
      cases k with
      | memory => exact Bool.noConfusion hnmem
      | storage =>
          simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.simple]
      | stack =>
          simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.isStorage,
            Typed.WrappedExpr.kind]
  | mkBinop op l r =>
      simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.isStorage,
        Typed.WrappedExpr.kind]
  | mkUnop op arg =>
      simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.isStorage,
        Typed.WrappedExpr.kind]
  | mkIncDec op t =>
      simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.isStorage,
        Typed.WrappedExpr.kind]
  | mkTernary c t e =>
      simp [memoryDeclCandidate, hnmem, Typed.WrappedExpr.isStorage,
        Typed.WrappedExpr.kind]

theorem incDecStmtCandidate_none {op : IncDec} {t : WrappedExpr}
    (hbad : compoundTargetOkB t = false) :
    incDecStmtCandidate op t = none := by
  unfold compoundTargetOkB at hbad
  have hsv := or_false_left hbad
  have hrest := or_false_right hbad
  cases t with
  | var k ty fld =>
      cases k with
      | storage =>
          have h' : (fld.origin == some StorageOrigin.global) = false := hrest
          have hts : (WrappedExpr.var Kind.storage ty fld).isStack = false :=
            rfl
          simp [incDecStmtCandidate, hts, ne_of_beqB_eq_false h']
      | memory =>
          have hts : (WrappedExpr.var Kind.memory ty fld).isStack = false :=
            rfl
          simp [incDecStmtCandidate, hts]
      | stack => exact Bool.noConfusion hsv
  | field k ty path fld =>
      cases k with
      | storage => exact Bool.noConfusion hrest
      | memory => exact Bool.noConfusion hrest
      | stack => simp [incDecStmtCandidate, hsv]
  | index k ty path idx =>
      cases k with
      | storage =>
          have h' : (!idx.complex) = false := hrest
          have hic : idx.complex = true := eq_true_of_bnot_false h'
          simp [incDecStmtCandidate, hsv, hic]
      | memory =>
          have h' : (!idx.complex) = false := hrest
          have hic : idx.complex = true := eq_true_of_bnot_false h'
          simp [incDecStmtCandidate, hsv, hic]
      | stack => simp [incDecStmtCandidate, hsv]
  | pushPlace p => simp [incDecStmtCandidate, hsv]
  | bool b => exact Bool.noConfusion hsv
  | intLit ty v => exact Bool.noConfusion hsv
  | mkCall k ty fn args => simp [incDecStmtCandidate, hsv]
  | mkBinop op2 l r => simp [incDecStmtCandidate, hsv]
  | mkUnop op2 arg => simp [incDecStmtCandidate, hsv]
  | mkIncDec op2 t2 => simp [incDecStmtCandidate, hsv]
  | mkTernary c t2 e2 => simp [incDecStmtCandidate, hsv]

theorem iteCandidate_none {cond : WrappedExpr}
    (hsimple : cond.simple = true) (hlit : boolLitB cond = false) :
    iteCandidate cond = none := by
  cases cond with
  | var k ty fld => simp [iteCandidate]
  | intLit ty v => simp [iteCandidate]
  | bool b => exact Bool.noConfusion hlit
  | field k ty base fld => exact Bool.noConfusion hsimple
  | index k ty base idx => exact Bool.noConfusion hsimple
  | pushPlace t => exact Bool.noConfusion hsimple
  | mkCall k ty fn args => exact Bool.noConfusion hsimple
  | mkBinop op l r => exact Bool.noConfusion hsimple
  | mkUnop op arg => exact Bool.noConfusion hsimple
  | mkIncDec op t => exact Bool.noConfusion hsimple
  | mkTernary c t e => exact Bool.noConfusion hsimple

/-- Where the dispatch function sends each residue shape: `none`, except
on the `assignPushRhsNonStorage` cell, whose data is returned explicitly
(see the module docstring). -/
theorem residue_dispatch {m : Modality} {stmt : Stmt}
    (h : ResidueShape stmt) :
    UniquenessAux.candidate m stmt = none ∨
      ∃ (lhs : PlaceExpr) (t : WrappedExpr),
        stmt = Stmt.assign lhs (WrappedExpr.pushPlace t) ∧
          ¬ t.kind = Kind.storage ∧
          ¬ (lhs.expr.kind = Kind.memory ∧ lhs.expr.complex = true) := by
  cases h with
  | assignPushRhsNonStorage lhs t hk hnm =>
      exact Or.inr ⟨lhs, t, rfl, hk, hnm⟩
  | iteSymbolicCond cond thn els hsimple hlit =>
      exact Or.inl (by
        simpa [UniquenessAux.candidate] using iteCandidate_none hsimple hlit)
  | incDecStmt op target hbad =>
      exact Or.inl (by
        simpa [UniquenessAux.candidate, exprCandidate] using
          incDecStmtCandidate_none (op := op) hbad)
  | assignMemFieldFromStorage lhs rhs ty path fld hl hpath hr hk =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr, hl,
        assignCandidate, assignSimpleCandidate, hr, hpath,
        isMemory_eq_false_of_isStorage hk, isStack_eq_false_of_isStorage hk]
  | assignMemIndexFromStorage lhs rhs ty path idx hl hpath hidx hr hk =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr, hl,
        assignCandidate, assignSimpleCandidate, hr, hpath, hidx,
        isMemory_eq_false_of_isStorage hk, isStack_eq_false_of_isStorage hk]
  | assignPushPlaceLhsNonStorage lhs rhs t hl hk hr =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr, hl,
        assignCandidate, assignSimpleCandidate, hr, hk]
  | assignStorageLocalRootFromStack lhs rhs ty fld hl horigin hr hk =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr, hl,
        assignCandidate, assignSimpleCandidate, hr, horigin,
        isStorage_eq_false_of_isStack hk, isMemory_eq_false_of_isStack hk]
  | assignMemoryRootFromStack lhs rhs ty fld hl hr hk =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr, hl,
        assignCandidate, assignSimpleCandidate, hr,
        isStorage_eq_false_of_isStack hk, isMemory_eq_false_of_isStack hk]
  | assignStackVarFromMemory lhs rhs ty fld hl hr hk =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr, hl,
        assignCandidate, assignSimpleCandidate, hr,
        isStorage_eq_false_of_isMemory hk, isStack_eq_false_of_isMemory hk]
  | assignStackPlace lhs rhs hshape hr hk =>
      refine Or.inl ?_
      cases hshape with
      | inl hex =>
          obtain ⟨ty, base, fld, hl⟩ := hex
          simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr, hl,
            assignCandidate, assignSimpleCandidate, hr, hk,
            Typed.WrappedExpr.isStack]
      | inr hex =>
          obtain ⟨ty, base, idx, hl⟩ := hex
          simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr, hl,
            assignCandidate, assignSimpleCandidate, hr, hk,
            Typed.WrappedExpr.isStack]
  | assignPushRhsNonLocalLhs lhs t hk htc hloc hnm =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr,
        assignCandidate, assignComplexCandidate, hnm, htc, hloc,
        Typed.WrappedExpr.isMemory]
  | assignOperatorRhsBadLhs lhs rhs hrhs hnsv hbad hnm =>
      exact Or.inl (by
        simpa [UniquenessAux.candidate, UniquenessAux.coe_eq_expr,
          assignCandidate, simple_eq_false_of_captureRhs hrhs] using
          assignComplexCandidate_operator_none (m := m) hrhs hnsv hbad hnm)
  | assignIncDecBadTarget lhs op t hsv hbad =>
      exact Or.inl (by
        simpa [UniquenessAux.candidate, UniquenessAux.coe_eq_expr,
          assignCandidate] using
          assignComplexCandidate_incDec_none (m := m) (op := op) hsv hbad)
  | assignTernaryBadLhs lhs c thn els hcs hnsv hnsto hnm =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr,
        assignCandidate, assignComplexCandidate, hnm, hcs, hnsv, hnsto,
        Typed.WrappedExpr.isMemory]
  | assignCallRhs lhs k ty fn args hnm hns =>
      refine Or.inl ?_
      have hcond : ¬ (lhs.expr.kind = Kind.storage ∧
          (Typed.WrappedExpr.mkCall k ty fn args).isMemory = true) := by
        intro hx
        refine hns ⟨hx.1, ?_⟩
        have h2 := hx.2
        simpa [Typed.WrappedExpr.isMemory, kind_mkCall] using h2
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr,
        assignCandidate, assignComplexCandidate, hnm, hcond]
  | assignStackPlaceRhs lhs rhs hshape hnm =>
      refine Or.inl ?_
      cases hshape with
      | inl hex =>
          obtain ⟨ty, base, fld, hrx⟩ := hex
          simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr, hrx,
            assignCandidate, assignComplexCandidate, hnm,
            Typed.WrappedExpr.isMemory]
      | inr hex =>
          obtain ⟨ty, base, idx, hrx⟩ := hex
          simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr, hrx,
            assignCandidate, assignComplexCandidate, hnm,
            Typed.WrappedExpr.isMemory]
  | compoundAssignPow lhs rhs =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, compoundAssignCandidate,
        BinOp.hasCompoundAssign]
  | compoundAssignBadTarget op lhs rhs hca hr hbad =>
      exact Or.inl (by
        simpa [UniquenessAux.candidate, UniquenessAux.coe_eq_expr] using
          compoundAssignCandidate_none (op := op) hr hbad)
  | memoryDeclBadInit ty name rhs hbad =>
      exact Or.inl (by
        simpa [UniquenessAux.candidate] using memoryDeclCandidate_none hbad)
  | deleteStorageLocalRoot target ty fld hl hng =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr, hl,
        deleteCandidate, ne_of_beqB_eq_false hng]
  | deletePushPlaceNonStorage target p hl hk =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr, hl,
        deleteCandidate, hk]
  | pushNonStorageTarget target value hk =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr,
        pushCandidate, hk]
  | pushMemoryValue target rhs hk htc hrc hrm =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr,
        pushCandidate, hk, htc, hrc,
        isStorage_eq_false_of_isMemory hrm, isStack_eq_false_of_isMemory hrm]
  | popNonStorageTarget target hk =>
      refine Or.inl ?_
      simp [UniquenessAux.candidate, UniquenessAux.coe_eq_expr,
        popCandidate, hk]

/-! ## Well-typedness facts feeding the coverage dichotomy -/

/-- A well-annotated storage variable is Γ-tracked (`origin = local`) or
layout-rooted (`origin = global`) — `origin = none` never typechecks. -/
theorem wt_storageVar_origin {Γ : Semantics.Ctx} {L : Semantics.Layout}
    {ty : Ty} {fld : Field}
    (h : Semantics.wtExpr Γ L (WrappedExpr.var Kind.storage ty fld) = true) :
    fld.origin = some StorageOrigin.local ∨
      fld.origin = some StorageOrigin.global := by
  simp only [Semantics.wtExpr] at h
  split at h
  · next ty' =>
      simp only [Bool.and_eq_true] at h
      exact Or.inl (eq_of_beq h.2)
  · exact Bool.noConfusion h
  · simp only [Bool.and_eq_true] at h
    exact Or.inr (eq_of_beq h.1)

/-- A well-annotated index expression has a container base: `elemTy`
succeeds only on arrays and mappings. -/
theorem wt_index_container {Γ : Semantics.Ctx} {L : Semantics.Layout}
    {k : Kind} {ty : Ty} {base index : WrappedExpr}
    (h : Semantics.wtExpr Γ L (WrappedExpr.index k ty base index) = true) :
    arrayTyB base = true ∨ mappingTyB base = true := by
  simp only [Semantics.wtExpr, Bool.and_eq_true] at h
  have helem := eq_of_beq h.2
  unfold arrayTyB mappingTyB
  cases hbt : base.ty with
  | prim p => rw [hbt] at helem; exact Option.noConfusion helem
  | ref rt =>
      cases rt with
      | struct s => rw [hbt] at helem; exact Option.noConfusion helem
      | array e => exact Or.inl rfl
      | mapping kt vt => exact Or.inr rfl

/-! ## Default-arm helpers for the coverage traversal -/

theorem compoundTargetOkB_eq_false_default {t : WrappedExpr}
    (hnt : ¬ (t.isStack && t.simple) = true)
    (h1 : ∀ ty fld, t = WrappedExpr.var Kind.storage ty fld -> False)
    (h2 : ∀ ty path fld,
      t = WrappedExpr.field Kind.storage ty path fld -> False)
    (h3 : ∀ ty path idx,
      t = WrappedExpr.index Kind.storage ty path idx -> False)
    (h4 : ∀ ty path fld,
      t = WrappedExpr.field Kind.memory ty path fld -> False)
    (h5 : ∀ ty path idx,
      t = WrappedExpr.index Kind.memory ty path idx -> False) :
    compoundTargetOkB t = false := by
  cases t with
  | var k ty fld =>
      cases k with
      | storage => exact absurd rfl (h1 ty fld)
      | memory => rfl
      | stack => exact absurd rfl hnt
  | field k ty path fld =>
      cases k with
      | storage => exact absurd rfl (h2 ty path fld)
      | memory => exact absurd rfl (h4 ty path fld)
      | stack => rfl
  | index k ty path idx =>
      cases k with
      | storage => exact absurd rfl (h3 ty path idx)
      | memory => exact absurd rfl (h5 ty path idx)
      | stack => rfl
  | pushPlace p => rfl
  | bool b => exact absurd rfl hnt
  | intLit ty v => exact absurd rfl hnt
  | mkCall k ty fn args =>
      simp [compoundTargetOkB, Typed.WrappedExpr.isStack,
        Typed.WrappedExpr.kind]
  | mkBinop op l r => rfl
  | mkUnop op arg => rfl
  | mkIncDec op t2 => rfl
  | mkTernary c t2 e2 => rfl

theorem incDecAssignTargetOkB_eq_false_default {t : WrappedExpr}
    (hnt : ¬ (t.isStack && t.simple) = true)
    (h1 : ∀ ty fld, t = WrappedExpr.var Kind.storage ty fld -> False)
    (h2 : ∀ ty path fld,
      t = WrappedExpr.field Kind.storage ty path fld -> False)
    (h3 : ∀ ty path idx,
      t = WrappedExpr.index Kind.storage ty path idx -> False)
    (h4 : ∀ ty path fld,
      t = WrappedExpr.field Kind.memory ty path fld -> False)
    (h5 : ∀ ty path idx,
      t = WrappedExpr.index Kind.memory ty path idx -> False) :
    incDecAssignTargetOkB t = false := by
  cases t with
  | var k ty fld =>
      cases k with
      | storage => exact absurd rfl (h1 ty fld)
      | memory => rfl
      | stack => exact absurd rfl hnt
  | field k ty path fld =>
      cases k with
      | storage => exact absurd rfl (h2 ty path fld)
      | memory => exact absurd rfl (h4 ty path fld)
      | stack => rfl
  | index k ty path idx =>
      cases k with
      | storage => exact absurd rfl (h3 ty path idx)
      | memory => exact absurd rfl (h5 ty path idx)
      | stack => rfl
  | pushPlace p => rfl
  | bool b => exact absurd rfl hnt
  | intLit ty v => exact absurd rfl hnt
  | mkCall k ty fn args =>
      simp [incDecAssignTargetOkB, Typed.WrappedExpr.isStack,
        Typed.WrappedExpr.kind]
  | mkBinop op l r => rfl
  | mkUnop op arg => rfl
  | mkIncDec op t2 => rfl
  | mkTernary c t2 e2 => rfl

theorem or_eq_false {a b : Bool} (ha : a = false) (hb : b = false) :
    (a || b) = false := by
  cases a with
  | true => exact Bool.noConfusion ha
  | false => exact hb

theorem memoryDeclInitOkB_eq_false {rhs : WrappedExpr}
    (hnm : ¬ rhs.isMemory = true)
    (hx : ∀ ty path fld,
      rhs = WrappedExpr.field Kind.storage ty path fld -> False)
    (hns : ¬ (rhs.isStorage && rhs.simple) = true) :
    memoryDeclInitOkB rhs = false := by
  have hnm' := eq_false_of_not_eq_true hnm
  have hns' := eq_false_of_not_eq_true hns
  cases rhs with
  | field k ty base fld =>
      cases k with
      | storage => exact absurd rfl (hx ty base fld)
      | memory => exact or_eq_false hnm' hns'
      | stack => exact or_eq_false hnm' hns'
  | var k ty fld => exact or_eq_false hnm' hns'
  | index k ty base idx => exact or_eq_false hnm' hns'
  | pushPlace t => exact or_eq_false hnm' hns'
  | bool b => exact or_eq_false hnm' hns'
  | intLit ty v => exact or_eq_false hnm' hns'
  | mkCall k ty fn args => exact or_eq_false hnm' hns'
  | mkBinop op l r => exact or_eq_false hnm' hns'
  | mkUnop op arg => exact or_eq_false hnm' hns'
  | mkIncDec op t => exact or_eq_false hnm' hns'
  | mkTernary c t e => exact or_eq_false hnm' hns'

theorem valueCaptureLhsOkB_eq_false_of_none {le : WrappedExpr}
    (h : valueRhsCaptureCandidate le = none) :
    valueCaptureLhsOkB le = false := by
  cases le with
  | var k ty fld =>
      cases k with
      | storage =>
          simp only [valueRhsCaptureCandidate] at h
          split at h
          · exact nomatch h
          · next hng =>
              simp [valueCaptureLhsOkB, beq_eq_false_of_ne hng]
      | memory => rfl
      | stack => rfl
  | field k ty base fld =>
      cases k with
      | storage => exact nomatch h
      | memory => rfl
      | stack => rfl
  | index k ty base idx =>
      cases k with
      | storage => exact nomatch h
      | memory => rfl
      | stack => rfl
  | pushPlace t => rfl
  | bool b => rfl
  | intLit t v => rfl
  | mkCall k t n args => rfl
  | mkBinop op l r => rfl
  | mkUnop op a => rfl
  | mkIncDec op t => rfl
  | mkTernary c t e => rfl

/-- **The hard direction of the dichotomy**: on a well-typed statement,
every `none` answer of the dispatch function is one of the explicitly
listed residue shapes.  The proof follows `candidate`'s branch
structure; each `none` leaf is either a `ResidueShape` constructor or
refuted by `stmtWt` (storage-variable origins, container index bases,
`callStmt`, non-arith compound operators, non-storage deletes). -/
theorem residue_of_candidate_none {m : Modality} {Γ Γ' : Semantics.Ctx}
    {L : Semantics.Layout} {stmt : Stmt}
    (hwt : Semantics.stmtWt Γ L stmt = some Γ')
    (h : UniquenessAux.candidate m stmt = none) :
    ResidueShape stmt := by
  cases stmt with
  | storageDecl ty name init =>
      cases init with
      | none => exact nomatch h
      | some rhs => exact nomatch h
  | storagePlaceAlias ty name init => exact nomatch h
  | stackDecl ty name init =>
      cases init with
      | none => exact nomatch h
      | some rhs => exact nomatch h
  | pushAssign target value => exact nomatch h
  | pushFieldAssign target fld value => exact nomatch h
  | «revert» msg => cases m <;> exact nomatch h
  | assertStmt c =>
      replace h : assertCandidate c = none := h
      simp only [assertCandidate] at h
      split at h <;> exact nomatch h
  | requireStmt c =>
      replace h : requireCandidate c = none := h
      simp only [requireCandidate] at h
      split at h <;> exact nomatch h
  | transfer recipient amount =>
      replace h : transferCandidate recipient amount = none := h
      simp only [transferCandidate] at h
      split at h
      · exact nomatch h
      · split at h <;> exact nomatch h
  | callStmt res fn args => exact nomatch hwt
  | ite cond thn els =>
      replace h : iteCandidate cond = none := h
      cases cond with
      | bool b => cases b <;> exact nomatch h
      | var k ty fld =>
          simp only [iteCandidate] at h
          split at h
          · exact nomatch h
          · exact ResidueShape.iteSymbolicCond _ thn els rfl rfl
      | intLit ty v =>
          simp only [iteCandidate] at h
          split at h
          · exact nomatch h
          · exact ResidueShape.iteSymbolicCond _ thn els rfl rfl
      | mkUnop op inner =>
          cases op with
          | not =>
              simp only [iteCandidate] at h
              split at h <;> exact nomatch h
          | neg =>
              simp only [iteCandidate] at h
              split at h
              · exact nomatch h
              · next hnc => exact absurd rfl hnc
      | field k ty base fld =>
          simp only [iteCandidate] at h
          split at h
          · exact nomatch h
          · next hnc => exact absurd rfl hnc
      | index k ty base idx =>
          simp only [iteCandidate] at h
          split at h
          · exact nomatch h
          · next hnc => exact absurd rfl hnc
      | pushPlace t =>
          simp only [iteCandidate] at h
          split at h
          · exact nomatch h
          · next hnc => exact absurd rfl hnc
      | mkCall k ty fn args =>
          simp only [iteCandidate] at h
          split at h
          · exact nomatch h
          · next hnc => exact absurd rfl hnc
      | mkBinop op l r =>
          simp only [iteCandidate] at h
          split at h
          · exact nomatch h
          · next hnc => exact absurd rfl hnc
      | mkIncDec op t =>
          simp only [iteCandidate] at h
          split at h
          · exact nomatch h
          · next hnc => exact absurd rfl hnc
      | mkTernary c t e =>
          simp only [iteCandidate] at h
          split at h
          · exact nomatch h
          · next hnc => exact absurd rfl hnc
  | pop target =>
      obtain ⟨te, hass⟩ := target
      replace h : popCandidate m te = none := h
      simp only [popCandidate] at h
      split at h
      · split at h
        · exact nomatch h
        · cases m <;> exact nomatch h
      · next hnk => exact ResidueShape.popNonStorageTarget _ hnk
  | push target value =>
      obtain ⟨te, hass⟩ := target
      cases value with
      | none =>
          replace h : pushCandidate te none = none := h
          simp only [pushCandidate] at h
          split at h
          · split at h <;> exact nomatch h
          · next hnk => exact ResidueShape.pushNonStorageTarget _ none hnk
      | some rhs =>
          replace h : pushCandidate te (some rhs) = none := h
          simp only [pushCandidate] at h
          split at h
          · next hks =>
              split at h
              · exact nomatch h
              · next hntc =>
                  split at h
                  · exact nomatch h
                  · next hnrc =>
                      split at h
                      · exact nomatch h
                      · next hnsto =>
                          split at h
                          · exact nomatch h
                          · next hnstk =>
                              rcases kind_trichotomy rhs with hk | hk | hk
                              · exact absurd hk hnsto
                              · exact ResidueShape.pushMemoryValue _ rhs hks
                                  (eq_false_of_not_eq_true hntc)
                                  (eq_false_of_not_eq_true hnrc) hk
                              · exact absurd hk hnstk
          · next hnk =>
              exact ResidueShape.pushNonStorageTarget _ (some rhs) hnk
  | «delete» target =>
      obtain ⟨te, hass⟩ := target
      simp only [Semantics.stmtWt] at hwt
      split at hwt
      case isFalse => exact nomatch hwt
      case isTrue hc =>
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hwte, hks⟩ := hc
      replace h : deleteCandidate te = none := h
      cases te with
      | var k ty fld =>
          cases k with
          | storage =>
              simp only [deleteCandidate] at h
              split at h
              · exact nomatch h
              · next hng =>
                  exact ResidueShape.deleteStorageLocalRoot _ ty fld rfl
                    (beq_eq_false_of_ne hng)
          | memory => exact nomatch h
          | stack => exact absurd (eq_of_beq hks) (by simp)
      | field k ty path fld =>
          cases k with
          | storage =>
              simp only [deleteCandidate] at h
              split at h <;> exact nomatch h
          | memory =>
              simp only [deleteCandidate] at h
              split at h <;> exact nomatch h
          | stack => exact absurd (eq_of_beq hks) (by simp)
      | index k ty path idx =>
          cases k with
          | storage =>
              simp only [deleteCandidate] at h
              split at h
              · exact nomatch h
              · next hnpc =>
                  split at h
                  · exact nomatch h
                  · next hnic =>
                      split at h
                      · exact nomatch h
                      · next hncont =>
                          rcases wt_index_container hwte with hcont | hcont
                          · exact absurd (by simp [hcont]) hncont
                          · exact absurd (by simp [hcont]) hncont
          | memory =>
              simp only [deleteCandidate] at h
              split at h
              · exact nomatch h
              · split at h <;> exact nomatch h
          | stack => exact absurd (eq_of_beq hks) (by simp)
      | pushPlace p =>
          simp only [deleteCandidate] at h
          split at h
          · split at h <;> exact nomatch h
          · next hnk =>
              exact ResidueShape.deletePushPlaceNonStorage _ p rfl hnk
      | bool b => exact Bool.noConfusion hass
      | intLit t v => exact Bool.noConfusion hass
      | mkCall k t n args => exact Bool.noConfusion hass
      | mkBinop op l r => exact Bool.noConfusion hass
      | mkUnop op a => exact Bool.noConfusion hass
      | mkIncDec op t => exact Bool.noConfusion hass
      | mkTernary c t e => exact Bool.noConfusion hass
  | memoryDecl ty name init =>
      replace h : memoryDeclCandidate init = none := h
      cases init with
      | none => exact nomatch h
      | some rhs =>
          simp only [memoryDeclCandidate] at h
          split at h
          · exact nomatch h
          · next hnmem =>
              split at h
              · split at h <;> exact nomatch h
              · next hx =>
                  split at h
                  · exact nomatch h
                  · next hns =>
                      exact ResidueShape.memoryDeclBadInit ty name rhs
                        (memoryDeclInitOkB_eq_false hnmem hx hns)
  | expr e =>
      cases e with
      | mkIncDec op target =>
          refine ResidueShape.incDecStmt op target ?_
          replace h : incDecStmtCandidate op target = none := h
          simp only [incDecStmtCandidate] at h
          split at h
          · exact nomatch h
          · next hnt =>
              split at h
              · next ty fld =>
                  split at h
                  · exact nomatch h
                  · next hng =>
                      simp [compoundTargetOkB, Typed.WrappedExpr.isStack,
                        Typed.WrappedExpr.kind, beq_eq_false_of_ne hng]
              · next ty path fld =>
                  split at h <;> exact nomatch h
              · next ty path idx =>
                  split at h
                  · next hic =>
                      simp [compoundTargetOkB, Typed.WrappedExpr.isStack,
                        Typed.WrappedExpr.kind, hic]
                  · split at h <;> exact nomatch h
              · next ty path fld =>
                  split at h <;> exact nomatch h
              · next ty path idx =>
                  split at h
                  · next hic =>
                      simp [compoundTargetOkB, Typed.WrappedExpr.isStack,
                        Typed.WrappedExpr.kind, hic]
                  · split at h <;> exact nomatch h
              · next hx1 hx2 hx3 hx4 hx5 =>
                  exact compoundTargetOkB_eq_false_default hnt hx1 hx2 hx3
                    hx4 hx5
      | var k ty fld => exact nomatch h
      | field k ty base fld => exact nomatch h
      | index k ty base idx => exact nomatch h
      | pushPlace t => exact nomatch h
      | bool b => exact nomatch h
      | intLit ty v => exact nomatch h
      | mkCall k ty fn args => exact nomatch h
      | mkBinop op l r => exact nomatch h
      | mkUnop op arg => exact nomatch h
      | mkTernary c t e => exact nomatch h
  | compoundAssign op lhs rhs =>
      obtain ⟨le, hass⟩ := lhs
      simp only [Semantics.stmtWt] at hwt
      split at hwt
      case isFalse => exact nomatch hwt
      case isTrue hc =>
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hArith, -⟩, -⟩ := hc
      replace h : compoundAssignCandidate op le rhs = none := h
      simp only [compoundAssignCandidate] at h
      split at h
      · next hca =>
          split at h
          · next hstk =>
              split at h
              · exact nomatch h
              · next hnsv =>
                  split at h
                  · next ty fld =>
                      split at h
                      · exact nomatch h
                      · next hng =>
                          refine ResidueShape.compoundAssignBadTarget op _
                            rhs hca hstk ?_
                          simp [compoundTargetOkB,
                            Typed.WrappedExpr.isStack,
                            Typed.WrappedExpr.kind,
                            beq_eq_false_of_ne hng]
                  · next ty path fld =>
                      split at h <;> exact nomatch h
                  · next ty path idx =>
                      split at h
                      · next hic =>
                          refine ResidueShape.compoundAssignBadTarget op _
                            rhs hca hstk ?_
                          simp [compoundTargetOkB,
                            Typed.WrappedExpr.isStack,
                            Typed.WrappedExpr.kind, hic]
                      · split at h <;> exact nomatch h
                  · next ty path fld =>
                      split at h <;> exact nomatch h
                  · next ty path idx =>
                      split at h
                      · next hic =>
                          refine ResidueShape.compoundAssignBadTarget op _
                            rhs hca hstk ?_
                          simp [compoundTargetOkB,
                            Typed.WrappedExpr.isStack,
                            Typed.WrappedExpr.kind, hic]
                      · split at h <;> exact nomatch h
                  · next hx1 hx2 hx3 hx4 hx5 =>
                      exact ResidueShape.compoundAssignBadTarget op _ rhs
                        hca hstk
                        (compoundTargetOkB_eq_false_default hnsv hx1 hx2 hx3
                          hx4 hx5)
          · exact nomatch h
      · next hnca =>
          cases op <;> first
            | exact Bool.noConfusion hArith
            | exact absurd rfl hnca
            | exact ResidueShape.compoundAssignPow _ rhs
  | assign lhs rhs =>
      obtain ⟨le, hass⟩ := lhs
      simp only [Semantics.stmtWt] at hwt
      split at hwt
      case isFalse => exact nomatch hwt
      case isTrue hc =>
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hwl, hwr⟩, -⟩ := hc
      replace h : assignCandidate m le rhs = none := h
      unfold assignCandidate at h
      split at h
      · next hsimp =>
          -- simple rhs tier
          cases le with
          | var k ty fld =>
              cases k with
              | storage =>
                  simp only [assignSimpleCandidate] at h
                  split at h
                  · next hloc =>
                      split at h
                      · exact nomatch h
                      · next hnsto =>
                          split at h
                          · exact nomatch h
                          · next hnmem =>
                              rcases kind_trichotomy rhs with hk | hk | hk
                              · exact absurd hk hnsto
                              · exact absurd hk hnmem
                              · exact
                                  ResidueShape.assignStorageLocalRootFromStack
                                    _ rhs ty fld rfl hloc hsimp hk
                  · next hnloc =>
                      split at h
                      · next hglob =>
                          split at h
                          · exact nomatch h
                          · next hnsto =>
                              split at h
                              · exact nomatch h
                              · next hnstk =>
                                  split at h
                                  · exact nomatch h
                                  · next hnmem =>
                                      rcases kind_trichotomy rhs with
                                        hk | hk | hk
                                      · exact absurd hk hnsto
                                      · exact absurd hk hnmem
                                      · exact absurd hk hnstk
                      · next hnglob =>
                          split at h
                          · exact nomatch h
                          · next hnmem =>
                              rcases wt_storageVar_origin hwl with ho | ho
                              · exact absurd ho hnloc
                              · exact absurd ho hnglob
              | memory =>
                  simp only [assignSimpleCandidate] at h
                  split at h
                  · exact nomatch h
                  · next hnmem =>
                      split at h
                      · exact nomatch h
                      · next hnsto =>
                          rcases kind_trichotomy rhs with hk | hk | hk
                          · exact absurd hk hnsto
                          · exact absurd hk hnmem
                          · exact ResidueShape.assignMemoryRootFromStack
                              _ rhs ty fld rfl hsimp hk
              | stack =>
                  simp only [assignSimpleCandidate] at h
                  split at h
                  · exact nomatch h
                  · next hn1 =>
                      split at h
                      · exact nomatch h
                      · next hn2 =>
                          have hnsto : rhs.isStorage = false :=
                            eq_false_of_not_eq_true (fun hx => hn1 hx)
                          have hnstk : rhs.isStack = false :=
                            eq_false_of_not_eq_true (fun hx => hn2 hx)
                          rcases kind_trichotomy rhs with hk | hk | hk
                          · rw [hk] at hnsto; exact Bool.noConfusion hnsto
                          · exact ResidueShape.assignStackVarFromMemory
                              _ rhs ty fld rfl hsimp hk
                          · rw [hk] at hnstk; exact Bool.noConfusion hnstk
          | field k ty path fld =>
              cases k with
              | storage =>
                  simp only [assignSimpleCandidate] at h
                  split at h
                  · split at h <;> exact nomatch h
                  · next hnpc =>
                      split at h
                      · exact nomatch h
                      · next hnsto =>
                          split at h
                          · exact nomatch h
                          · next hnstk =>
                              split at h
                              · exact nomatch h
                              · next hnmem =>
                                  rcases kind_trichotomy rhs with hk | hk | hk
                                  · exact absurd hk hnsto
                                  · exact absurd hk hnmem
                                  · exact absurd hk hnstk
              | memory =>
                  simp only [assignSimpleCandidate] at h
                  split at h
                  · exact nomatch h
                  · next hnpc =>
                      split at h
                      · exact nomatch h
                      · next hnmem =>
                          split at h
                          · exact nomatch h
                          · next hnstk =>
                              rcases kind_trichotomy rhs with hk | hk | hk
                              · exact ResidueShape.assignMemFieldFromStorage
                                  _ rhs ty path fld rfl
                                  (eq_false_of_not_eq_true hnpc) hsimp hk
                              · exact absurd hk hnmem
                              · exact absurd hk hnstk
              | stack =>
                  simp only [assignSimpleCandidate] at h
                  split at h
                  · exact nomatch h
                  · next hn1 =>
                      split at h
                      · exact nomatch h
                      · next hn2 =>
                          have hnsto : rhs.isStorage = false :=
                            eq_false_of_not_eq_true (fun hx => hn1 hx)
                          exact ResidueShape.assignStackPlace _ rhs
                            (Or.inl ⟨ty, path, fld, rfl⟩) hsimp hnsto
          | index k ty path idx =>
              cases k with
              | storage =>
                  simp only [assignSimpleCandidate] at h
                  split at h
                  · exact nomatch h
                  · next hnpc =>
                      split at h
                      · split at h <;> exact nomatch h
                      · next hnic =>
                          split at h
                          · next hsto =>
                              split at h
                              · cases m <;> exact nomatch h
                              · next hna =>
                                  split at h
                                  · exact nomatch h
                                  · next hnmap =>
                                      rcases wt_index_container hwl with
                                        hcont | hcont
                                      · exact absurd hcont hna
                                      · exact absurd hcont hnmap
                          · next hnsto =>
                              split at h
                              · next hstk =>
                                  split at h
                                  · cases m <;> exact nomatch h
                                  · next hna =>
                                      split at h
                                      · exact nomatch h
                                      · next hnmap =>
                                          rcases wt_index_container hwl with
                                            hcont | hcont
                                          · exact absurd hcont hna
                                          · exact absurd hcont hnmap
                              · next hnstk =>
                                  split at h
                                  · next hmem =>
                                      split at h
                                      · cases m <;> exact nomatch h
                                      · next hna =>
                                          split at h
                                          · exact nomatch h
                                          · next hnmap =>
                                              rcases wt_index_container hwl
                                                with hcont | hcont
                                              · exact absurd hcont hna
                                              · exact absurd hcont hnmap
                                  · next hnmem =>
                                      rcases kind_trichotomy rhs with
                                        hk | hk | hk
                                      · exact absurd hk hnsto
                                      · exact absurd hk hnmem
                                      · exact absurd hk hnstk
              | memory =>
                  simp only [assignSimpleCandidate] at h
                  split at h
                  · exact nomatch h
                  · next hnpc =>
                      split at h
                      · exact nomatch h
                      · next hnic =>
                          split at h
                          · cases m <;> exact nomatch h
                          · next hnmem =>
                              split at h
                              · cases m <;> exact nomatch h
                              · next hnstk =>
                                  rcases kind_trichotomy rhs with hk | hk | hk
                                  · exact
                                      ResidueShape.assignMemIndexFromStorage
                                        _ rhs ty path idx rfl
                                        (eq_false_of_not_eq_true hnpc)
                                        (eq_false_of_not_eq_true hnic)
                                        hsimp hk
                                  · exact absurd hk hnmem
                                  · exact absurd hk hnstk
              | stack =>
                  simp only [assignSimpleCandidate] at h
                  split at h
                  · exact nomatch h
                  · next hn1 =>
                      split at h
                      · exact nomatch h
                      · next hn2 =>
                          have hnsto : rhs.isStorage = false :=
                            eq_false_of_not_eq_true (fun hx => hn1 hx)
                          exact ResidueShape.assignStackPlace _ rhs
                            (Or.inr ⟨ty, path, idx, rfl⟩) hsimp hnsto
          | pushPlace t =>
              simp only [assignSimpleCandidate] at h
              split at h
              · exact nomatch h
              · next hnk =>
                  exact ResidueShape.assignPushPlaceLhsNonStorage _ rhs t
                    rfl hnk hsimp
          | bool b => exact Bool.noConfusion hass
          | intLit t v => exact Bool.noConfusion hass
          | mkCall k t n args => exact Bool.noConfusion hass
          | mkBinop op l r => exact Bool.noConfusion hass
          | mkUnop op a => exact Bool.noConfusion hass
          | mkIncDec op t => exact Bool.noConfusion hass
          | mkTernary c t e => exact Bool.noConfusion hass
      · next hns =>
          -- complex rhs tier
          cases rhs with
          | var k2 ty2 fld2 => exact absurd rfl hns
          | bool b => exact absurd rfl hns
          | intLit ty2 v => exact absurd rfl hns
          | field k2 ty2 path fld2 =>
              cases k2 with
              | storage =>
                  simp only [assignComplexCandidate] at h
                  split at h
                  · exact nomatch h
                  · next hn1 =>
                      split at h
                      · exact nomatch h
                      · next hn2 =>
                          split at h
                          · exact nomatch h
                          · next hnpc =>
                              split at h
                              · next hsto =>
                                  split at h
                                  · exact nomatch h
                                  · next hnlc =>
                                      split at h
                                      · exact nomatch h
                                      · next hnloc =>
                                          split at h
                                          · exact nomatch h
                                          · next hnglob =>
                                              obtain ⟨ty3, fld3, heq⟩ :=
                                                simple_storage_shape
                                                  (simple_of_not_complex hnlc)
                                                  (kind_of_isStorage hsto)
                                              rw [heq] at hwl hnloc hnglob
                                              rcases wt_storageVar_origin hwl
                                                with ho | ho
                                              · exact absurd (by
                                                  simp
                                                    [Typed.WrappedExpr.isLocal,
                                                    ho]) hnloc
                                              · exact absurd (by
                                                  simp
                                                    [Typed.WrappedExpr.isGlobal,
                                                    ho]) hnglob
                              · next hnsto =>
                                  split at h
                                  · exact nomatch h
                                  · next hnstk =>
                                      split at h
                                      · exact nomatch h
                                      · next hnmem =>
                                          rcases kind_trichotomy le with
                                            hk | hk | hk
                                          · exact absurd hk hnsto
                                          · exact absurd
                                              (kind_of_isMemory hk) hnmem
                                          · exact absurd hk hnstk
              | memory =>
                  simp only [assignComplexCandidate] at h
                  split at h
                  · split at h <;> exact nomatch h
                  · next hn1 =>
                      split at h
                      · exact nomatch h
                      · next hn2 =>
                          split at h
                          · exact nomatch h
                          · next hnpc =>
                              split at h
                              · exact nomatch h
                              · next hnstk =>
                                  split at h
                                  · exact nomatch h
                                  · next hnmem =>
                                      rcases kind_trichotomy le with
                                        hk | hk | hk
                                      · exact absurd
                                          ⟨kind_of_isStorage hk, rfl⟩ hn2
                                      · exact absurd (kind_of_isMemory hk)
                                          hnmem
                                      · exact absurd hk hnstk
              | stack =>
                  simp only [assignComplexCandidate] at h
                  split at h
                  · exact nomatch h
                  · next hn1 =>
                      split at h
                      · exact nomatch h
                      · next hn2 =>
                          exact ResidueShape.assignStackPlaceRhs _ _
                            (Or.inl ⟨ty2, path, fld2, rfl⟩) hn1
          | index k2 ty2 path idx =>
              cases k2 with
              | storage =>
                  simp only [assignComplexCandidate] at h
                  split at h
                  · exact nomatch h
                  · next hn1 =>
                      split at h
                      · exact nomatch h
                      · next hn2 =>
                          split at h
                          · exact nomatch h
                          · next hnpc =>
                              split at h
                              · exact nomatch h
                              · next hnic =>
                                  split at h
                                  · next hsto =>
                                      split at h
                                      · exact nomatch h
                                      · next hnlc =>
                                          split at h
                                          · next hloc =>
                                              split at h
                                              · cases m <;> exact nomatch h
                                              · next hna =>
                                                  split at h
                                                  · exact nomatch h
                                                  · next hnmap =>
                                                      rcases
                                                        wt_index_container hwr
                                                        with hcont | hcont
                                                      · exact absurd hcont hna
                                                      · exact absurd hcont
                                                          hnmap
                                          · next hnloc =>
                                              split at h
                                              · next hglob =>
                                                  split at h
                                                  · cases m <;>
                                                      exact nomatch h
                                                  · next hna =>
                                                      split at h
                                                      · exact nomatch h
                                                      · next hnmap =>
                                                          rcases
                                                            wt_index_container
                                                              hwr
                                                            with hcont | hcont
                                                          · exact absurd hcont
                                                              hna
                                                          · exact absurd hcont
                                                              hnmap
                                              · next hnglob =>
                                                  obtain ⟨ty3, fld3, heq⟩ :=
                                                    simple_storage_shape
                                                      (simple_of_not_complex
                                                        hnlc)
                                                      (kind_of_isStorage hsto)
                                                  rw [heq] at hwl hnloc hnglob
                                                  rcases
                                                    wt_storageVar_origin hwl
                                                    with ho | ho
                                                  · exact absurd (by
                                                      simp
                                                        [Typed.WrappedExpr.isLocal,
                                                        ho]) hnloc
                                                  · exact absurd (by
                                                      simp
                                                        [Typed.WrappedExpr.isGlobal,
                                                        ho]) hnglob
                                  · next hnsto =>
                                      split at h
                                      · next hstk =>
                                          split at h
                                          · cases m <;> exact nomatch h
                                          · next hna =>
                                              split at h
                                              · exact nomatch h
                                              · next hnmap =>
                                                  rcases
                                                    wt_index_container hwr
                                                    with hcont | hcont
                                                  · exact absurd hcont hna
                                                  · exact absurd hcont hnmap
                                      · next hnstk =>
                                          split at h
                                          · exact nomatch h
                                          · next hnmem =>
                                              rcases kind_trichotomy le with
                                                hk | hk | hk
                                              · exact absurd hk hnsto
                                              · exact absurd
                                                  (kind_of_isMemory hk) hnmem
                                              · exact absurd hk hnstk
              | memory =>
                  simp only [assignComplexCandidate] at h
                  split at h
                  · split at h
                    · exact nomatch h
                    · split at h <;> exact nomatch h
                  · next hn1 =>
                      split at h
                      · exact nomatch h
                      · next hn2 =>
                          split at h
                          · exact nomatch h
                          · next hnpc =>
                              split at h
                              · exact nomatch h
                              · next hnic =>
                                  split at h
                                  · cases m <;> exact nomatch h
                                  · next hnstk =>
                                      split at h
                                      · cases m <;> exact nomatch h
                                      · next hnmem =>
                                          rcases kind_trichotomy le with
                                            hk | hk | hk
                                          · exact absurd
                                              ⟨kind_of_isStorage hk, rfl⟩ hn2
                                          · exact absurd
                                              (kind_of_isMemory hk) hnmem
                                          · exact absurd hk hnstk
              | stack =>
                  simp only [assignComplexCandidate] at h
                  split at h
                  · exact nomatch h
                  · next hn1 =>
                      split at h
                      · exact nomatch h
                      · next hn2 =>
                          exact ResidueShape.assignStackPlaceRhs _ _
                            (Or.inr ⟨ty2, path, idx, rfl⟩) hn1
          | pushPlace t =>
              simp only [assignComplexCandidate] at h
              split at h
              · exact nomatch h
              · next hn1 =>
                  split at h
                  · exact nomatch h
                  · next hn2 =>
                      split at h
                      · exact nomatch h
                      · next hntc =>
                          split at h
                          · exact nomatch h
                          · next hnloc =>
                              by_cases hkt : t.kind = Kind.storage
                              · exact
                                  ResidueShape.assignPushRhsNonLocalLhs _ t
                                    hkt (eq_false_of_not_eq_true hntc)
                                    (eq_false_of_not_eq_true hnloc) hn1
                              · exact
                                  ResidueShape.assignPushRhsNonStorage _ t
                                    hkt hn1
          | mkBinop op2 l r =>
              simp only [assignComplexCandidate] at h
              split at h
              · exact nomatch h
              · next hn1 =>
                  split at h
                  · exact nomatch h
                  · next hn2 =>
                      split at h
                      · next hsv =>
                          split at h
                          · exact nomatch h
                          · next hnlc =>
                              split at h
                              · split at h <;> exact nomatch h
                              · exact nomatch h
                      · next hnsv =>
                          split at h
                          · exact nomatch h
                          · next hnb =>
                              refine
                                ResidueShape.assignOperatorRhsBadLhs _ _
                                  (bnot_eq_true_of_eq_false
                                    (eq_false_of_not_eq_true hnb))
                                  (eq_false_of_not_eq_true hnsv)
                                  (valueCaptureLhsOkB_eq_false_of_none h)
                                  hn1
          | mkUnop op2 arg =>
              simp only [assignComplexCandidate] at h
              split at h
              · exact nomatch h
              · next hn1 =>
                  split at h
                  · exact nomatch h
                  · next hn2 =>
                      split at h
                      · next hsv =>
                          split at h <;> exact nomatch h
                      · next hnsv =>
                          exact ResidueShape.assignOperatorRhsBadLhs _ _
                            rfl (eq_false_of_not_eq_true hnsv)
                            (valueCaptureLhsOkB_eq_false_of_none h) hn1
          | mkIncDec op2 t =>
              simp only [assignComplexCandidate] at h
              split at h
              · exact nomatch h
              · next hn1 =>
                  split at h
                  · exact nomatch h
                  · next hn2 =>
                      split at h
                      · next hsv =>
                          split at h
                          · exact nomatch h
                          · next hnt =>
                              split at h
                              · next ty3 fld3 =>
                                  split at h
                                  · exact nomatch h
                                  · next hng =>
                                      refine
                                        ResidueShape.assignIncDecBadTarget
                                          _ op2 _ hsv ?_
                                      simp [incDecAssignTargetOkB,
                                        Typed.WrappedExpr.isStack,
                                        Typed.WrappedExpr.kind,
                                        beq_eq_false_of_ne hng]
                              · next ty3 path3 fld3 =>
                                  split at h
                                  · next hpc =>
                                      refine
                                        ResidueShape.assignIncDecBadTarget
                                          _ op2 _ hsv ?_
                                      simp [incDecAssignTargetOkB,
                                        Typed.WrappedExpr.isStack,
                                        Typed.WrappedExpr.kind, hpc]
                                  · exact nomatch h
                              · next ty3 path3 idx3 =>
                                  split at h
                                  · next hor =>
                                      refine
                                        ResidueShape.assignIncDecBadTarget
                                          _ op2 _ hsv ?_
                                      simp [incDecAssignTargetOkB,
                                        Typed.WrappedExpr.isStack,
                                        Typed.WrappedExpr.kind, hor]
                                  · exact nomatch h
                              · next ty3 path3 fld3 =>
                                  split at h
                                  · next hpc =>
                                      refine
                                        ResidueShape.assignIncDecBadTarget
                                          _ op2 _ hsv ?_
                                      simp [incDecAssignTargetOkB,
                                        Typed.WrappedExpr.isStack,
                                        Typed.WrappedExpr.kind, hpc]
                                  · exact nomatch h
                              · next ty3 path3 idx3 =>
                                  split at h
                                  · next hor =>
                                      refine
                                        ResidueShape.assignIncDecBadTarget
                                          _ op2 _ hsv ?_
                                      simp [incDecAssignTargetOkB,
                                        Typed.WrappedExpr.isStack,
                                        Typed.WrappedExpr.kind, hor]
                                  · exact nomatch h
                              · next hx1 hx2 hx3 hx4 hx5 =>
                                  exact
                                    ResidueShape.assignIncDecBadTarget
                                      _ op2 _ hsv
                                      (incDecAssignTargetOkB_eq_false_default
                                        hnt hx1 hx2 hx3 hx4 hx5)
                      · next hnsv =>
                          exact ResidueShape.assignOperatorRhsBadLhs _ _
                            rfl (eq_false_of_not_eq_true hnsv)
                            (valueCaptureLhsOkB_eq_false_of_none h) hn1
          | mkTernary c thn els =>
              simp only [assignComplexCandidate] at h
              split at h
              · exact nomatch h
              · next hn1 =>
                  split at h
                  · exact nomatch h
                  · next hn2 =>
                      split at h
                      · exact nomatch h
                      · next hncc =>
                          split at h
                          · exact nomatch h
                          · next hnsv =>
                              split at h
                              · exact nomatch h
                              · next hnsto =>
                                  exact ResidueShape.assignTernaryBadLhs
                                    _ c thn els
                                    (eq_false_of_not_eq_true hncc)
                                    (eq_false_of_not_eq_true hnsv)
                                    (eq_false_of_not_eq_true hnsto) hn1
          | mkCall k2 ty2 fn args =>
              simp only [assignComplexCandidate] at h
              split at h
              · exact nomatch h
              · next hn1 =>
                  split at h
                  · exact nomatch h
                  · next hn2 =>
                      refine ResidueShape.assignCallRhs _ k2 ty2 fn args
                        hn1 ?_
                      intro hx
                      refine hn2 ⟨hx.1, ?_⟩
                      simp [Typed.WrappedExpr.isMemory, kind_mkCall, hx.2]

/-! ## Headline theorems (deliverable 3) -/

/-- A `none` answer of the dispatch function means no rule of the calculus applies
(direct contrapositive of `applicable_eq_candidate`). -/
theorem not_covered_of_candidate_none {m : Modality} {stmt : Stmt}
    (h : UniquenessAux.candidate m stmt = none) :
    ¬ Rules.ruleApplies m stmt := by
  rintro ⟨rule, hmem, hmode, hcond⟩
  rw [UniquenessAux.applicable_eq_candidate hmem hmode hcond] at h
  exact Option.noConfusion h

/-- Non-coverage of the overshoot cell: an assignment binding a
non-storage `pushPlace` (outside `pushRhsStorageB`) is claimed by no
rule of the calculus, although `candidate` does not answer `none` on it — the
push-bind rules it names require a storage receiver. -/
theorem pushRhs_not_covered {m : Modality} {lhs : PlaceExpr}
    {t : WrappedExpr} (hk : ¬ t.kind = Kind.storage)
    (hnm : ¬ (lhs.expr.kind = Kind.memory ∧ lhs.expr.complex = true)) :
    ¬ Rules.ruleApplies m
      (Stmt.assign lhs (WrappedExpr.pushPlace t)) := by
  rintro ⟨rule, hmem, hmode, hcond⟩
  have hcand := UniquenessAux.applicable_eq_candidate hmem hmode hcond
  obtain ⟨le, hass⟩ := lhs
  replace hcand :
      assignCandidate m le (WrappedExpr.pushPlace t) = some rule := hcand
  unfold assignCandidate at hcand
  split at hcand
  · next hs => exact Bool.noConfusion hs
  · next hns =>
      simp only [assignComplexCandidate] at hcand
      split at hcand
      · next hmc => exact hnm hmc
      · next hn1 =>
          split at hcand
          · next h2 => exact Bool.noConfusion h2.2
          · next hn2 =>
              split at hcand
              · next htc =>
                  cases Option.some.inj hcand
                  exact hk hcond.1
              · next hntc =>
                  split at hcand
                  · next hloc =>
                      cases Option.some.inj hcand
                      exact hk hcond.2.1
                  · exact nomatch hcand

/-- **Residue is never covered** (deliverable 3): a residue-shaped
statement is claimed by no rule of the calculus, under either modality. -/
theorem residue_not_covered {m : Modality} {stmt : Stmt}
    (h : ResidueShape stmt) : ¬ Rules.ruleApplies m stmt := by
  rcases residue_dispatch (m := m) h with hnone | ⟨lhs, t, heq, hk, hnm⟩
  · exact not_covered_of_candidate_none hnone
  · subst heq
    exact pushRhs_not_covered hk hnm

/-- On the trustworthy fragment, `candidate`'s `none` answers on a
well-typed statement are *exactly* the residue shapes.  (The `none`
answers are also mode-independent: `residue_dispatch`'s computations
never consult the modality, so this equivalence holds for every `m`
with the same right-hand side.) -/
theorem candidate_none_iff_residue {m : Modality} {Γ Γ' : Semantics.Ctx}
    {L : Semantics.Layout} {stmt : Stmt}
    (hwt : Semantics.stmtWt Γ L stmt = some Γ')
    (hp : pushRhsStorageB stmt = true) :
    UniquenessAux.candidate m stmt = none ↔ ResidueShape stmt := by
  constructor
  · exact residue_of_candidate_none hwt
  · intro h
    rcases residue_dispatch (m := m) h with hnone | ⟨lhs, t, heq, hk, -⟩
    · exact hnone
    · subst heq
      exact absurd (eq_of_beq (hp : (t.kind == Kind.storage) = true)) hk

/-- **Coverage** (deliverable 3): every well-typed statement is either
claimed by a rule of the calculus or has one of the explicitly listed residue
shapes.  With `residue_not_covered` the disjunction is exclusive
(`not_covered_iff_residue`). -/
theorem coverage_residue (m : Modality) {Γ Γ' : Semantics.Ctx}
    {L : Semantics.Layout} {stmt : Stmt}
    (hwt : Semantics.stmtWt Γ L stmt = some Γ') :
    Rules.ruleApplies m stmt ∨ ResidueShape stmt := by
  by_cases hp : pushRhsStorageB stmt = true
  · cases hcand : UniquenessAux.candidate m stmt with
    | none => exact Or.inr (residue_of_candidate_none hwt hcand)
    | some rule =>
        obtain ⟨h1, h2, h3⟩ := candidate_applies hp hcand
        exact Or.inl ⟨rule, h1, h2, h3⟩
  · cases stmt with
    | assign lhs rhs =>
        cases rhs with
        | pushPlace t =>
            have hk : ¬ t.kind = Kind.storage := by
              intro he
              exact hp (by simp [pushRhsStorageB, he])
            by_cases hmc :
                lhs.expr.kind = Kind.memory ∧ lhs.expr.complex = true
            · refine Or.inl
                ⟨.memoryWriteUnfoldRightSndResult, by decide, rfl, ?_⟩
              exact ⟨hmc.1, hmc.2, rfl, trivial⟩
            · exact Or.inr
                (ResidueShape.assignPushRhsNonStorage lhs t hk hmc)
        | var k ty fld => exact absurd rfl hp
        | field k ty base fld => exact absurd rfl hp
        | index k ty base idx => exact absurd rfl hp
        | bool b => exact absurd rfl hp
        | intLit ty v => exact absurd rfl hp
        | mkCall k ty fn args => exact absurd rfl hp
        | mkBinop op l r => exact absurd rfl hp
        | mkUnop op arg => exact absurd rfl hp
        | mkIncDec op t => exact absurd rfl hp
        | mkTernary c t e => exact absurd rfl hp
    | expr e => exact absurd rfl hp
    | storageDecl ty name init => exact absurd rfl hp
    | storagePlaceAlias ty name init => exact absurd rfl hp
    | memoryDecl ty name init => exact absurd rfl hp
    | stackDecl ty name init => exact absurd rfl hp
    | «delete» target => exact absurd rfl hp
    | push target value => exact absurd rfl hp
    | pushAssign target value => exact absurd rfl hp
    | pushFieldAssign target fld value => exact absurd rfl hp
    | pop target => exact absurd rfl hp
    | «revert» msg => exact absurd rfl hp
    | compoundAssign op lhs rhs => exact absurd rfl hp
    | ite cond thn els => exact absurd rfl hp
    | assertStmt c => exact absurd rfl hp
    | requireStmt c => exact absurd rfl hp
    | transfer recipient amount => exact absurd rfl hp
    | callStmt res fn args => exact absurd rfl hp

/-- Uncovered exactly means residue: for a well-typed statement, no rule
of the calculus applies iff the statement has a residue shape. -/
theorem not_covered_iff_residue (m : Modality) {Γ Γ' : Semantics.Ctx}
    {L : Semantics.Layout} {stmt : Stmt}
    (hwt : Semantics.stmtWt Γ L stmt = some Γ') :
    ¬ Rules.ruleApplies m stmt ↔ ResidueShape stmt := by
  constructor
  · intro hn
    rcases coverage_residue m hwt with hc | hr
    · exact absurd hc hn
    · exact hr
  · exact residue_not_covered

end Coverage

/-- **Completeness over the rule-independent fragment**: a `stmtWt`-typed
statement that is not one of the explicitly listed residue shapes has a
first step under either modality.  Unlike `RuleStep.step_of_ruleApplies`
(whose hypothesis *is* "some rule's condition holds"), the hypotheses here
never mention the rules: the fragment is the type checker's language minus
the 24 syntactic `ResidueShape` constructors. -/
theorem RuleStep.complete_of_wellTyped (m : Modality) {Γ Γ' : Semantics.Ctx}
    {L : Semantics.Layout} {stmt : Stmt}
    (hwt : Semantics.stmtWt Γ L stmt = some Γ')
    (hres : ¬ Coverage.ResidueShape stmt) :
    ∃ cond rhs, cond ∧ RuleStep (.ofModality m) stmt cond rhs :=
  (Coverage.coverage_residue m hwt).elim
    (RuleStep.step_of_ruleApplies m stmt)
    (fun h => absurd h hres)
end Solidity
