import Solidity.Examples.Decision

/-!
# Fresh memory arrays and given-heap parameter witnesses (M7)

`decideLeaf` (`Calculus/Decision.lean`) on leaves that bind fresh arrays of
primitives (`Fml.allocAll`), over `Gaps` of `Examples/Decision.lean`: the
counterexample once pinned there (`gapMemory`) and one leaf per shape the
cut takes (`Calculus/MemSwap.lean`).  The given-heap parameter witness and alias controls are below. The verdicts are the compiled ones;
coverage and the fragment are the kernel's.  The verdicts run one after
another, as `Examples/Decision.lean`'s do.
-/

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-! ### Fresh memory arrays (M7, plan step 6)

A leaf binding fresh arrays of primitives (`Fml.allocAll`, any contents)
whose reads `decideLeafA` refuses: each binder read as its length's word,
each read as a word of its own, under what actual arrays make of them
(`Fml.mxTop`, `Calculus/MemSwap.lean`: two reads at equal indices one word,
a read past the length `⊥`).  Exact at every state (`Fml.mxTop_holds`), so a
refutation of the cut leaf refutes the leaf, its arrays any. -/

section MemPins

/-- A dynamic array's length and element, read off a fresh local. -/
def mlenG {Γ : Ctx} (i : Idx Γ (.mem (.array (.prim .uint)))) : Tm Gaps Γ (.val .uint) :=
  .app2 .mlen (.app0 .memory) (.pvI i)
def mrdG {Γ : Ctx} {R : RefTy} (a : ArrTy R (.prim .uint)) (i : Idx Γ (.mem R))
    (e : Tm Gaps Γ (.val .uint)) : Tm Gaps Γ (.val .uint) :=
  .app2 .read (.app0 .memory) (.app2 (.mat a) (.pvI i) e)
def eqB {Γ : Ctx} (a b : Tm Gaps Γ (.val .uint)) : Tm Gaps Γ (.val .bool) := .app2 (.binop .eqB rfl) a b
def gtB {Γ : Ctx} (a b : Tm Gaps Γ (.val .uint)) : Tm Gaps Γ (.val .bool) := .app2 (.binop .gt rfl) a b
abbrev UA : RefTy := .array (.prim .uint)

/-- A read at a parameter index, read twice: proved. -/
def memSame : Fml Gaps [] := allU (.allocAll (.user "s") UA
  (.imp (.eq (mrdG .dyn .here (.pvV (.there .here))) (litU 5)) (.eq (mrdG .dyn .here (.pvV (.there .here))) (litU 5))))
/-- Reads at equal indices read one word (`i == j`): proved; without it,
refuted. -/
def memAck : Fml Gaps [] := .all (.user "i") .uint (.all (.user "j") .uint (.allocAll (.user "s") UA
  (.imp (isT (eqB (.pvV (.there (.there .here))) (.pvV (.there .here))))
    (.imp (.eq (mrdG .dyn .here (.pvV (.there (.there .here)))) (litU 5))
      (.eq (mrdG .dyn .here (.pvV (.there .here))) (litU 5))))))
def memAckBad : Fml Gaps [] := .all (.user "i") .uint (.all (.user "j") .uint (.allocAll (.user "s") UA
  (.imp (.eq (mrdG .dyn .here (.pvV (.there (.there .here)))) (litU 5))
    (.eq (mrdG .dyn .here (.pvV (.there .here))) (litU 5)))))
/-- Two fresh arrays are apart: refuted. -/
def memApart : Fml Gaps [] := .allocAll (.user "s") UA (.allocAll (.user "t") UA
  (.imp (.eq (mrdG .dyn (.there .here) (litU 0)) (litU 1)) (.eq (mrdG .dyn .here (litU 0)) (litU 1))))
/-- Below the length a read returns (proved); past it, it halts (refuted at
length `0`); the Theory's `==` of two reads that halt alike holds (proved). -/
def memInRange : Fml Gaps [] := .allocAll (.user "s") UA
  (.imp (isT (gtB (mlenG .here) (litU 3))) (isT (eqB (mrdG .dyn .here (litU 2)) (mrdG .dyn .here (litU 2)))))
def memPast : Fml Gaps [] := .allocAll (.user "s") UA
  (isT (eqB (mrdG .dyn .here (litU 0)) (mrdG .dyn .here (litU 0))))
def memHalts : Fml Gaps [] := .allocAll (.user "s") UA (.eq (mrdG .dyn .here (litU 0)) (mrdG .dyn .here (litU 0)))
/-- A fixed array `uint[3]`: read below its length (proved), past it
(refuted). -/
def memFixed : Fml Gaps [] := .allocAll (.user "s") (.fixed (.prim .uint) 3)
  (isT (eqB (mrdG .fixed .here (litU 2)) (mrdG .fixed .here (litU 2))))
def memFixedPast : Fml Gaps [] := .allocAll (.user "s") (.fixed (.prim .uint) 3)
  (isT (eqB (mrdG .fixed .here (litU 3)) (mrdG .fixed .here (litU 3))))
/-- Two fresh arrays' lengths: any, so not equal (refuted). -/
def memLenEq : Fml Gaps [] := .allocAll (.user "s") UA (.allocAll (.user "t") UA
  (.eq (mlenG (.there .here)) (mlenG .here)))
/-- A `bool[]`: an element that reads `true` is below the length (proved). -/
def memBools : Fml Gaps [] := allU (.allocAll (.user "s") (.array (.prim .bool))
  (.imp (.eq (.app2 .read (.app0 .memory) (.app2 (.mat .dyn) (.pvI .here) (.pvV (.there .here))))
      (.app0 (.lit (p := .bool) true)))
    (isT (gtB (.app2 .mlen (.app0 .memory) (.pvI .here)) (.pvV (.there .here))))))

end MemPins

/-- info: "refuted" -/
#guard_msgs in #eval verdict gapMemory
/-- info: "proved" -/
#guard_msgs in #eval verdict memSame
/-- info: "proved" -/
#guard_msgs in #eval verdict memAck
/-- info: "refuted" -/
#guard_msgs in #eval verdict memAckBad
/-- info: "refuted" -/
#guard_msgs in #eval verdict memApart
/-- info: "proved" -/
#guard_msgs in #eval verdict memInRange
/-- info: "refuted" -/
#guard_msgs in #eval verdict memPast
/-- info: "proved" -/
#guard_msgs in #eval verdict memHalts
/-- info: "proved" -/
#guard_msgs in #eval verdict memFixed
/-- info: "refuted" -/
#guard_msgs in #eval verdict memFixedPast
/-- info: "refuted" -/
#guard_msgs in #eval verdict memLenEq
/-- info: "proved" -/
#guard_msgs in #eval verdict memBools

-- Each in the named fragment.
/-- info: true -/
#guard_msgs in
#eval ([memSame, memAck, memAckBad, memApart, memInRange, memPast, memHalts, memFixed,
  memFixedPast, memLenEq, memBools].map (Fml.inTarget {})).all id

/-- Kernel-checked coverage: the counterexample once pinned, and Ackermann's
premise. -/
theorem gapMemory_covered : gapMemory.Covered = true := by decide +kernel
theorem memAck_covered : memAck.Covered = true := by decide +kernel
theorem memAck_inTarget : memAck.inTarget {} = true := by decide +kernel

/-- `decideLeaf_complete`, applied: `gapMemory` is answered. -/
theorem gapMemory_answers : decideLeaf gapMemory ≠ .unknown := decideLeaf_complete gapMemory_covered

/-- `decideLeaf_proved_iff`, applied: the verdict on Ackermann's premise is exact. -/
theorem memAck_iff : decideLeaf memAck = .proved ↔ Fml.Valid memAck :=
  decideLeaf_proved_iff memAck_covered

/-- info: 'Solidity.Examples.Decision.memAck_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memAck_iff


/-! ### An index bound after its array (feature 23)

`∀ fresh s. len(s) > 0 → ∀ i. i < len(s) → s[i] == 0` binds `i` after `s`.
Universal value binders move out of consequents, conjuncts and fresh
objects' binders at every state (`Fml.hoist`, `Calculus/MemHoist.lean`), so
it is read as `∀ i. ∀ fresh s. …` and cut as the others: refuted (the
contents are any).  With Ackermann's premise it holds. -/

/-- `∀ fresh s. s[0] == 5 → ∀ i. i == 0 → s[i] == 5`: proved. -/
def memInnerAck : Fml Gaps [] := .allocAll (.user "s") UA
  (.imp (.eq (mrdG .dyn .here (litU 0)) (litU 5))
    (.all (.user "i") .uint (.imp (isT (eqB (.pvV .here) (litU 0)))
      (.eq (mrdG .dyn (.there .here) (.pvV .here)) (litU 5)))))

/-! ### Writes in a leaf's update (feature 24)

`{memory := write(memory, s[e], v)}` over fresh arrays: each read of the
written local at an index `e₁` the table holds reads `e₁ == e ? v : w`
afterwards, two locals name two objects (`MxRel.apart`), and the update
halts exactly where a write's index is not below its bound or its value
does not return (`mxGuard`, `MxW.guard_iff`): a box reads it as a premise, a
diamond as a conjunct. -/

/-- The update `{memory := write(memory, s[k], v)}`. -/
def wrU {Γ : Ctx} (i : Idx Γ (.mem UA)) (k v : Nat) : Upd Gaps Γ Γ :=
  .snoc .nil (.memory (.app3 .write (.app0 .memory) (.app2 (.mat .dyn) (.pvI i) (litU k))
    (.app1 .mval (litU v))))

/-- `∀ fresh s. len(s) > 0 → [s[0] := 5] s[0] == 6`: refuted. -/
def memWriteBad : Fml Gaps [] := .allocAll (.user "s") UA
  (.imp (isT (gtB (mlenG .here) (litU 0)))
    (.upd .box (wrU .here 0 5) (.eq (mrdG .dyn .here (litU 0)) (litU 6))))
/-- `∀ fresh s. s[0] == 7 → [s[1] := 5] s[0] == 7`: proved (a write
elsewhere keeps the element). -/
def memWriteOther : Fml Gaps [] := .allocAll (.user "s") UA
  (.imp (.eq (mrdG .dyn .here (litU 0)) (litU 7))
    (.upd .box (wrU .here 1 5) (.eq (mrdG .dyn .here (litU 0)) (litU 7))))
/-- `∀ fresh s. ⟨s[0] := 5⟩ s[0] == 5`: refuted (an empty array halts the
write). -/
def memWriteDia : Fml Gaps [] := .allocAll (.user "s") UA
  (.upd .diamond (wrU .here 0 5) (.eq (mrdG .dyn .here (litU 0)) (litU 5)))

/-! ### Original memory gaps

Each remains in `Fml.inTarget` (by the kernel). The negative block is now
refuted by exact preparation and the hidden memory parameter by its given-heap
witness; the fresh struct remains `unknown`
(`docs/automation.md`, M7, "What is not proved"): a negative-position block
over an array's contents (its index bound after the array), a hidden memory
binder (it ranges over the objects already there, and over none), a fresh
struct's member (the cut takes arrays of primitives). -/

/-- `∀ fresh s. len(s) > 0 → [s[0] := 5] s[0] == 5`: proved (feature 24). -/
def gapMemWrite : Fml Gaps [] := .allocAll (.user "s") UA
  (.imp (isT (gtB (mlenG .here) (litU 0)))
    (.upd .box (wrU .here 0 5) (.eq (mrdG .dyn .here (litU 0)) (litU 5))))
def gapMemInner : Fml Gaps [] := .allocAll (.user "s") UA
  (.imp (isT (gtB (mlenG .here) (litU 0)))
    (.all (.user "i") .uint (.imp (isT (gtB (mlenG (.there .here)) (.pvV .here)))
      (.eq (mrdG .dyn (.there .here) (.pvV .here)) (litU 0)))))
def gapMemParam : Fml Gaps [] := .bind .box (.user "s") (.mem UA)
  (.imp (isT (gtB (mlenG .here) (litU 0))) (.eq (mrdG .dyn .here (litU 0)) (litU 0)))
def gapMemStruct : Fml StandardExample [] := .allocAll (.user "p") (.struct "Person")
  (.eq (.app2 .read (.app0 .memory)
      (.app1 (.mfield (s := "Person") (f := "age") (T := .prim .uint) (by decide)) (.pvI .here)))
    (.app0 (.lit (uintOfNat 0))))

/-- A negative-position block over a fresh array's contents (Bradley,
Manna and Sipma over a memory array, its length in the index set): not
moved out, so its index is bound after the array. -/
def gapMemInnerNeg : Fml Gaps [] := .allocAll (.user "s") UA
  (.imp (.all (.user "i") .uint (.imp (isT (gtB (mlenG (.there .here)) (.pvV .here)))
      (.eq (mrdG .dyn (.there .here) (.pvV .here)) (litU 0))))
    (.eq (mrdG .dyn .here (litU 0)) (litU 0)))

theorem gapMemInnerNeg_inTarget : gapMemInnerNeg.inTarget {} = true := by decide +kernel
theorem gapMemWrite_inTarget : gapMemWrite.inTarget {} = true := by decide +kernel
theorem gapMemInner_inTarget : gapMemInner.inTarget {} = true := by decide +kernel
theorem gapMemParam_inTarget : gapMemParam.inTarget {} = true := by decide +kernel
theorem gapMemStruct_inTarget : gapMemStruct.inTarget {} = true := by decide +kernel

/-- info: ["refuted", "refuted", "unknown"] -/
#guard_msgs in
#eval [verdict gapMemInnerNeg, verdict gapMemParam, verdict gapMemStruct]

/-! The index bound after its array, decided (feature 23). -/

/-- info: ["refuted", "proved"] -/
#guard_msgs in #eval [verdict gapMemInner, verdict memInnerAck]

theorem gapMemInner_covered : gapMemInner.Covered = true := by decide +kernel
theorem memInnerAck_covered : memInnerAck.Covered = true := by decide +kernel
theorem memInnerAck_inTarget : memInnerAck.inTarget {} = true := by decide +kernel
theorem gapMemInner_answers : decideLeaf gapMemInner ≠ .unknown := decideLeaf_complete gapMemInner_covered

/-! The writes in a leaf's update, decided (feature 24). -/

/-- info: ["proved", "refuted", "proved", "refuted"] -/
#guard_msgs in
#eval [verdict gapMemWrite, verdict memWriteBad, verdict memWriteOther, verdict memWriteDia]

theorem gapMemWrite_covered : gapMemWrite.Covered = true := by decide +kernel
theorem memWriteBad_covered : memWriteBad.Covered = true := by decide +kernel
theorem memWriteDia_covered : memWriteDia.Covered = true := by decide +kernel
theorem memWriteBad_inTarget : memWriteBad.inTarget {} = true := by decide +kernel
theorem gapMemWrite_answers : decideLeaf gapMemWrite ≠ .unknown := decideLeaf_complete gapMemWrite_covered

/-- `decideLeaf_proved_iff`, applied: the verdict on the write is exact. -/
theorem gapMemWrite_iff : decideLeaf gapMemWrite = .proved ↔ Fml.Valid gapMemWrite :=
  decideLeaf_proved_iff gapMemWrite_covered

/-- info: 'Solidity.Examples.Decision.gapMemWrite_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gapMemWrite_iff


/-! ### Given-heap memory parameters

The original binder and its inTarget certificate above are unchanged.
The countermodel has an existing array [1], while the empty heap satisfies
the pin. Both modalities bind universally, including unset. -/

section MemoryParameters

local instance memoryParameterContract : InContract := ⟨Gaps⟩
open scoped Solidity.Scoped

/-- A repeated Theory read is equal even at an unset memory parameter. -/
def memParamSame : Fml Gaps [] :=
  dl![.box]{ s[0] = s[0] where uint[] memory s }

/-- Two hidden locals can name the same array; no fresh-apart premise exists. -/
def memParamAliasBad : Fml Gaps [] :=
  dl![.box]{ (s[0] = 1 → t[0] = 2 where uint[] memory t) where uint[] memory s }

/-- The original parameter leaf holds at the empty heap, so that state
cannot certify its refutation. -/
theorem gapMemParam_empty : holds (State.init Gaps) gapMemParam := by
  intro v
  cases v with
  | none => intro h; cases h
  | some r =>
    have hr : ([] : HTy)[r.id]? = some UA := r.get?
    cases hr

/-- The given-heap witness really refutes the unchanged parameter leaf. -/
theorem gapMemParam_countermodel :
    ¬ holds (MemoryWitness.candidate Gaps) gapMemParam :=
  MemoryWitness.Checked.refutes
    (gapMemParam.checkMemoryAt (MemoryWitness.candidate Gaps)) (by decide +kernel)

/-- The original pin's exact decision, checked in the kernel. -/
theorem gapMemParam_verdict : verdict gapMemParam = "refuted" := by
  decide +kernel

/-- Repeated reads remain valid over every given heap and every binder value. -/
theorem memParamSame_valid : Fml.Valid memParamSame := by
  intro σ v
  rfl

/-- The concrete checker includes unset when validating the positive control. -/
theorem memParamSame_checked :
    (memParamSame.checkMemoryAt (MemoryWitness.candidate Gaps)).isYes = true := by
  decide +kernel

/-- Aliasing is a genuine countermodel, not an implicit freshness condition. -/
theorem memParamAliasBad_countermodel :
    ¬ holds (MemoryWitness.candidate Gaps) memParamAliasBad :=
  MemoryWitness.Checked.refutes
    (memParamAliasBad.checkMemoryAt (MemoryWitness.candidate Gaps)) (by decide +kernel)

/-- Two independent references to identity 0, a distinct object at identity 1,
and read observations before/after s[0] = 7, including an untouched index. -/
def memoryAliasTrace (a b : MemoryWitness.Words .uint) :
    List Nat × List (Option Nat) × List (Option Int) × List (Option Int) :=
  let ws := [a, b]
  let H := MemoryWitness.typing ws
  let hp : Heap H := MemoryWitness.objects H ws
  let s := MemoryWitness.reference ws ⟨0, Nat.zero_lt_succ 1⟩
  let t := MemoryWitness.reference ws ⟨1, Nat.lt_succ_self 1⟩
  let alias : HRef H UA := ⟨0, by rfl⟩
  let addrOf (r : HRef H UA) (i : Nat) : MAddr H (.prim .uint) :=
    .index r .dyn (uintOfNat i)
  let rd (h : Heap H) (r : HRef H UA) (i : Nat) : Option Int :=
    (Heap.readAddr h (addrOf r i)).map (fun v => v.1)
  ([s.id, alias.id, t.id],
    (MemoryWitness.values H UA).map (fun r => r.map HRef.id),
    [rd hp s 0, rd hp s 1, rd hp t 0, rd hp t 1],
    match Heap.writeAddr hp (addrOf s 0) (uintOfNat 7) with
    | none => [none, none, none, none, none]
    | some hp' => [rd hp' s 0, rd hp' alias 0, rd hp' s 1, rd hp' t 0, rd hp' t 1])

/-- Equal contents do not identify distinct objects: writes follow identities. -/
theorem memoryAlias_equalContents :
    memoryAliasTrace ⟨[uintOfNat 1, uintOfNat 3], by decide⟩
      ⟨[uintOfNat 1, uintOfNat 3], by decide⟩ =
      ([0, 0, 1], [some 0, some 1, none],
        [some 1, some 3, some 1, some 3],
        [some 7, some 7, some 3, some 1, some 3]) := by
  decide +kernel

/-- Different contents and an untouched index retain their complete observations. -/
theorem memoryAlias_differentContents :
    memoryAliasTrace ⟨[uintOfNat 1, uintOfNat 3], by decide⟩
      ⟨[uintOfNat 2, uintOfNat 4], by decide⟩ =
      ([0, 0, 1], [some 0, some 1, none],
        [some 1, some 3, some 2, some 4],
        [some 7, some 7, some 3, some 2, some 4]) := by
  decide +kernel

/-- Empty and wrong-type heaps still admit the unset binder value. -/
theorem memoryParameter_emptyDomains :
    (MemoryWitness.values [] UA).map (fun r => r.map HRef.id) = [none] ∧
    (MemoryWitness.values (MemoryWitness.candidate Gaps).H (.array (.prim .bool))).map
      (fun r => r.map HRef.id) = [none] := by
  decide +kernel

/-- info: ["unknown", "refuted"] -/
#guard_msgs in #eval [verdict memParamSame, verdict memParamAliasBad]
/-- info: [true, true] -/
#guard_msgs in #eval [(memParamSame.checkMemoryAt (MemoryWitness.candidate Gaps)).isYes,
  (memParamAliasBad.checkMemoryAt (MemoryWitness.candidate Gaps)).isNo]
/-- info: ([0, 0, 1], [some 0, some 1, none], [some 1, some 3, some 1, some 3], [some 7, some 7, some 3, some 1, some 3]) -/
#guard_msgs in #eval memoryAliasTrace ⟨[uintOfNat 1, uintOfNat 3], by decide⟩
  ⟨[uintOfNat 1, uintOfNat 3], by decide⟩
/-- info: ([0, 0, 1], [some 0, some 1, none], [some 1, some 3, some 2, some 4], [some 7, some 7, some 3, some 2, some 4]) -/
#guard_msgs in #eval memoryAliasTrace ⟨[uintOfNat 1, uintOfNat 3], by decide⟩
  ⟨[uintOfNat 2, uintOfNat 4], by decide⟩
/-- info: 'Solidity.Examples.Decision.gapMemParam_countermodel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gapMemParam_countermodel
/-- info: 'Solidity.Examples.Decision.gapMemParam_verdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gapMemParam_verdict
/-- info: 'Solidity.Examples.Decision.memParamSame_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memParamSame_valid
/-- info: 'Solidity.Examples.Decision.memoryAlias_equalContents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memoryAlias_equalContents

/-- info: 'Solidity.Examples.Decision.gapMemParam_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gapMemParam_empty
/-- info: 'Solidity.Examples.Decision.memParamAliasBad_countermodel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memParamAliasBad_countermodel
/-- info: 'Solidity.Examples.Decision.memParamSame_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memParamSame_checked
/-- info: 'Solidity.Examples.Decision.memoryAlias_differentContents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memoryAlias_differentContents
/-- info: 'Solidity.Examples.Decision.memoryParameter_emptyDomains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memoryParameter_emptyDomains

end MemoryParameters

end Solidity.Examples.Decision
