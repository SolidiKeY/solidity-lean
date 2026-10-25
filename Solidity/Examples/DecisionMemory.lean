import Solidity.Examples.Decision

/-!
# The closer's decision on fresh memory arrays (M7, plan step 6)

`decideLeaf` (`Calculus/Decision.lean`) on leaves that bind fresh arrays of
primitives (`Fml.allocAll`), over `Gaps` of `Examples/Decision.lean`: the
counterexample once pinned there (`gapMemory`) and one leaf per shape the
cut takes (`Calculus/MemSwap.lean`).  The verdicts are the compiled ones;
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

end Solidity.Examples.Decision
