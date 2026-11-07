import Solidity.Backend.PrimitivePackets.SignedCast.Agreement
import Solidity.Backend.MemoryOps.StructDefaults.WordControls
import Solidity.Backend.InternalFlow.RuntimeFrameRestoredRepresentation
import Solidity.Source.SemanticsExamples

/-! Populated caller witness, both Source pipelines, narrowing and widening,
negative/sign-boundary cases, and wrong width/result/tail controls. -/
namespace Solidity.Backend.PrimitivePackets.SignedCast.Controls
open Evm Evm.Memory Solidity.Lowering.V07
open Source.SemanticsExamples (E0 G0 F0 s0)
namespace Seed
abbrev C := Backend.MemoryOps.StructDefaults.WordControls.C
abbrev initial := Backend.MemoryOps.StructDefaults.WordControls.initial
abbrev machine := Backend.MemoryOps.StructDefaults.WordControls.machine
abbrev bases := Backend.MemoryOps.StructDefaults.WordControls.bases
abbrev represented := Backend.MemoryOps.StructDefaults.WordControls.initial_repr
end Seed
abbrev C := Seed.C
abbrev Γ : Ctx := [.val .int]
abbrev F := Frag.init Γ
abbrev T := ty 16 (by decide)
def target (x : Int) (hx : T.lo ≤ x ∧ x ≤ T.hi) : State C Γ :=
  Seed.initial.push (t:=.val .int) (integerValue T x hx)
def machine (x : Int) : Machine := writeMachine Seed.machine 1 (.val (sword x))
def source (x : Int) (hx : T.lo ≤ x ∧ x ≤ T.hi) : Source.EMState E0 [.int T] :=
  (.cons (.int x hx) .nil,s0)
def si (_ : Unit) : Source.Idx [.int T] (.int T) := .here
def ti (_ : Unit) : Idx Γ (.val .int) := .here

theorem family (x : Int) (hx : T.lo ≤ x ∧ x ≤ T.hi) :
    IntegerLocalFamily T si ti (source x hx).1 (target x hx).env := by
  constructor
  · intro k; exact integer_related _ _ _
  · intro k l; cases k; cases l; rfl

theorem represented (x : Int) (hx : T.lo ≤ x ∧ x ≤ T.hi) :
    StateRepr 1 1 64 F (target x hx) Seed.bases (machine x) := by
  exact Seed.represented.1.consVal (integerValue T x hx) (.val (sword x))
    (ReprV.int_word _) (by decide)

def application (p : Roadmap.Pipeline) (bits : Nat) (valid : Valid bits)
    (x : Int) (hx : T.lo ≤ x ∧ x ≤ T.hi) (tail : List Word) :=
  success 16 bits (by decide) valid (G0 p) F0 0 (source x hx) (target x hx)
    si ti (family x hx) () x hx rfl (represented x hx) tail

theorem actual (bits : Nat) (valid : Valid bits) (x : Int)
    (hx : T.lo ≤ x ∧ x ≤ T.hi) (tail : List Word) :
    run (selected (C:=C) bits valid 1 F (.here)).code {machine x with stack := tail} =
      .ok ({machine x with stack := tail}.push (.val (sword ((ty bits valid).wrap x)))) 0 := by
  obtain ⟨word,repr,ran⟩ := (application .legacy bits valid x hx tail).2.2
  have same : word = .val (sword ((ty bits valid).wrap x)) :=
    Backend.InternalFlow.RuntimeFrame.Restored.value_unique repr (ReprV.int_word _)
  rw [same] at ran
  exact ran

theorem negative (tail : List Word) :
    run (selected (C:=C) 8 (by decide) 1 F (.here)).code {machine (-129) with stack := tail} =
      .ok ({machine (-129) with stack := tail}.push (.val (sword 127))) 0 := by
  have ran := actual 8 (by decide) (-129) (by decide) tail
  have wrap : (ty 8 (by decide)).wrap (-129) = 127 := by decide
  rw [wrap] at ran
  exact ran

theorem boundary (tail : List Word) :
    run (selected (C:=C) 8 (by decide) 1 F (.here)).code {machine 128 with stack := tail} =
      .ok ({machine 128 with stack := tail}.push (.val (sword (-128)))) 0 := by
  have ran := actual 8 (by decide) 128 (by decide) tail
  have wrap : (ty 8 (by decide)).wrap 128 = -128 := by decide
  rw [wrap] at ran
  exact ran

theorem widening (tail : List Word) :
    run (selected (C:=C) 256 (by decide) 1 F (.here)).code {machine (-32768) with stack := tail} =
      .ok ({machine (-32768) with stack := tail}.push (.val (sword (-32768)))) 0 := by
  have ran := actual 256 (by decide) (-32768) (by decide) tail
  have wrap : (ty 256 (by decide)).wrap (-32768) = -32768 := by decide
  rw [wrap] at ran
  exact ran

def both_pipelines (p : Roadmap.Pipeline) (tail : List Word) :=
  application p 8 (by decide) (-129) (by decide) tail

theorem no_checked_overflow : (ty 8 (by decide)).wrap 128 = -128 := by decide

theorem wrong_unsigned : (sword (-128)) ≠ wmod 128 := by decide +kernel

theorem wrong_width : (ty 8 (by decide)).wrap 128 ≠ (ty 16 (by decide)).wrap 128 := by decide

theorem wrong_signextend_byte :
    Backend.Scalar.run (Backend.Scalar.signedCode ⟨0,by decide⟩) [128,77] ≠
      Backend.Scalar.run (Backend.Scalar.signedCode ⟨1,by decide⟩) [128,77] := by decide +kernel

theorem missing_operand : Backend.Scalar.run (Backend.Scalar.signedCode ⟨0,by decide⟩) [] = none := by decide

theorem saved_tail_wrong (tail : List Word) :
    ({machine (-129) with stack := w[77]::tail}.push w[127]).stack ≠ w[127]::w[78]::tail := by
  intro same
  have wrong := (List.cons.inj (List.cons.inj same).2).1
  exact (by decide : (w[77] : Word) ≠ w[78]) wrong

theorem ordered_memory (x : Int) (tail : List Word) :
    ([0,1,63,64].map ({machine x with stack := tail}.push (.val (sword 127))).mem,
      ({machine x with stack := tail}.push (.val (sword 127))).stack) =
    ([w[128],.val (sword x),w[99],w[0]],.val (sword 127)::tail) := rfl

#print axioms actual
#print axioms negative
#print axioms boundary
#print axioms widening
#print axioms represented
#print axioms wrong_signextend_byte
end Solidity.Backend.PrimitivePackets.SignedCast.Controls
