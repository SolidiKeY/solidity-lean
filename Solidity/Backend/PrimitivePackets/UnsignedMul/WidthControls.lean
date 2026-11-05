import Solidity.Backend.PrimitivePackets.UnsignedMul.Controls

/-! Nonempty physical input for every legal unsigned byte width, with two
independent zero locals. The general theorem, not just this zero control,
handles every in-range operand pair. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedMul.WidthControls
open Evm Evm.Memory Solidity.Lowering.V07
open Solidity.Lowering.V07.UnsignedNarrowing
open Source.SemanticsExamples

def source (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    Source.EMState E0 [.int (ty bits valid),.int (ty bits valid)] :=
  (.cons (.int 0 (ty bits valid).zero_mem) (.cons (.int 0 (ty bits valid).zero_mem) .nil),s0)
def si (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    Bool → Source.Idx [.int (ty bits valid),.int (ty bits valid)] (.int (ty bits valid))
  | false => .here | true => .there .here

theorem family (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    IntegerLocalFamily (ty bits valid) (si bits valid) Controls.ti
      (source bits valid).1 (Controls.target 0 0).env := by
  constructor
  · intro k
    cases k <;> rfl
  · intro k l
    cases k <;> cases l <;> rfl

def application (p : Roadmap.Pipeline) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :=
  execution (G0 p) F0 0 (source bits valid) (Controls.target 0 0) bits valid
    (si bits valid) Controls.ti (family bits valid) false true 0 0
    (ty bits valid).zero_mem (ty bits valid).zero_mem rfl rfl (Controls.represented 0 0)

theorem emitted (p : Roadmap.Pipeline) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (tail : List Word) :
    run (selected (C := Controls.Seed.C) 1 Controls.F bits
      (Controls.ti false) (Controls.ti true)).code {Controls.machine 0 0 with stack := tail} =
        .ok ({Controls.machine 0 0 with stack := tail}.push w[0]) 0 ∧
      StateRepr 1 1 64 Controls.F (Controls.target 0 0) Controls.Seed.bases
        ({Controls.machine 0 0 with stack := tail}.push w[0]) := by
  obtain ⟨word,repr,runs⟩ := (application p bits valid).2.2.2.2
  have expected : ReprV .uint
      (integerValue (ty bits valid) ((ty bits valid).wrap (0*0)) ((ty bits valid).wrap_mem (0*0))) w[0] := by
    apply ReprV.uint_of
    change (ty bits valid).wrap 0 = 0
    exact wrap_of_range bits valid 0 (ty bits valid).zero_mem
  have same : word = w[0] :=
    Solidity.Backend.InternalFlow.RuntimeFrame.Restored.value_unique repr expected
  subst word
  exact runs tail

end Solidity.Backend.PrimitivePackets.UnsignedMul.WidthControls
