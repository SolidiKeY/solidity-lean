import Solidity.Backend.Passes.CheckedAdditionReachedOverflow
import Solidity.Backend.PrimitivePackets.CheckedAdd.Controls

namespace Solidity.Backend.Passes.CheckedAdditionReachedOverflow.Controls
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets
open CheckedAdd.Controls
open CompileExamples (C)
def initial := Fixture.machine (W-1) 0 (by decide) (by decide)
def maximum : Word := .val ⟨W-1,by decide⟩
def captured (tail : List Word) := writeMachine {initial with stack := tail} 6 maximum

def joint := reached (.user "sum") (.user "again") .here (.there .here)
  (Fixture.target (W-1) 0 (by decide) (by decide))
  (Fixture.represented (W-1) 0 (by decide) (by decide)) (by decide)
  (W-1) 0 (Fixture.nat_range (W-1) (by decide)) (Fixture.nat_range 0 (by decide))
  rfl rfl (by decide) (by decide)

theorem prefix_run (tail : List Word) :
    run (CheckedAdditionCapture.selected (C:=C) 0 Fixture.F (.user "sum")
      .here (.there .here)).code {initial with stack := tail} = .ok (captured tail) 0 := by
  exact CheckedAdditionCapture.capture_after 0 Fixture.F (.user "sum") .here (.there .here)
    {initial with stack := tail} maximum (Fixture.maximum tail)

/-- The physical captured prefix, not a replacement machine, is consumed. -/
theorem physical_terminal (tail : List Word) :
    run (CheckedAdditionCapture.selected (C:=C) 0 (Fixture.F.push (.val .uint) .ok)
      (.user "again") .here (.there .here)).code (captured tail) = .revert ∧
    run (selected (C:=C) 0 Fixture.F (.user "sum") (.user "again")
      .here (.there .here)).code {initial with stack := tail} = .revert := by
  rcases joint with ⟨_,_,_,_,canonical,outBase,_,allTails⟩
  rcases allTails tail with ⟨_,prefixRun,_,_,suffixRun,wholeRun⟩
  simp only [Compilation.code] at prefixRun suffixRun
  have equalRuns := (prefix_run tail).symm.trans prefixRun
  have same : captured tail = {canonical with stack := tail} := by
    injection equalRuns
  rw [←same] at suffixRun
  exact ⟨suffixRun,wholeRun⟩

def cells : List Nat := [0,1,2,3,4,5,6,7,16,17,18,20,21]
theorem complete_prefix (tail : List Word) :
    cells.map (captured tail).mem =
      [w[20],w[16],w[16],w[0],w[0],maximum,maximum,w[0],w[2],w[7],w[9],w[1],w[4]] ∧
    (captured tail).stack = tail := by
  exact ⟨by change cells.map (captured []).mem = _; decide,rfl⟩

theorem capture_is_reached (tail : List Word) :
    (captured tail).mem 6 ≠ initial.mem 6 := by
  change (captured []).mem 6 ≠ initial.mem 6
  decide

/-- Moving the doubling before capture fails immediately, rather than after
an observed successful prefix. It is still actual typed selected code. -/
theorem wrong_order (tail : List Word) :
    run (CheckedAdditionCapture.selected (C:=C) 0 Fixture.F (.user "wrong")
      .here .here).code {initial with stack := tail} = .revert := by
  have failed := CheckedAdd.value_overflow
    (Fixture.target (W-1) 0 (by decide) (by decide)) .here .here (W-1) (W-1)
    (Fixture.nat_range (W-1) (by decide)) (Fixture.nat_range (W-1) (by decide))
    rfl rfl (by decide)
  have intrinsic := CheckedAdditionCapture.intrinsic_revert (.user "wrong") .here .here _ failed
  exact (compilation_revert_iff (.memory (CheckedAdditionCapture.selected 0 Fixture.F
    (.user "wrong") .here .here))
      (CheckedAdditionCapture.input (.user "wrong") .here .here
        ((Fixture.represented (W-1) 0 (by decide) (by decide)).stack tail) (by decide))
      (by rfl)).mpr (Or.inl intrinsic)

theorem insufficient_suffix_frame (state : State C (.val .uint :: Fixture.Γ))
    (base : Nat → Fin W) (machine : Machine) :
    ¬ (Compilation.memory (CheckedAdditionCapture.selected (C:=C) 0
      (Fixture.F.push (.val .uint) .ok) (.user "again") .here (.there .here))).Input
        1 7 base state machine := by
  intro h
  have bound := h.2.1
  change 8 ≤ 7 at bound
  omega

#print axioms joint
#print axioms prefix_run
#print axioms wrong_order
end Solidity.Backend.Passes.CheckedAdditionReachedOverflow.Controls
