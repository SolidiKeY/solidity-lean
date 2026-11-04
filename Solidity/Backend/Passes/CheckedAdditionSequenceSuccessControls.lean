import Solidity.Backend.Passes.CheckedAdditionSequenceSuccess
import Solidity.Backend.Passes.CheckedAdditionCaptureControls

namespace Solidity.Backend.Passes.CheckedAdditionSequenceSuccess.Controls
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets
open CheckedAdd.Controls
open CheckedAdditionReachedOverflow (program selected code_sequence)
open CompileExamples (C)

def initial := Fixture.machine 7 9 (by decide) (by decide)
def next := (Fixture.target 7 9 (by decide) (by decide)).push
  (t:=.val .uint) (Fixture.u 16 (by decide))
def middle := writeMachine initial 6 w[16]
def final := writeMachine middle 7 w[23]

def joint := success (.user "sum") (.user "again") .here (.there .here)
  (Fixture.target 7 9 (by decide) (by decide))
  (Fixture.represented 7 9 (by decide) (by decide)) (by decide)
  7 9 (Fixture.nat_range 7 (by decide)) (Fixture.nat_range 9 (by decide))
  rfl rfl (by decide) (by decide)

def successful_guard := guard_exact (.user "sum") (.user "again") .here (.there .here)
  (Fixture.target 7 9 (by decide) (by decide))
  (Fixture.represented 7 9 (by decide) (by decide)) (by decide)
  7 9 (Fixture.nat_range 7 (by decide)) (Fixture.nat_range 9 (by decide))
  rfl rfl (by decide)
def overflowing_guard := guard_exact (.user "sum") (.user "again") .here (.there .here)
  (Fixture.target (W-1) 0 (by decide) (by decide))
  (Fixture.represented (W-1) 0 (by decide) (by decide)) (by decide)
  (W-1) 0 (Fixture.nat_range (W-1) (by decide)) (Fixture.nat_range 0 (by decide))
  rfl rfl (by decide)

theorem middle_repr : StateRepr 1 0 8 (Fixture.F.push (.val .uint) .ok)
    next CompileExamples.base middle := by
  exact (Fixture.represented 7 9 (by decide) (by decide)).consVal
    (Fixture.u 16 (by decide)) w[16] (ReprV.uint_of (by rfl)) (by decide)

theorem suffix_value (tail : List Word) :
    run (CheckedAdd.selected (C:=C) 0 (Fixture.F.push (.val .uint) .ok)
      .here (.there .here)).code {middle with stack := tail} =
      .ok ({middle with stack := tail}.push w[23]) 0 := by
  obtain ⟨word,repr,ran⟩ := CheckedAdd.target_success next .here (.there .here) 16 7
    (Fixture.nat_range 16 (by decide)) (Fixture.nat_range 7 (by decide)) rfl rfl
    (Fixture.nat_range 23 (by decide)) middle_repr tail
  rcases repr with ⟨actual,rfl,content⟩
  have same : actual = (⟨23,by decide⟩ : Fin W) := by
    apply Fin.ext
    change actual.val = 23
    change (23:Int) = actual.val at content
    omega
  rw [same] at ran
  exact ran

theorem suffix_run (tail : List Word) :
    run (CheckedAdditionCapture.selected (C:=C) 0 (Fixture.F.push (.val .uint) .ok)
      (.user "again") .here (.there .here)).code {middle with stack := tail} =
      .ok {final with stack := tail} 0 := by
  exact CheckedAdditionCapture.capture_after 0 (Fixture.F.push (.val .uint) .ok)
    (.user "again") .here (.there .here) {middle with stack := tail} w[23] (suffix_value tail)

theorem whole_run (tail : List Word) :
    run (selected (C:=C) 0 Fixture.F (.user "sum") (.user "again")
      .here (.there .here)).code {initial with stack := tail} =
      .ok {final with stack := tail} 0 := by
  have firstRun := CheckedAdditionCapture.Controls.capture_run tail
  change run (CheckedAdditionCapture.selected (C:=C) 0 Fixture.F (.user "sum")
    .here (.there .here)).code {initial with stack := tail} =
    .ok {middle with stack := tail} 0 at firstRun
  rw [code_sequence,run_append_ok firstRun]
  exact suffix_run tail

def cells : List Nat := [0,1,2,3,4,5,6,7,8,16,17,18,20,21]
theorem complete_observations (tail : List Word) :
    cells.map {final with stack := tail}.mem =
      [w[20],w[16],w[16],w[0],w[9],w[7],w[16],w[23],w[0],w[2],w[7],w[9],w[1],w[4]] ∧
    {final with stack := tail}.stack = tail := by
  exact ⟨by change cells.map final.mem = _; decide,rfl⟩

theorem captured_readback (tail : List Word) :
    run [.mload 6] {final with stack := tail} =
      .ok ({final with stack := tail}.push w[16]) 0 := by
  rfl

theorem wrong_recapture (tail : List Word) : {final with stack := tail}.mem 6 ≠ w[23] := by
  change final.mem 6 ≠ w[23]
  decide

theorem skipped_suffix : middle.mem 7 ≠ final.mem 7 := by decide

theorem corrupted_tail :
    run ((selected (C:=C) 0 Fixture.F (.user "sum") (.user "again")
      .here (.there .here)).code ++ [.pop]) {initial with stack := [w[99]]} =
      .ok {final with stack := []} 0 := by
  rw [run_append_ok (whole_run [w[99]])]
  rfl

#print axioms joint
#print axioms whole_run
end Solidity.Backend.Passes.CheckedAdditionSequenceSuccess.Controls
