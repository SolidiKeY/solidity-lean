import Solidity.Backend.Passes.CheckedAdditionCapture
import Solidity.Backend.PrimitivePackets.CheckedAdd.Controls

namespace Solidity.Backend.Passes.CheckedAdditionCapture.Controls
open Evm Evm.Memory
open Solidity.Backend.PrimitivePackets.CheckedAdd.Controls
open Source.SemanticsExamples (G0 F0)
open CompileExamples (C)
def capturedCode := (selected (C:=C) 0 Fixture.F (.user "sum") .here (.there .here)).code
def initial := Fixture.machine 7 9 (by decide) (by decide)
def final (tail : List Word) := writeMachine {initial with stack := tail} 6 w[16]
theorem capture_run (tail : List Word) :
    run capturedCode {initial with stack := tail} = .ok (final tail) 0 := by
  exact capture_after 0 Fixture.F (.user "sum") .here (.there .here)
    {initial with stack := tail} w[16] (Fixture.regular tail)

def joint (p : Roadmap.Pipeline) :=
  success (G0 p) F0 0 (Fixture.source 7 9 (by decide) (by decide))
    (Fixture.target 7 9 (by decide) (by decide)) Fixture.si Fixture.ti
    (Fixture.family 7 9 (by decide) (by decide)) false true 7 9
    (Fixture.nat_range 7 (by decide)) (Fixture.nat_range 9 (by decide)) rfl rfl
    (Fixture.nat_range 16 (by decide)) (.user "sum")
    (Fixture.represented 7 9 (by decide) (by decide)) (by decide)
def jointOverflow (p : Roadmap.Pipeline) :=
  overflow (G0 p) F0 0 (Fixture.source (W-1) 1 (by decide) (by decide))
    (Fixture.target (W-1) 1 (by decide) (by decide)) Fixture.si Fixture.ti
    (Fixture.family (W-1) 1 (by decide) (by decide)) false true (W-1) 1
    (Fixture.nat_range (W-1) (by decide)) (Fixture.nat_range 1 (by decide)) rfl rfl
    (by decide) (.user "sum") (Fixture.represented (W-1) 1 (by decide) (by decide)) (by decide)
def cells : List Nat := [0,1,2,3,4,5,6,7,16,17,18,20,21]
theorem complete_observations (tail : List Word) :
    cells.map (final tail).mem =
      [w[20],w[16],w[16],w[0],w[9],w[7],w[16],w[0],w[2],w[7],w[9],w[1],w[4]] ∧
    (final tail).stack = tail := by
  exact ⟨by change cells.map (final []).mem = _; decide,rfl⟩
theorem skipped_capture (tail : List Word) :
    run Fixture.sumCode {initial with stack := tail} =
      .ok ({initial with stack := tail}.push w[16]) 0 ∧ initial.mem 6 ≠ w[16] := by
  exact ⟨Fixture.regular tail,by decide⟩
theorem wrong_value (tail : List Word) : (final tail).mem 6 ≠ w[15] := by
  change (final []).mem 6 ≠ w[15]
  decide
theorem corrupted_saved_tail :
    run (capturedCode ++ [.pop]) {initial with stack := [w[99]]} =
      .ok (final []) 0 := by
  rw [run_append_ok (capture_run [w[99]])]
  rfl
#print axioms capture_run
#print axioms joint
#print axioms jointOverflow
end Solidity.Backend.Passes.CheckedAdditionCapture.Controls
