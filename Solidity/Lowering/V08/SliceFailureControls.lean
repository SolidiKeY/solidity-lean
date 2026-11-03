import Solidity.Lowering.V08.SliceFailureLowering
import Solidity.Lowering.V08.SourceExternalPhaseControls

namespace Solidity.Lowering.V08.SliceFailureControls
open Solidity Source Backend
open SliceFailureLowering SourceCustomErrorControls

def word (n : Nat) : Roadmap.Word := ⟨n % 2^256,Nat.mod_lt _ (by decide)⟩
def bytesFrame : Fr := {frame with cd := [31,32,255,0,255,33]}
def old := SourceExternalPhaseControls.caller

def bounds (start stop : Nat) : Locals E.layout (context (.bytes .calldata) SourceExternalPhaseControls.ctx) := caller (E := E) rfl 2 3 (word start) (word stop) old

theorem accepted_client :
    (evalE (global .legacy) bytesFrame 4 (expression (.bytes .calldata) rfl false)).run
      (bounds 1 3,populated) =
      (.ok (.val (.cdRef rfl 3 2)),(bounds 1 3,populated)) :=
  accepted _ _ 2 _ rfl rfl 2 3 (word 1) (word 3) (by decide) (by decide) old populated

theorem observed_client :
    ((do let value ← evalE (global .legacy) bytesFrame 4 (expression (.bytes .calldata) rfl false)
         bytesOfRV bytesFrame 2 value) : EM E _ Roadmap.Bytes).run (bounds 1 3,populated) =
      (.ok [0,255],(bounds 1 3,populated)) :=
  observed_bytes _ _ 2 2 3 (word 1) (word 3) (by decide) (by decide) old populated

theorem empty_client :
    (evalE (global .legacy) bytesFrame 4 (expression (.bytes .calldata) rfl false)).run
      (bounds 3 3,populated) =
      (.ok (.val (.cdRef rfl 5 0)),(bounds 3 3,populated)) :=
  accepted _ _ 2 _ rfl rfl 2 3 (word 3) (word 3) (by decide) (by decide) old populated

theorem reversed_client :
    (evalE (global .legacy) bytesFrame 4 (expression (.bytes .calldata) rfl false)).run
      (bounds 3 1,populated) = (.error (.revert []),(bounds 3 1,populated)) :=
  reversed _ _ 2 _ rfl rfl 2 3 (word 3) (word 1) (by decide) old populated

theorem beyond_client :
    (evalE (global .legacy) bytesFrame 4 (expression (.bytes .calldata) rfl false)).run
      (bounds 1 4,populated) = (.error (.revert []),(bounds 1 4,populated)) :=
  beyond _ _ 2 _ rfl rfl 2 3 (word 1) (word 4) (by decide) (by decide) old populated

theorem timeout_client :
    (evalE (global .legacy) bytesFrame 1 (expression (.bytes .calldata) rfl false)).run
      (bounds 3 1,populated) = (.error .timeout,(bounds 3 1,populated)) :=
  exhausted _ _ _ rfl false _ populated

theorem absent_end :
    (evalE (global .legacy) bytesFrame 4 (expression (.bytes .calldata) rfl true)).run
      (bounds 1 (2^256-1),populated) =
      (.ok (.val (.cdRef rfl 3 2)),(bounds 1 (2^256-1),populated)) :=
  accepted_toEnd _ _ 2 _ rfl rfl 2 3 (word 1) _ (by decide) old populated

theorem array_stride :
    (evalE (global .legacy) bytesFrame 4
      (expression (.array .calldata (.int IntTy.u256) none) rfl false)).run
      (caller rfl 2 3 (word 1) (word 3) old,populated) =
      (.ok (.val (.cdRef rfl 34 2)),(caller rfl 2 3 (word 1) (word 3) old,populated)) :=
  accepted _ _ 2 _ rfl rfl 2 3 (word 1) (word 3) (by decide) (by decide) old populated

/-- A logical slice can extend beyond actual input; existing byte observation
then truncates. This is acceptance, not a claimed classified decoder failure. -/
theorem outside_input :
    ((do let value ← evalE (global .legacy) bytesFrame 4 (expression (.bytes .calldata) rfl false)
         bytesOfRV bytesFrame 2 value) : EM E _ Roadmap.Bytes).run
      (caller rfl 100 3 (word 0) (word 2) old,populated) =
      (.ok [],(caller rfl 100 3 (word 0) (word 2) old,populated)) :=
  observed_bytes _ _ 2 100 3 (word 0) (word 2) (by decide) (by decide) old populated

/-- Caller old memory reference and its bytes remain populated. -/
theorem old_alias : old.get (.there (.there .here)) = .memRef rfl 0 := rfl

theorem wrong_byte_order : ([0,255] : Roadmap.Bytes) ≠ [255,0] := by decide +kernel


def machine : Failure.Slice.Machine :=
  ⟨[⟨77,by decide +kernel⟩,⟨88,by decide +kernel⟩],fun k => if k=7 then 231 else 17⟩

theorem empty_fits : Failure.Fits 8 [] :=
  ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

/-- Both Source and target outcomes are actual executions, with populated
source locals/heap and a target stack/memory sentinel. -/
theorem combined :
    (evalE (global .legacy) bytesFrame 4 (expression (.bytes .calldata) rfl false)).run
      (bounds 3 1,populated) = (.error (.revert []),(bounds 3 1,populated)) ∧
    Failure.Slice.checkedRun (Failure.emit 8 .empty ++ [.op .ADD]) machine =
      some ({machine with memory := Failure.Slice.putBytes machine.memory 8 []},some (.revert [])) :=
  lowered_reversed _ _ 2 _ rfl rfl 2 3 (word 3) (word 1) (by decide) old populated
    8 [.op .ADD] machine empty_fits (by decide +kernel)

theorem old_heap : populated.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ := rfl

theorem max_word_reject :
    (evalE (global .legacy) bytesFrame 4 (expression (.bytes .calldata) rfl false)).run
      (bounds 0 (2^256-1),populated) =
      (.error (.revert []),(bounds 0 (2^256-1),populated)) :=
  beyond _ _ 2 _ rfl rfl 2 3 (word 0) (word (2^256-1)) (by decide) (by decide) old populated

theorem wrong_reference :
    (evalE (global .legacy) bytesFrame 4 (expression (.bytes .calldata) rfl false)).run
      (bounds 1 3,populated) ≠
      (.ok (.val (.cdRef rfl 2 2)),(bounds 1 3,populated)) := by
  rw [accepted_client]
  intro equal
  cases equal
end Solidity.Lowering.V08.SliceFailureControls
