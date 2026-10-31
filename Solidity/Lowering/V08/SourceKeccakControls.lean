import Solidity.Lowering.V08.SourceKeccak
import Solidity.Lowering.V08.SourceEnvironmentControls
import Solidity.Lowering.V08.CryptoControls

/-! Actual source executions in the retained populated fixture. The only state
change is the evaluator's fresh literal allocation. Mock globals are used only
with their published real Keccak pin; this is not SourceSpec/admission. -/
namespace Solidity.Lowering.V08.SourceKeccakControls
open Solidity
open SourceKeccak SourceEnvironmentControls

def binary : Roadmap.Bytes := [0, 255, 128]
def wide : Roadmap.Bytes := List.replicate 32 255 ++ [128]

theorem binary_execution (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.evalE (global pipeline) frame (horizon + 5) (literal binary)).run
      (locals, populated) =
    (.ok (.val (Source.mkBytes (n := 32) (h := by decide +kernel)
      (Semantics.wordBytes (keccakBytes [0,255,128]).1.toNat))),
      (locals, afterLiteral populated binary)) :=
  eval_transport (global pipeline) Roadmap.Controls.toyFixed_keccak frame horizon binary locals populated

theorem empty_execution (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 5 (literal [])).run (locals, populated) =
    (.ok (.val (Source.mkBytes (n := 32) (h := by decide +kernel)
      (Semantics.wordBytes (keccakBytes []).1.toNat))),
      (locals, afterLiteral populated [])) :=
  eval_transport (global pipeline) Roadmap.Controls.toyFixed_keccak frame 0 [] locals populated

theorem wide_execution (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 5 (literal wide)).run (locals, populated) =
    (.ok (.val (Source.mkBytes (n := 32) (h := by decide +kernel)
      (Semantics.wordBytes (keccakBytes (wide.map (fun b => (b.toNat : Int)))).1.toNat))),
      (locals, afterLiteral populated wide)) :=
  eval_transport (global pipeline) Roadmap.Controls.toyFixed_keccak frame 0 wide locals populated

theorem wide_length : wide.length = 33 := rfl

/-- Every old populated observation remains available through exact ex/events/
logs/fnLocals equality; heap now contains both the old and the fresh object. -/
theorem complete_machine (bytes : Roadmap.Bytes) :
    (afterLiteral populated bytes).ex = populated.ex ∧
    (afterLiteral populated bytes).events = populated.events ∧
    (afterLiteral populated bytes).logs = populated.logs ∧
    (afterLiteral populated bytes).fnLocals = populated.fnLocals ∧
    (afterLiteral populated bytes).heap.next = 2 ∧
    (afterLiteral populated bytes).heap.get 0 = some ⟨.bytes .memory, .bytes [0,255]⟩ ∧
    (afterLiteral populated bytes).heap.get 1 = some ⟨.bytes .memory, .bytes bytes⟩ :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem allocation_is_not_input (bytes : Roadmap.Bytes) :
    afterLiteral populated bytes ≠ populated := by
  intro same
  have next := congrArg (fun s : Source.St E => s.heap.next) same
  change 2 = 1 at next
  contradiction

theorem timeout (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 0 (literal binary)).run (locals, populated) =
      (.error .timeout, (locals, populated)) :=
  zero_horizon (global pipeline) frame binary locals populated

theorem binary_word :
    EnvironmentProjection.liftWord ((global .legacy).fixed.hash binary) =
      keccakBytes [0,255,128] := CryptoControls.fixed_transport

theorem wrong_input :
    EnvironmentProjection.liftWord ((global .legacy).fixed.hash binary) ≠
      keccakBytes [0,255,127] := by
  rw [binary_word]
  exact CryptoControls.wrong_input

theorem empty_word : (keccakBytes []).1 =
    0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 :=
  CryptoControls.empty_hash

theorem wrong_output : (keccakBytes []).1 ≠ 0 := CryptoControls.wrong_hash

/-- A wrong successful bytes32 result is rejected by the actual source run. -/
theorem wrong_source_output (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 5 (literal [])).run (locals, populated) ≠
      (.ok (.val (.fixedBytes (List.replicate 32 0) (by rfl))),
        (locals, afterLiteral populated [])) := by
  intro same
  rw [eval_literal (global pipeline) frame 0, mk_wordBytes] at same
  have number := congrArg (fun result => match result.1 with
    | .ok (.val (.fixedBytes bs _)) => Source.bytesNat bs
    | _ => 0) same
  change Source.bytesNat (Source.wordBytes ((global pipeline).fixed.hash [])) = 0 at number
  rw [word_observation] at number
  apply CryptoControls.wrong_hash
  have fixed : EnvironmentProjection.liftWord ((global pipeline).fixed.hash []) =
      keccakBytes [] := by
    simpa only [List.map_nil] using CryptoObservations.fixed_keccak_observation
      (global pipeline).fixed Roadmap.Controls.toyFixed_keccak []
  calc
    (keccakBytes []).1 = (((global pipeline).fixed.hash []).val : Int) :=
      congrArg Subtype.val fixed.symm
    _ = 0 := congrArg (fun n : Nat => (n : Int)) number

#print axioms wrong_source_output
#print axioms binary_execution
#print axioms empty_execution
#print axioms wide_execution
#print axioms wide_length
#print axioms complete_machine
#print axioms allocation_is_not_input
#print axioms timeout
#print axioms binary_word
#print axioms wrong_input
#print axioms empty_word
#print axioms wrong_output
end Solidity.Lowering.V08.SourceKeccakControls
