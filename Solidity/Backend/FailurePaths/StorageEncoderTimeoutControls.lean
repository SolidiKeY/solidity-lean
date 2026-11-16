import Solidity.Backend.FailurePaths.StorageEncoderTimeout
import Solidity.Source.Semantics
import Solidity.Source.Elaborate

/-! Seeded Source controls distinguish timeout/completion; their Env is not an admitted production caller. -/
namespace Solidity.Backend.FailurePaths.StorageEncoderTimeout.Controls
open Source
open Source.EM
def bytesError : Decl :=
  ⟨.error,"Failure",some "C",false,
    .error "Failure" (.cons (.errorParam (.elem .bytes) none) .nil)⟩
def unit : Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.elem .bytes) none none none false "data" .none)
    (.cons (.error "Failure" (.cons (.errorParam (.elem .bytes) none) .nil)) .nil))) .nil)
def E : Source.Env := unit.env
def path : Source.SPath := ⟨⟨some "C","data"⟩,[]⟩
def frame : Fr :=
  {this:=⟨0,by decide⟩,sender:=⟨1,by decide⟩,value:=⟨0,by decide⟩,static:=false,contract:="C"}
def values : RVals E.layout [.bytes .storage] := .cons (.val (.storRef rfl path)) .nil
def seed : EM E [] Unit := do
  writeLen frame path 2
  writeAt (τ:=.fixedBytes 1 (by decide)) frame (path.go (.index 0)) (.fixedBytes [17] rfl)
  writeAt (τ:=.fixedBytes 1 (by decide)) frame (path.go (.index 1)) (.fixedBytes [34] rfl)
def initial : St E := (seed.run (.nil,St.init E)).2.2
def caller : Locals E.layout [.bytes .storage] := .cons (.storRef rfl path) .nil
def global (pipeline : Roadmap.Pipeline) : Glob E :=
  ⟨Source.progOf E,pipeline,⟨Roadmap.Evm.withKeccak,fun bal _ a => bal a,1,1⟩,fun _ => ⟨0,by decide⟩,
    fun _ _ => true,fun _ => .answer (.success []),⟨0,by decide⟩⟩

theorem actual_incomplete :
    Premises.IncompleteAt (encodeVals frame 2 false values : EM E [] Roadmap.Bytes)
      (.nil,initial) (.nil,initial) :=
  incomplete frame path false (.nil,initial) 17 rfl rfl

theorem actual_local_timeout (pipeline : Roadmap.Pipeline) :
    (evalE (global pipeline) frame 3
      (.abiEncode .encode (.cons (.local .here) .nil))).run (caller,initial) =
      (.error .timeout,(caller,initial)) :=
  local_abi_timeout (global pipeline) frame .here caller initial path 17 rfl rfl rfl

theorem exact_completion :
    (encodeVals frame 4 false values : EM E [] Roadmap.Bytes).run (.nil,initial) =
      (.ok (abiLayout [(true,[17,34])]),(.nil,initial)) :=
  by rfl

def completed : St E :=
  {initial with heap := (initial.heap.alloc
    ⟨.bytes .memory,Data.bytes (abiLayout [(true,[17,34])])⟩).1}

theorem actual_local_completes (pipeline : Roadmap.Pipeline) :
    (evalE (global pipeline) frame 5
      (.abiEncode .encode (.cons (.local .here) .nil))).run (caller,initial) =
      (.ok (.val (.memRef rfl 0)),(caller,completed)) := by rfl

theorem declared_error : bytesError ∈ E.decls := by
  exact .tail _ (.tail _ (.head _))

theorem timeout_not_revert (pipeline : Roadmap.Pipeline) (payload : Roadmap.Bytes) :
    (evalE (global pipeline) frame 3
      (.abiEncode .encode (.cons (.local .here) .nil))).run (caller,initial) ≠
      (.error (.revert payload),(caller,initial)) := by
  rw [actual_local_timeout]
  intro same
  cases same


/-- Error parameters use memory; the storage witness cannot instantiate identity-conversion local-error encoding. -/
theorem error_signature_memory :
    bytesError.paramTys E = some [.bytes .memory] := rfl

theorem error_signature_storage_refused :
    bytesError.paramTys E ≠ some [.bytes .storage] := by decide
/-- info: 'Solidity.Backend.FailurePaths.StorageEncoderTimeout.Controls.actual_incomplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_incomplete
/-- info: 'Solidity.Backend.FailurePaths.StorageEncoderTimeout.Controls.actual_local_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_local_timeout
/-- info: 'Solidity.Backend.FailurePaths.StorageEncoderTimeout.Controls.exact_completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_completion
/-- info: 'Solidity.Backend.FailurePaths.StorageEncoderTimeout.Controls.actual_local_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_local_completes
/-- info: 'Solidity.Backend.FailurePaths.StorageEncoderTimeout.Controls.declared_error' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms declared_error
/-- info: 'Solidity.Backend.FailurePaths.StorageEncoderTimeout.Controls.timeout_not_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms timeout_not_revert
/-- info: 'Solidity.Backend.FailurePaths.StorageEncoderTimeout.Controls.error_signature_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms error_signature_memory
/-- info: 'Solidity.Backend.FailurePaths.StorageEncoderTimeout.Controls.error_signature_storage_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms error_signature_storage_refused
end Solidity.Backend.FailurePaths.StorageEncoderTimeout.Controls
