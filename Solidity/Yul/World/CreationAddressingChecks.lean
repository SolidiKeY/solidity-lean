import Solidity.Yul.World.CreationAddressing
import Solidity.Yul.World.CreationFramesChecks

/-! Scripted producer probes the actual selected frame/address/code. Its trace
is an interface witness, not a reachable constructor/log/credit certificate. -/
namespace Solidity.Yul.World.CreationAddressingChecks
open Solidity.Source
open Solidity.Source.StateExamples
open Solidity.Roadmap (Fixed Word Bytes Outcome)
open Solidity.Yul.World.Checks
open Solidity.Yul.World.AdapterChecks (observed memory)
open Solidity.Yul.World.CreationFramesChecks (prepared parent actual_preparation)

def target (F : Fixed) (salt : Option Word) :=
  selectCreationAddress F (addr 1) ⟨3,by decide⟩ salt [17,34,51]

def probeTrace (F : Fixed) (salt : Option Word) : List Observation :=
  [.event (.credit (target F salt) (toWord 5)),
   .log ⟨target F salt,⟨0,by decide⟩,#v[],[17,34,51]⟩] ++ calleeTrace

def producer (failed : Bool) : InitcodePort D₀ LW LW := fun _ _ context code =>
  some ⟨havoc,[.event (.credit context.this context.value),
    .log ⟨context.this,⟨0,by decide⟩,#v[],code⟩] ++ calleeTrace,
    if failed then .revert [253,254] else .success [96,0]⟩

def result (F : Fixed) (salt : Option Word) (failed : Bool) : CompletedCreation D₀ LW LW :=
  ⟨if failed then .revert [253,254] else .success [96,0],
   finishCreation prepared (constructorFrame prepared.effects.execution parent (target F salt) (toWord 5))
     ⟨havoc,probeTrace F salt,if failed then .revert [253,254] else .success [96,0]⟩,rfl⟩

theorem actual_addressed (F : Fixed) (salt : Option Word) (failed : Bool) :
    addressedCreation F salt TargetMemory.port (producer failed) observed memory parent
      (toWord 100000) (toWord 5) (toWord 7) (toWord 3) = some (result F salt failed) :=
  addressedCreation_exact _ _ _ _ _ _ _ _ _ _ _ [17,34,51] prepared
    ⟨havoc,probeTrace F salt,if failed then .revert [253,254] else .success [96,0]⟩ rfl (by decide)
    Solidity.Yul.World.AdapterChecks.input_loaded actual_preparation rfl

/-- CREATE really uses old nonce3, while the prepared account has nonce4.
No address injectivity or no-collision claim is used. -/
theorem old_nonce_control (F : Fixed) :
    target F none = createAddress F (addr 1) ⟨3,by decide⟩ ∧
    (prepared.effects.execution.world.accounts (addr 1)).nonce = 4 := ⟨rfl,rfl⟩

theorem loaded_create2_control (F : Fixed) (salt : Word) :
    target F (some salt) = create2Address F (addr 1) salt [17,34,51] ∧
    (result F (some salt) false).observed.trace = callerTrace ++ probeTrace F (some salt) ∧
    (result F (some salt) false).observed.effects.returndata = [] := ⟨rfl,rfl,rfl⟩

theorem failed_selected_control (F : Fixed) (salt : Option Word) :
    (result F salt true).observed.effects.execution = prepared.effects.execution ∧
    (result F salt true).observed.trace = rollbackTrace callerTrace (probeTrace F salt) ∧
    (result F salt true).initialization = .revert [253,254] ∧
    (result F salt true).observed.effects.returndata = [253,254] := by
  exact ⟨(finishCreation_revert _ _ _ _ _).1,rfl,rfl,rfl⟩

theorem static_control (F : Fixed) (salt : Option Word) :
    addressedCreation F salt TargetMemory.port (producer false) observed memory {parent with static := true}
      (toWord 100000) (toWord 5) (toWord 7) (toWord 3) = none :=
  addressedCreation_static _ _ _ _ _ _ _ _ _ _ _ rfl

theorem cap_control (F : Fixed) (salt : Option Word) :
    addressedCreation F salt TargetMemory.port (producer false) CreationFramesChecks.capped memory parent
      (toWord 100000) (toWord 5) (toWord 7) (toWord 3) = none :=
  addressedCreation_cap _ _ _ _ _ _ _ _ _ _ _ (by decide)

theorem memory_refusal (F : Fixed) (salt : Option Word) :
    addressedCreation F salt TargetMemory.port (producer false) observed memory parent
      (toWord 100000) (toWord 5) ⟨2^256-1,by decide⟩ (toWord 2) = none := rfl

theorem rule_use (F : Fixed) (salt : Option Word) (failed : Bool) : AdapterRules.Box
    (AddressedRules.Step F salt TargetMemory.port (producer failed) parent
      (toWord 100000) (toWord 5) (toWord 7) (toWord 3) (result F salt failed).initialization)
    (fun after => after.observed = (result F salt failed).observed ∧ after.memory = memory ∧
      after.observed.effects.returndata = createReturnData (result F salt failed).initialization)
    ⟨observed,memory⟩ := AddressedRules.addressed_rule _ _ _ _ _ _ _ _ _ _ _ (actual_addressed F salt failed)

theorem wrong_outcome (F : Fixed) (salt : Option Word) :
    ¬ AddressedRules.Step F salt TargetMemory.port (producer false) parent
      (toWord 100000) (toWord 5) (toWord 7) (toWord 3) (.revert [96,0])
      ⟨observed,memory⟩ ⟨(result F salt false).observed,memory⟩ := by
  intro hs
  obtain ⟨r,hr,ho,_⟩ := hs
  rw [actual_addressed] at hr
  cases Option.some.inj hr
  cases ho

end Solidity.Yul.World.CreationAddressingChecks
