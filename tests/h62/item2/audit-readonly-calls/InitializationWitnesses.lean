import Solidity.Lowering.Readonly.PrimitiveInitialization

/-! Guard horizon exhaustion and empty returns being erased by an always-timeout initializer.
The SAME inhabited Env, Bool locals and Source state instantiate all four frozen
primitive initialization interfaces. Positive horizons succeed; zero horizon
retains the distinct nonempty-timeout/empty-success boundary. Horizons are not
EVM gas/fork resources. This supplies original inputs, not compiler adequacy. -/
namespace Solidity.H62.ReadonlyAudit.InitializationWitnesses
open Solidity Solidity.Source Solidity.Lowering.Readonly

def environment : Env := ⟨[]⟩
def context : RCtx := [.bool]
def input : Locals environment.layout context := .cons (.bool true) .nil
def seed : St environment :=
  { ex := {world := ⟨fun _ => Account.empty _⟩,transient := ⟨fun _ => Storage.empty⟩,journal := []}
    heap := Solidity.Source.Heap.empty,events := [],logs := [],fnLocals := ⟨[],.nil⟩ }
def kinds : List PrimTy := [.bool,.uint,.int]

theorem zero_value_joint :
    (zeroVal (E := environment) (Γ := context) 1 (PrimitiveValues.sourceTy .uint)) =
      pure (PrimitiveValues.toSource environment.layout .uint (PrimTy.dflt .uint)) :=
  PrimitiveInitialization.zero_value 0 .uint

theorem zero_values_joint :
    (zeroVals (E := environment) (Γ := context) 1 (kinds.map PrimitiveValues.sourceTy)) =
      pure (PrimitiveInitialization.defaults environment.layout kinds) :=
  PrimitiveInitialization.zero_values 0 kinds

theorem exhausted_nonempty_joint :
    (zeroVals (E := environment) (Γ := context) 0 (kinds.map PrimitiveValues.sourceTy)) =
      EM.halt .timeout :=
  PrimitiveInitialization.exhausted_nonempty .bool [.uint,.int]

theorem exhausted_empty_joint :
    (zeroVals (E := environment) (Γ := context) 0 []) =
      pure (Vals.nil : Vals environment.layout []) :=
  PrimitiveInitialization.exhausted_empty

/-- An actual local/state argument distinguishes success from timeout. -/
theorem pure_ne_timeout {α : Type} (value : α) :
    (pure value : EM environment context α) ≠ EM.halt .timeout := by
  intro same
  have observed := congrArg (fun m : EM environment context α => m.run (input,seed)) same
  cases observed

theorem initialized_observed :
    (zeroVals (E := environment) (Γ := context) 1 (kinds.map PrimitiveValues.sourceTy)).run (input,seed) =
      (.ok (PrimitiveInitialization.defaults environment.layout kinds),(input,seed)) :=
  congrArg (fun m => m.run (input,seed)) zero_values_joint

theorem exhausted_observed :
    (zeroVals (E := environment) (Γ := context) 0 (kinds.map PrimitiveValues.sourceTy)).run (input,seed) =
      (.error .timeout,(input,seed)) :=
  congrArg (fun m => m.run (input,seed)) exhausted_nonempty_joint

theorem empty_observed :
    (zeroVals (E := environment) (Γ := context) 0 []).run (input,seed) =
      (.ok (Vals.nil : Vals environment.layout []),(input,seed)) :=
  congrArg (fun m => m.run (input,seed)) exhausted_empty_joint

theorem always_timeout_refused :
    (zeroVals (E := environment) (Γ := context) 1 (kinds.map PrimitiveValues.sourceTy)) ≠ EM.halt .timeout := by
  rw [zero_values_joint]
  exact pure_ne_timeout _

theorem empty_timeout_refused :
    (zeroVals (E := environment) (Γ := context) 0 []) ≠ EM.halt .timeout := by
  rw [exhausted_empty_joint]
  exact pure_ne_timeout _

end Solidity.H62.ReadonlyAudit.InitializationWitnesses
