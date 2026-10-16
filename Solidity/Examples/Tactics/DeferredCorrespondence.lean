import Solidity.Semantics.DeferredCorrespondence
import Solidity.Examples.Tactics.DeferredCallback
import Solidity.Examples.Tactics.DeferredSource

/-! Independent direct callback executions and their actual capture programs. -/

namespace Solidity.Examples.Tactics.DeferredCorrespondence

open Solidity.DeferredSource Solidity.DeferredSource.Callback
open Solidity.Examples.Tactics.DeferredCallback

/-- A direct prefix reads resumed storage and allocates; explicit capture has the same outcome. -/
theorem resumed_allocation_captured :
    ∃ o, DirectCall keep (State.init CallbackContract) "valuesRef" .nil (.user "r")
      getterBody (allocatingPaymentAt []) o ∧
      (∃ u, ExecP keep (State.init CallbackContract)
        (callProgram "valuesRef" .nil (.user "r") getterBody (allocatingPaymentAt [])) u ∧
        o = u.map (Out.drop (.push (.push .refl)))) ∧
      observed o = some 9 ∧ heapLength o = some 1 := by
  have hp : ∃ u, ExecP keep (State.init CallbackContract) (allocatingPaymentAt []).code u ∧
      observed (finishAt (allocatingPaymentAt []) (SRef.ofRoot "values" rfl) u) = some 9 ∧
      heapLength (finishAt (allocatingPaymentAt []) (SRef.ofRoot "values" rfl) u) = some 1 := by
    refine ⟨_, ExecP.cons
      (ExecS.transferResume (J := keep) (st := changed) (nt := []) rfl trivial trivial)
      (ExecP.cons (ExecS.det rfl) ExecP.nil), ?_⟩
    decide +kernel
  obtain ⟨u, hu, hobs, hheap⟩ := hp
  have hc : ExecS keep (State.init CallbackContract)
      (.call "valuesRef" .nil (.storage (.array .uint) (.user "r")) getterBody)
      (.ok ⟨before, List.prefix_refl _⟩) :=
    .callBody (J := keep) (σ := State.init CallbackContract) (f := "valuesRef")
      (args := .nil) (ret := .storage (.array .uint) (.user "r")) (body := getterBody)
      rfl (.cons (.det rfl) .nil)
  have hd : DirectCall keep (State.init CallbackContract) "valuesRef" .nil (.user "r")
      getterBody (allocatingPaymentAt [])
      (finishAt (allocatingPaymentAt []) (SRef.ofRoot "values" rfl) u) := by
    simpa only [map_cat_refl] using DirectCall.next hc
      (show DirectAfterGetter (J := keep) before (allocatingPaymentAt [])
        (finishAt (allocatingPaymentAt []) (SRef.ofRoot "values" rfl) u) from ⟨u, hu, rfl⟩)
  exact ⟨_, hd, (callProgram_direct_iff _ _ _ _ _).mpr hd, hobs, hheap⟩

def trapped : Operand CallbackContract [] .uint :=
  { paymentAt [] with
    value := .val (.binop .div rfl rfl (.simple (.lit 1 rfl)) (.simple (.lit 0 rfl))) }

/-- An unset return reverts before a broken callback invariant or the bad operand source. -/
theorem unset_suppresses_prefix :
    ∃ u, ExecP broken (State.init CallbackContract)
      (callProgram "unset" .nil (.user "r") .nil trapped) u ∧
      (.halt .revert : COut CallbackContract [] []) = u.map (Out.drop (.push (.push .refl))) := by
  have hd : DirectCall broken (State.init CallbackContract) "unset" .nil (.user "r")
      .nil trapped (.halt .revert) := .next (.callBody rfl .nil) rfl
  exact (callProgram_direct_iff _ _ _ _ _).mpr hd

/-- A prefix invariant violation wins over reading `1 / 0` after a valid getter. -/
theorem violation_suppresses_source :
    ∃ u, ExecP broken before (captureProgram trapped) u ∧
      (.violated : COut CallbackContract [] []) = u.map (Out.drop (.push (.push .refl))) := by
  have hd : DirectAfterGetter (J := broken) before trapped .violated :=
    ⟨.violated, ExecP.violated (ExecS.transferViolated (J := broken) rfl (fun h => h)), rfl⟩
  exact (captureProgram_direct_iff trapped before).mpr hd

/-- Recover the direct reading from an independently constructed capture-program execution. -/
theorem captured_resume_is_direct :
    ∃ o, DirectCall keep (State.init CallbackContract) "valuesRef" .nil (.user "r")
      getterBody (paymentAt []) o ∧ observed o = some 9 := by
  obtain ⟨u, hu, hobs⟩ := complete_capture_reads_resumed_storage
  exact ⟨_, (callProgram_direct_iff _ _ _ _ _).mp ⟨u, hu, rfl⟩, hobs⟩

namespace ReferenceCopy

open Solidity.Examples.Tactics.DeferredSource

def keep : StateInv ExampleContract := ⟨fun _ => True⟩

def observedCopy {H : HTy} {Γ : Ctx} :
    COut ExampleContract H Γ → Option (Int × Int × Int × Nat)
  | .ok a => (do
      let calls ← Val.evalT a.st (.read (.root "calls" rfl))
      let len ← Val.evalT a.st (.len (.loc (.root "matrix" rfl)) rfl)
      let first ← Val.evalT a.st
        (.read (.index (.arr .dyn)
          (.loc (.index (.arr .dyn) (.loc (.root "matrix" rfl)) (.simple (.lit 0 rfl))))
          (.simple (.lit 0 rfl))))
      pure (calls.1, len.1, first.1, a.st.H.length)).toOption
  | _ => none

/-- A reference operand copies the allocated memory value; the getter increments only once. -/
theorem allocated_reference_is_direct :
    ∃ o, DirectCall keep (State.init ExampleContract) "matrixRef" .nil (.user "r")
      matrixGetterBody memoryCopy o ∧ observedCopy o = some (1, 1, 47, 1) := by
  let P := callProgram "matrixRef" .nil (.user "r") matrixGetterBody memoryCopy
  refine ⟨_, (callProgram_direct_iff _ _ _ _ _).mp
    ⟨_, execP_noTransfer P (State.init ExampleContract) rfl, rfl⟩, ?_⟩
  decide +kernel

end ReferenceCopy

end Solidity.Examples.Tactics.DeferredCorrespondence
