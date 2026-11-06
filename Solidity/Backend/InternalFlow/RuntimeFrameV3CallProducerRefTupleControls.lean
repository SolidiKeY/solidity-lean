import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefTupleCall
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefArrayControls

/-! A real mixed tuple call with a memory argument and a memory return.
The default result array allocates, is rebound to the old argument, and a
bounds-checked read gates the distinctive primitive result7. Both outcomes are inhabited. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple.Controls
open Evm Evm.Memory

abbrev C := ArrayControls.C
abbrev A := ArrayControls.A
abbrev Γ := ArrayControls.Γ
abbrev F := ArrayControls.F
abbrev rs : Ctx := [.val .uint, .mem A]
def binders : RetBinders rs :=
  .snoc (.snocMem .nil A (.user "array") rfl rfl) .uint (.user "number")
def body : Prog C (rs ++ [.mem A, .val .uint]) (rs ++ [.mem A, .val .uint]) :=
  .cons (.rebindMem (.there .here) (.alias (.var (.there (.there .here)) rfl)))
    (.cons (.assignLocal .here (.readMem (.index .dyn (.var (.there .here) rfl)
      (.simple (.local (.there (.there (.there .here))))))))
      (.cons (.assignLocal .here (.simple (.lit 7 rfl))) .nil))
def call : Stmt C Γ (rs ++ Γ) := .call "tupleAlias" ArrayControls.args (.rets binders) body

def expanded : Composition.Program 1 F (expand ArrayControls.args binders body) :=
  (Composition.compileProgram 1 F (expand ArrayControls.args binders body)).get (by decide +kernel)
def statement : Composition.Statement 1 F call :=
  emit "tupleAlias" ArrayControls.args binders body expanded
def selected : Composition.Program 1 F (.cons call .nil) :=
  Composition.cons statement (Composition.nil 1 statement.checked.frag)

theorem source_success : ∃ out : Solidity.Out C (ArrayControls.caller (wmod 0)).H (rs ++ Γ),
    call.run (ArrayControls.caller (wmod 0)) = .ok out := by
  with_unfolding_all exact ⟨_,rfl⟩

theorem source_revert : call.run (ArrayControls.caller (wmod 2)) = .error .revert := by
  with_unfolding_all rfl

theorem cost (n : Fin W) : selected.checked.cost (ArrayControls.caller n) = 1 := by
  with_unfolding_all rfl

def scope : Ext Γ (rs ++ Γ) := Ext.append Γ rs
theorem form : Form Γ (.rets binders) scope := .tuple binders
theorem flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope := by
  intro R index live
  nomatch index

theorem capacity (n : Fin W) :
    AllocationInput 1 64 (selected.checked.cost (ArrayControls.caller n))
      (ArrayControls.caller n) ArrayControls.bases (ArrayControls.machine n) :=
  .inr ⟨by decide, wmod 130, (ArrayControls.initial n).2, by rw [cost]; decide⟩

theorem member (n : Fin W) : admitted selected 16 16 1 64
    (ArrayControls.caller n) ArrayControls.bases (ArrayControls.machine n) 20 :=
  ⟨(ArrayControls.initial n).1, by decide +kernel, by decide, by decide,
    by decide, by decide, by decide, by decide, rfl, capacity n⟩

theorem entered (n : Fin W) : InterfaceV1.Entry (plan selected 16 16) 1 1 64 F
    (ArrayControls.caller n) ArrayControls.bases (ArrayControls.machine n) 20 :=
  coverage selected 16 16 1 64 (ArrayControls.caller n) ArrayControls.bases
    (ArrayControls.machine n) 20 (member n)

theorem successful : InterfaceV3.SuccessfulEntry 1 F (admitted selected 16 16)
    call (plan selected 16 16) := by
  obtain ⟨out, source⟩ := source_success
  exact ⟨1,64,ArrayControls.caller (wmod 0),ArrayControls.bases,
    ArrayControls.machine (wmod 0),20,out,member _,entered _,source⟩

theorem reverting : InterfaceV3.RevertingEntry 1 F (admitted selected 16 16)
    call (plan selected 16 16) :=
  ⟨1,64,ArrayControls.caller (wmod 2),ArrayControls.bases,
    ArrayControls.machine (wmod 2),20,member _,entered _,source_revert⟩

/-- Profile provenance stays external; real success/revert and universal
physical-input coverage are supplied by this producer. -/
def producer (approved : InterfaceV3.Admission C Γ)
    (hprof : InterfaceV3.AdmissionAgreement approved (admitted selected 16 16)) :
    InterfaceV3.PendingCallProducer 1 F approved (admitted selected 16 16)
      "tupleAlias" ArrayControls.args (.rets binders) body :=
  make form selected 16 16 approved hprof flags successful reverting

theorem simulated_success : ∃ out : Solidity.Out C (ArrayControls.caller (wmod 0)).H (rs ++ Γ),
    call.run (ArrayControls.caller (wmod 0)) = .ok out ∧
    InterfaceV1.Returned (plan selected 16 16) 1 1 64 (ArrayControls.caller (wmod 0))
      ArrayControls.bases (ArrayControls.machine (wmod 0)) 20 out := by
  obtain ⟨out, source⟩ := source_success
  exact ⟨out,source,returns form selected 16 16 flags 1 64 (ArrayControls.caller (wmod 0))
    ArrayControls.bases (ArrayControls.machine (wmod 0)) 20 (entered _) out source⟩

theorem simulated_revert :
    Evm.run (plan selected 16 16).code (ArrayControls.machine (wmod 2)) = .revert :=
  bare_revert selected 16 16 1 64 (ArrayControls.caller (wmod 2)) ArrayControls.bases
    (ArrayControls.machine (wmod 2)) 20 (entered _) source_revert

/-- Capacity refusal concerns the real cost premise, not a runtime panic. -/
theorem capacity_refused : ¬ AllocationInput 1 64
    (selected.checked.cost (ArrayControls.caller (wmod 0))) (ArrayControls.caller (wmod 0))
    ArrayControls.bases (writeMachine (ArrayControls.machine (wmod 0)) 0 (.val (wmod (W-1)))) := by
  rw [cost]
  intro capacity
  rcases capacity with zero | ⟨positive, cursor, allocator, space⟩
  · cases zero
  · have same := allocator.arrays.free.cell
    change Evm.Word.val (wmod (W-1)) = Evm.Word.val cursor at same
    have cursorEq := Evm.Word.val.inj same
    have top : (wmod (W-1)).val = W-1 := Nat.mod_eq_of_lt (by have := W_pos; omega)
    rw [← cursorEq, top] at space
    have positive := W_pos
    omega

theorem literal_revert_refused :
    (Composition.compileProgram 1 F (expand ArrayControls.args binders
      (.cons .revert .nil : Prog C (rs ++ [.mem A,.val .uint])
        (rs ++ [.mem A,.val .uint])))).isSome = false := by decide +kernel

#print axioms source_success
#print axioms source_revert
#print axioms producer
#print axioms simulated_success
#print axioms simulated_revert
#print axioms capacity_refused
def sourceObservation (n : Fin W) : Option (List Nat) :=
  match call.run (ArrayControls.caller n) with
  | .ok out => do
    let returned ← out.st.env.2.1
    let original ← out.st.env.2.2.2.1
    pure [out.st.env.1.val.toNat,returned.id,original.id,out.st.H.length,out.st.heap.len returned .dyn]
  | _ => none

def targetObservation : Evm.Out → Option (List Nat)
  | .ok target _ => (target.stack ++ [target.mem 0,target.mem 1,target.mem 2,target.mem 3,
      target.mem 4,target.mem 16,target.mem 63,target.mem 128,target.mem 129,target.mem 130]).mapM
      (fun word => match word with | .val value => some value.val | _ => none)
  | _ => none

def missingExport : List Instr :=
  Restore.saveCells 16 (Restore.contextCells 1 Γ) ++ expanded.checked.code ++
    Restore.restoreCells 16 (Restore.contextCells 1 Γ)

theorem source_observation : sourceObservation (wmod 0) = some [7,0,0,2,1] := by
  decide +kernel

theorem target_observation : targetObservation
    (Evm.run (plan selected 16 16).code (ArrayControls.machine (wmod 0))) =
      some [77,131,128,0,128,7,20,99,1,0,0] := by decide +kernel

/-- Omitting the real compaction preserves parameter words in the result
slots: pointer export and the nonzero primitive result are both lost. -/
theorem missing_export_refused : targetObservation
    (Evm.run missingExport (ArrayControls.machine (wmod 0))) ≠
      some [77,131,128,0,128,7,20,99,1,0,0] := by decide +kernel

#print axioms source_observation
#print axioms target_observation
#print axioms missing_export_refused
end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple.Controls
