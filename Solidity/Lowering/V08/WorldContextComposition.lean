import Solidity.Lowering.V08.LibraryFrameTransport
import Solidity.Lowering.V08.TransactionPrefixes

/-! Actual world transactions of the certified library context component.
The real reset input supplies the new typed stores. No raw/reset identification,
new world evaluator, source transaction adequacy or catchability is assumed. -/
namespace Solidity.Lowering.V08.WorldContextComposition
open Solidity ContractWorld LibraryFrameTransport
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

def reset_inputs (w : World contracts) (caller kind : K) (reference : Handle caller)
    (address : Address) (inputs : RuntimeInputs w caller kind reference address) :
    RuntimeInputs w.resetTransient caller kind reference address where
  linked := Storage.resetTransient inputs.linked
  store := Storage.resetTransient inputs.store
  libraryRole := inputs.libraryRole
  callerRole := inputs.callerRole
  linkedAccount := by rw [World.resetTransient_accounts,inputs.linkedAccount]; rfl
  callerAccount := by rw [World.resetTransient_accounts,inputs.callerAccount]; rfl

def frame (caller kind : K) (reference : Handle caller) (address : Address) (ctx : Context)
    (w : World contracts) : TRes (World contracts × Observation) :=
  w.libraryCall reference (library caller kind address) ctx

theorem transaction (w : World contracts) (caller kind : K) (reference : Handle caller)
    (address : Address) (ctx : Context) (inputs : RuntimeInputs w caller kind reference address) :
    w.transact (frame caller kind reference address ctx) =
      (w.resetTransient,.ok (ctx.sender.1.1,ctx.value.1,reference.address.1.1)) := by
  unfold World.transact frame
  rw [library_actual w.resetTransient caller kind reference address ctx
    (reset_inputs w caller kind reference address inputs)]
  simp only [resetTransient_idem]

theorem repeated (w : World contracts) (caller kind : K) (reference : Handle caller)
    (address : Address) (ctx : Context) (inputs : RuntimeInputs w caller kind reference address) :
    ((w.transact (frame caller kind reference address ctx)).2,
      (w.transact (frame caller kind reference address ctx)).1.transact (frame caller kind reference address ctx)) =
      (.ok (ctx.sender.1.1,ctx.value.1,reference.address.1.1),
       (w.resetTransient,.ok (ctx.sender.1.1,ctx.value.1,reference.address.1.1))) := by
  rw [transaction w caller kind reference address ctx inputs]
  rw [transaction w.resetTransient caller kind reference address ctx
    (reset_inputs w caller kind reference address inputs),resetTransient_idem]

/-- Arbitrarily many actual context transactions, retaining every typed status.
The empty history keeps the raw input; a nonempty one normalizes at its real
boundaries. This is the existing transactPrefix fold, not another evaluator. -/
theorem finite_history (w : World contracts) (caller kind : K) (reference : Handle caller)
    (address : Address) (ctx : Context) (inputs : RuntimeInputs w caller kind reference address)
    (count : Nat) :
    transactPrefix w (List.replicate count (frame caller kind reference address ctx)) =
      (if count=0 then w else w.resetTransient,
       List.replicate count (.ok (ctx.sender.1.1,ctx.value.1,reference.address.1.1))) := by
  induction count generalizing w with
  | zero => rfl
  | succ count ih =>
    rw [List.replicate_succ,transact_prefix_cons,transaction w caller kind reference address ctx inputs]
    rw [ih w.resetTransient (reset_inputs w caller kind reference address inputs)]
    cases count with
    | zero => rfl
    | succ n => simp only [Nat.succ_ne_zero,if_false,resetTransient_idem,List.replicate_succ]

theorem later_failure {α : Type} (w : World contracts) (caller kind : K) (reference : Handle caller)
    (address : Address) (ctx : Context) (inputs : RuntimeInputs w caller kind reference address)
    (later : World contracts → Observation → TRes (World contracts × α)) (halt : THalt)
    (failed : later w.resetTransient (ctx.sender.1.1,ctx.value.1,reference.address.1.1) = .error halt) :
    w.transact (fun before => do
      let (next,value) ← frame caller kind reference address ctx before
      later next value) = (w.resetTransient,.error halt) := by
  apply transact_descendant_failure w w.resetTransient
  · exact library_actual w.resetTransient caller kind reference address ctx
      (reset_inputs w caller kind reference address inputs)
  · exact failed

theorem populated_transaction :
    LibraryHandlerControls.outer.transact
      (frame false true (⟨Controls.self⟩ : Handle false) LibraryHandlerControls.link Controls.paidCtx) =
      (LibraryHandlerControls.outer.resetTransient,.ok (1,7,2)) := by
  obtain ⟨runtime⟩ := runtime_of_success (contracts:=LibraryHandlerControls.Catalog)
    LibraryHandlerControls.outer LibraryHandlerControls.handled (⟨Controls.self⟩ : Handle false)
    LibraryHandlerControls.library Controls.paidCtx LibraryHandlerControls.expected
    LibraryHandlerControls.delegated_reached
  exact transaction LibraryHandlerControls.outer false true _ _ Controls.paidCtx runtime

theorem populated_history (count : Nat) :
    transactPrefix LibraryHandlerControls.outer
      (List.replicate count (frame false true (⟨Controls.self⟩ : Handle false)
        LibraryHandlerControls.link Controls.paidCtx)) =
      (if count=0 then LibraryHandlerControls.outer else LibraryHandlerControls.outer.resetTransient,
       List.replicate count (.ok (1,7,2))) := by
  obtain ⟨runtime⟩ := runtime_of_success (contracts:=LibraryHandlerControls.Catalog)
    LibraryHandlerControls.outer LibraryHandlerControls.handled (⟨Controls.self⟩ : Handle false)
    LibraryHandlerControls.library Controls.paidCtx LibraryHandlerControls.expected
    LibraryHandlerControls.delegated_reached
  exact finite_history LibraryHandlerControls.outer false true _ _ Controls.paidCtx runtime count

/-- info: 'Solidity.Lowering.V08.WorldContextComposition.populated_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms populated_history
/-- info: 'Solidity.Lowering.V08.WorldContextComposition.finite_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms finite_history
/-- info: 'Solidity.Lowering.V08.WorldContextComposition.transaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transaction
/-- info: 'Solidity.Lowering.V08.WorldContextComposition.repeated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms repeated
/-- info: 'Solidity.Lowering.V08.WorldContextComposition.later_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms later_failure
/-- info: 'Solidity.Lowering.V08.WorldContextComposition.populated_transaction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms populated_transaction
end Solidity.Lowering.V08.WorldContextComposition
