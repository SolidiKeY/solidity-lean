import Solidity.Backend.MemoryCopies.CanonicalRebindInterface

/-! Reuse the canonical load and populated allocator; only the existing local
store changes the destination. Old identities and their contents survive. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem canonical_rebind_source {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (value : primitive.Denote)
    (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (singletonArrayValue primitive value)) :
    let grown := (singletonArrayValue primitive value).copyStToM state.heap rfl
    TRun.rebindMem destination (.copy path rfl) state =
      .ok ⟨(state.adopt grown).1.setLocal destination (some grown.val),grown.ext⟩ := by
  rw [TRun.rebindMem,storage_singleton_rhs state path reference value resolved found]
  rfl

theorem canonical_rebind_correct {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    {L b frame : Nat} {frag : Frag Γ} (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (value : primitive.Denote)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (singletonArrayValue primitive value))
    (fits : cursor.val + 2 < W) :
    CanonicalRebindResult L b frame frag state base cursor machine destination path value fits := by
  obtain ⟨word,base',body,_,ran,allocated,root,extension,shape,below,_⟩ :=
    loaded_singleton_success (canonicalSingletonExpression path) value state base cursor machine represented allocator
      (canonical_singleton_supported frag path supported)
      (canonical_singleton_evaluation state path reference value resolved found) fits
  let grown := (singletonArrayValue primitive value).copyStToM state.heap rfl
  let target := writeMachine body (cellOf b destination) (.val cursor)
  have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
    represented.adopt grown allocated.heap extension shape (fun address lower upper =>
      below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
  refine ⟨base',target,canonical_rebind_source state destination path reference value resolved found,?_,?_,?_,extension,?_,root,?_,?_,
    SVal.keeps_copyStToM _ rfl state.heap,?_⟩
  · rw [canonicalRebindCode,run_append_ok ran]
    rfl
  · simpa only [grown,root,target] using adopted.setMem destination grown.val
  · exact allocated.localWrite (lvl b destination) (Nat.lt_of_lt_of_le positive (le_lvl b destination))
      (Nat.lt_of_lt_of_le (lvl_lt b destination) represented.locals) (.val cursor)
  · change body.stack = machine.stack
    rw [shape]
  · exact upd_same _ _ _
  · intro address lower upper different
    change upd body.mem (cellOf b destination) (.val cursor) address = machine.mem address
    rw [upd_other _ _ different]
    exact below address lower upper
  · intro R old
    exact Nat.lt_of_lt_of_le old.id_lt (SVal.copyStToM_id_ge state.heap (singletonArrayValue primitive value) rfl)

theorem canonical_rebind_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    {L b : Nat} {frag : Frag Γ} (state : State C Γ) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.prim primitive))))
    (path : SPath C Γ (.ref (.array (.prim primitive))))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    TRun.rebindMem destination (.copy path rfl) state = .error .revert ∧
    run (canonicalRebindCode b destination path) machine = .revert := by
  constructor
  · simp only [TRun.rebindMem,MRhs.evalT,refused,bind,Except.bind]
  · exact run_append_revert (loaded_singleton_refusal (canonicalSingletonExpression path) state machine represented
      (canonical_singleton_supported frag path supported) (canonical_singleton_failed_evaluation state path refused))

def canonicalRebind : CanonicalRebindCertificate := ⟨canonical_rebind_correct,canonical_rebind_refusal⟩

#print axioms canonical_rebind_source
#print axioms canonical_rebind_correct
#print axioms canonical_rebind_refusal
#print axioms canonicalRebind
end Solidity.Backend.MemoryCopies
