import Solidity.Backend.MemoryCopies.FixedReferenceRebindInterface

/-! Existing copy evaluation, object adoption and local rebinding transport the
actual original value. Only successful intrinsic TRun execution is related here. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem fixed_reference_rebind_source {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (state : State C Γ) (destination : Idx Γ (.mem (.fixed (.ref (.array (.prim primitive))) count)))
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (reference : SRef C (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (resolved : path.resolveT state = .ok reference) (found : state.storage.find reference = some value) :
    let grown := value.copyStToM state.heap rfl
    TRun.rebindMem destination (.copy path rfl) state =
      .ok ⟨(state.adopt grown).1.setLocal destination (some grown.val),grown.ext⟩ := by
  simp only [TRun.rebindMem,MRhs.evalT,resolved,found,TRes.ofOpt,bind,Except.bind,pure,Except.pure,
    State.copyStToMG,State.grow]

theorem fixed_reference_rebind_correct {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.fixed (.ref (.array (.prim primitive))) count)))
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (reference : SRef C (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value) :
    (∃ fits, FixedReferenceRebindResult L b frame frag state base cursor machine destination path value fits) ∨
    (¬ cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value) < W ∧
      run (fixedReferenceRebindCode b destination path) machine = .revert) := by
  rcases fixed_reference_path_copy_correct state base cursor machine path reference value represented.core allocator supported resolved found with success | refusal
  · obtain ⟨fits,base',body,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents,growth⟩ := success
    let grown := value.copyStToM state.heap rfl
    let target := writeMachine body (cellOf b destination) (.val cursor)
    have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
      represented.adopt grown allocated.heap extension shape (fun address lower upper =>
        below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
    left
    refine ⟨fits,base',target,fixed_reference_rebind_source state destination path reference value resolved found,?_,?_,?_,extension,?_,root,?_,?_,keeps,?_,contents⟩
    · rw [fixedReferenceRebindCode,run_append_ok ran]
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
      exact Nat.lt_of_lt_of_le old.id_lt (SVal.copyStToM_id_ge state.heap value rfl)
  · right
    exact ⟨refusal.1,run_append_revert refusal.2⟩

def fixedReferenceRebind : FixedReferenceRebindCertificate := ⟨fixed_reference_rebind_correct⟩

/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_rebind_source' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_rebind_source
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_rebind_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_rebind_correct
/--
info: 'Solidity.Backend.MemoryCopies.fixedReferenceRebind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixedReferenceRebind
end Solidity.Backend.MemoryCopies
