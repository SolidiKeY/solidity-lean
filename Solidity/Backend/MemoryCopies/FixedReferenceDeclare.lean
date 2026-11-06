import Solidity.Backend.MemoryCopies.FixedReferenceDeclareInterface

/-! Existing copy evaluation, object adoption and local binding transport the
actual original value. Only successful intrinsic TRun execution is related here. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem fixed_reference_declare_source {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (state : State C Γ) (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (reference : SRef C (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (resolved : path.resolveT state = .ok reference) (found : state.storage.find reference = some value) :
    let grown := value.copyStToM state.heap rfl
    TRun.declMem (.fixed (.ref (.array (.prim primitive))) count) (some (.copy path rfl)) rfl state =
      .ok ⟨(state.adopt grown).1.push (t := .mem (.fixed (.ref (.array (.prim primitive))) count)) (some grown.val),grown.ext⟩ := by
  simp only [TRun.declMem,MRhs.evalT,resolved,found,TRes.ofOpt,bind,Except.bind,pure,Except.pure,
    State.copyStToMG,State.grow]

theorem fixed_reference_declare_correct {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (reference : SRef C (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value) (locals : b + (Γ.length + 1) ≤ frame) :
    (∃ fits, FixedReferenceDeclareResult L b frame frag state base cursor machine path value fits) ∨
    (¬ cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value) < W ∧
      run (fixedReferenceDeclareCode b path) machine = .revert) := by
  rcases fixed_reference_path_copy_correct state base cursor machine path reference value represented.core allocator supported resolved found with success | refusal
  · obtain ⟨fits,base',body,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents,growth⟩ := success
    let grown := value.copyStToM state.heap rfl
    let target := writeMachine body (cell (b + Γ.length)) (.val cursor)
    have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
      represented.adopt grown allocated.heap extension shape (fun address lower upper =>
        below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
    left
    refine ⟨fits,base',target,fixed_reference_declare_source state path reference value resolved found,?_,?_,?_,extension,?_,root,?_,?_,keeps,contents⟩
    · rw [fixedReferenceDeclareCode,run_append_ok ran]
      rfl
    · simpa only [grown,root,target] using adopted.consMem grown.val locals
    · exact allocated.localWrite (b + Γ.length) (by omega) (by omega) (.val cursor)
    · change body.stack = machine.stack
      rw [shape]
    · exact upd_same _ _ _
    · intro address lower upper different
      change upd body.mem (cell (b + Γ.length)) (.val cursor) address = machine.mem address
      rw [upd_other _ _ different]
      exact below address lower upper
  · right
    exact ⟨refusal.1,run_append_revert refusal.2⟩

def fixedReferenceDeclare : FixedReferenceDeclareCertificate := ⟨fixed_reference_declare_correct⟩

/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_declare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_declare_source
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_declare_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_declare_correct
/--
info: 'Solidity.Backend.MemoryCopies.fixedReferenceDeclare' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixedReferenceDeclare
end Solidity.Backend.MemoryCopies
