import Solidity.Backend.MemoryCopies.NestedStoragePathInterface

/-! Actual selected dynamic outer values feed the existing checked copier.
Intrinsic local transport reuses typed adoption and local-write preservation. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

private theorem primitive_words {primitive : PrimTy} {n : Nat} (elements : SVec (.prim primitive) n) :
    elementWordCount elements = 0 := by
  cases elements with
  | nil => rfl
  | cons value rest =>
    cases value with
    | prim value => simp only [elementWordCount,liveWordCount,primitive_words rest,Nat.zero_add]

private theorem child_words {primitive : PrimTy} (value : SVal (.ref (.array (.prim primitive)))) :
    liveWordCount value = (fixedReferenceLiveRow value).val.length + 1 := by
  cases value with
  | array elements shadow bounded =>
    simp only [liveWordCount,primitive_words,Nat.zero_add,fixedReferenceLiveRow,primitiveArrayLiveValues,
      SVal.view_array,List.length_map,SVec.length_toList,Nat.add_comm]

private theorem element_words {primitive : PrimTy} {n : Nat} (elements : SVec (.ref (.array (.prim primitive))) n) :
    elementWordCount elements = nestedStorageDemand (elements.toList.map fixedReferenceLiveRow) := by
  cases elements with
  | nil => simp only [elementWordCount,SVec.toList_nil,List.map_nil,nestedStorageDemand]
  | cons value rest =>
    simp only [elementWordCount,child_words,element_words rest,SVec.toList_cons,List.map_cons,nestedStorageDemand]

theorem nested_storage_path_demand {primitive : PrimTy} (value : SVal (.ref (.array (.ref (.array (.prim primitive)))))) :
    liveWordCount value = nestedStorageParentDemand (nestedStorageLiveRows value) := by
  cases value with
  | array elements shadow bounded =>
    simp only [liveWordCount,element_words,nestedStorageParentDemand,nestedStorageLiveRows,SVal.view_array,
      List.length_map,SVec.length_toList]
    omega

theorem nested_storage_path_copy {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive))))))
    (reference : SRef C (.ref (.array (.ref (.array (.prim primitive))))))
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (represented : Sim C L b frag state machine) (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value) :
    (∃ fits, NestedStoragePathResult b frame state base cursor machine path value fits) ∨
    (¬ cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W ∧ run (nestedStoragePathCode b path) machine = .revert) := by
  rcases spath_sim path represented supported with
    ⟨actual,source,selected,resolution,live,_,sourceRepr,pathRun⟩ | ⟨refused,_⟩
  · rw [resolved] at resolution
    cases resolution
    have observed : state.storage.find reference = some selected := Sto.find_of_findLive live
    rw [found] at observed
    cases observed
    rcases nested_storage_live_correct state.heap value base frame cursor machine source L allocator sourceRepr with success | refusal
    · obtain ⟨fits,base',target,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents⟩ := success
      left
      refine ⟨fits,base',target,?_,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents,?_⟩
      · rw [nestedStoragePathCode,run_append_ok pathRun]
        exact ran
      · rw [valueCopy_words,nested_storage_path_demand]
    · right
      refine ⟨refusal.1,?_⟩
      rw [nestedStoragePathCode,run_append_ok pathRun]
      exact refusal.2
  · rw [resolved] at refused
    cases refused

theorem nested_storage_path_declare_source {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive))))))
    (reference : SRef C (.ref (.array (.ref (.array (.prim primitive))))))
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (resolved : path.resolveT state = .ok reference) (found : state.storage.find reference = some value) :
    let grown := value.copyStToM state.heap rfl
    TRun.declMem (.array (.ref (.array (.prim primitive)))) (some (.copy path rfl)) rfl state =
      .ok ⟨(state.adopt grown).1.push (t := .mem (.array (.ref (.array (.prim primitive))))) (some grown.val),grown.ext⟩ := by
  simp only [TRun.declMem,MRhs.evalT,resolved,found,TRes.ofOpt,bind,Except.bind,pure,Except.pure,
    State.copyStToMG,State.grow]

theorem nested_storage_path_declare {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive))))))
    (reference : SRef C (.ref (.array (.ref (.array (.prim primitive))))))
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value) (locals : b + (Γ.length + 1) ≤ frame) :
    (∃ fits, NestedStoragePathDeclareResult L b frame frag state base cursor machine path value fits) ∨
    (¬ cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W ∧
      run (nestedStoragePathDeclareCode b path) machine = .revert) := by
  rcases nested_storage_path_copy state base cursor machine path reference value represented.core allocator supported resolved found with success | refusal
  · obtain ⟨fits,base',body,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents,growth⟩ := success
    let grown := value.copyStToM state.heap rfl
    let target := writeMachine body (cell (b + Γ.length)) (.val cursor)
    have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
      represented.adopt grown allocated.heap extension shape (fun address lower upper =>
        below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
    left
    refine ⟨fits,base',target,nested_storage_path_declare_source state path reference value resolved found,?_,?_,?_,extension,?_,root,?_,?_,keeps,contents⟩
    · rw [nestedStoragePathDeclareCode,run_append_ok ran]
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

theorem nested_storage_path_rebind_source {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (destination : Idx Γ (.mem (.array (.ref (.array (.prim primitive))))))
    (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive))))))
    (reference : SRef C (.ref (.array (.ref (.array (.prim primitive))))))
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (resolved : path.resolveT state = .ok reference) (found : state.storage.find reference = some value) :
    let grown := value.copyStToM state.heap rfl
    TRun.rebindMem destination (.copy path rfl) state =
      .ok ⟨(state.adopt grown).1.setLocal destination (some grown.val),grown.ext⟩ := by
  simp only [TRun.rebindMem,MRhs.evalT,resolved,found,TRes.ofOpt,bind,Except.bind,pure,Except.pure,
    State.copyStToMG,State.grow]

theorem nested_storage_path_rebind {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (destination : Idx Γ (.mem (.array (.ref (.array (.prim primitive))))))
    (path : SPath C Γ (.ref (.array (.ref (.array (.prim primitive))))))
    (reference : SRef C (.ref (.array (.ref (.array (.prim primitive))))))
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value) :
    (∃ fits, NestedStoragePathRebindResult L b frame frag state base cursor machine destination path value fits) ∨
    (¬ cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W ∧
      run (nestedStoragePathRebindCode b destination path) machine = .revert) := by
  rcases nested_storage_path_copy state base cursor machine path reference value represented.core allocator supported resolved found with success | refusal
  · obtain ⟨fits,base',body,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents,growth⟩ := success
    let grown := value.copyStToM state.heap rfl
    let target := writeMachine body (cellOf b destination) (.val cursor)
    have adopted : Objects.StateRepr L b frame frag (state.adopt grown).1 base' body :=
      represented.adopt grown allocated.heap extension shape (fun address lower upper =>
        below address (by omega) (Nat.lt_of_lt_of_le upper (Nat.le_trans represented.locals allocator.free.above)))
    left
    refine ⟨fits,base',target,nested_storage_path_rebind_source state destination path reference value resolved found,?_,?_,?_,extension,?_,root,?_,?_,keeps,?_,contents⟩
    · rw [nestedStoragePathRebindCode,run_append_ok ran]
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

def nestedStoragePath : NestedStoragePathCertificate :=
  ⟨nested_storage_path_copy,nested_storage_path_declare,nested_storage_path_rebind⟩

/--
info: 'Solidity.Backend.MemoryCopies.nested_storage_path_demand' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms nested_storage_path_demand
/--
info: 'Solidity.Backend.MemoryCopies.nested_storage_path_copy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nested_storage_path_copy
/--
info: 'Solidity.Backend.MemoryCopies.nested_storage_path_declare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nested_storage_path_declare_source
/--
info: 'Solidity.Backend.MemoryCopies.nested_storage_path_declare' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nested_storage_path_declare
/--
info: 'Solidity.Backend.MemoryCopies.nested_storage_path_rebind_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nested_storage_path_rebind_source
/--
info: 'Solidity.Backend.MemoryCopies.nested_storage_path_rebind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nested_storage_path_rebind
/--
info: 'Solidity.Backend.MemoryCopies.nestedStoragePath' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nestedStoragePath
end Solidity.Backend.MemoryCopies
