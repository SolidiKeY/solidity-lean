import Solidity.Backend.MemoryCopies.CheckedStoragePath
import Solidity.Evm.Correct

/-! Actual runtime path copies bind fresh arrays while preserving old aliases.
The existing path compiler refuses invalid outer indices before allocation. -/
namespace Solidity.Backend.MemoryCopies.CheckedStoragePathControls
open Evm Evm.Memory Semantics
private abbrev leaf : RefTy := .array (.prim .uint)
private def C : Contract := {vars := [("matrix",.ref (.array (.ref leaf)))]}
private def root : C.rootType "matrix" = some (.ref (.array (.ref leaf))) := by decide +kernel
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private def wide : 128 < W := by decide
private def array (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref leaf) :=
  primitiveArrayValue .uint (values payloads) (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide)
private def matrix (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref (.array (.ref leaf))) :=
  .array (.cons (array payloads bounded) .nil) .nil (by decide)
private abbrev H : HTy := [leaf]
private abbrev Γ : Ctx := [.mem leaf,.mem leaf]
private def old : HRef H leaf := ⟨0,rfl⟩
private def heap : Heap H := (⟨[indexValue (wmod 7)],by decide⟩,())
private def state (payloads : List (Fin W)) (bounded : payloads.length < 128) : State C Γ :=
  {storage := .cons (matrix payloads bounded) .nil,H := H,heap := heap,env := (some old,(some old,()))}
private def store (payloads : List (Fin W)) : WordStore := ⟨fun slot => match slot with
  | .root 0 => wmod 1
  | .data (.root 0) 0 => wmod payloads.length
  | .data (.data (.root 0) 0) index => payloads[index]?.getD (wmod 0)
  | _ => wmod 0⟩
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with
    store := store payloads
    stack := [w[77]]
    mem := fun address => if address = 0 then w[40] else if address = 1 ∨ address = 2 then w[16]
      else if address = 7 then w[99] else if address = 16 then w[1] else if address = 17 then w[7] else w[0]}
private def bases : Nat → Fin W := fun _ => wmod 16
private def path (index : Nat) : SPath C Γ (.ref leaf) :=
  .loc (.index (.arr .dyn) (.loc (.root "matrix" root))
    (.simple (.lit (indexValue (wmod index)).val (indexValue (wmod index)).property)))
private def reference : SRef C (.ref leaf) := (SRef.ofRoot "matrix" root).index (.arr .dyn) (indexValue (wmod 0))
private def destination : Idx Γ (.mem leaf) := .here
private theorem refs {R : RefTy} (reference : HRef H R) : R = leaf ∧ HEq reference old := by
  rcases reference with ⟨index,selected⟩
  cases index with
  | zero => cases selected; exact ⟨rfl,HEq.rfl⟩
  | succ index => cases selected

private theorem leaf_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ReprAt (store payloads) 128 (.ref leaf) (.data (.root 0) 0) (array payloads bounded) := by
  refine .array ?_ (by simpa only [values,List.length_map] using bounded) ?_
  · simp only [values,List.length_map]
    exact Nat.mod_eq_of_lt (Nat.lt_trans bounded wide)
  · intro index item selected
    simp only [SVec.toList_ofList,values,List.getElem?_map] at selected
    cases chosen : payloads[index]? with
    | none => simp only [chosen,Option.map_none] at selected; cases selected
    | some payload =>
      simp only [chosen,Option.map_some] at selected
      cases selected
      simp only [size_prim,Nat.mul_one]
      refine .prim (ReprV.uint_of ?_)
      simp only [store,chosen,Option.getD_some]
      rfl

private theorem storage_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ReprStore C 128 (store payloads) (state payloads bounded).storage := by
  intro name type found
  change (if name = "matrix" then some (.ref (.array (.ref leaf))) else none) = some type at found
  split at found
  · rename_i same
    subst name
    cases found
    change ReprAt (store payloads) 128 (.ref (.array (.ref leaf))) (.root 0) (matrix payloads bounded)
    refine .array rfl (by decide) ?_
    intro index item selected
    simp only [SVec.toList_cons,SVec.toList_nil] at selected
    cases index with
    | zero => cases selected; exact leaf_repr payloads bounded
    | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at selected; cases selected
  · cases found

private theorem core (payloads : List (Fin W)) (bounded : payloads.length < 128) : Sim C 128 1 (Frag.init Γ) (state payloads bounded) (machine payloads) := by
  have initial : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0,W_pos⟩) (Machine.init (fun _ => 0) ⟨0,W_pos⟩) :=
    Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨storage_repr payloads bounded,?_,?_,initial.net,initial.netSelf,by unfold Lmax; decide,?_,initial.env,initial.funds,initial.oracle⟩
  all_goals intro p index
  all_goals cases index with
    | there index => cases index with
      | there index => nomatch index

private theorem heap_repr (payloads : List (Fin W)) : Objects.HeapRepr heap bases 8 (machine payloads) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro R reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    decide +kernel
  · intro R reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    decide +kernel
  · intro R Q left right different
    obtain ⟨rfl,leftEq⟩ := refs left
    obtain ⟨rfl,rightEq⟩ := refs right
    cases leftEq
    cases rightEq
    exact (different rfl).elim
  · intro A E array reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    cases array
    refine ⟨?_,?_,?_⟩
    · with_unfolding_all change 16 + 2 ≤ W
      decide
    · intro _
      with_unfolding_all rfl
    · intro index item selected
      with_unfolding_all change ([indexValue (wmod 7)] : List PrimTy.uint.Denote)[index]? = some item at selected
      cases index with
      | zero => cases selected; exact ReprV.uint_of rfl
      | succ index => cases selected
  · intro name reference
    obtain ⟨different,_⟩ := refs reference
    cases different
  · intro name field R reference fieldType
    obtain ⟨different,_⟩ := refs reference
    cases different

private theorem represented (payloads : List (Fin W)) (bounded : payloads.length < 128) : Objects.StateRepr 128 1 8 (Frag.init Γ) (state payloads bounded) bases (machine payloads) := by
  refine ⟨core payloads bounded,heap_repr payloads,?_,by decide⟩
  intro R index
  cases index with
  | here => exact ⟨old,rfl,rfl⟩
  | there index => cases index with
    | here => exact ⟨old,rfl,rfl⟩
    | there index => nomatch index

private theorem allocator (payloads : List (Fin W)) : Objects.AllocatorRepr heap bases 8 (wmod 40) (machine payloads) := by
  refine ⟨heap_repr payloads,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro address above
    change 40 ≤ address at above
    simp only [machine,if_neg (show address ≠ 0 by omega),
      if_neg (show ¬ (address = 1 ∨ address = 2) by omega),if_neg (show address ≠ 7 by omega),
      if_neg (show address ≠ 16 by omega),if_neg (show address ≠ 17 by omega)]
  · intro R reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    decide +kernel

private theorem resolved (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    (path 0).resolveT (state payloads bounded) = .ok reference := by with_unfolding_all rfl
private theorem found (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    (state payloads bounded).storage.find reference = some (array payloads bounded) := by with_unfolding_all rfl
private def grown (payloads : List (Fin W)) (bounded : payloads.length < 128) := (array payloads bounded).copyStToM heap rfl
private def after (payloads : List (Fin W)) (bounded : payloads.length < 128) :=
  ((state payloads bounded).adopt (grown payloads bounded)).1.setLocal destination (some (grown payloads bounded).val)

private theorem payload_observations (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (base' : Nat → Fin W) (target : Machine) (fits : 40 + (payloads.length + 1) < W)
    (allocated : Objects.AllocatorRepr (grown payloads bounded).heap base' 8 ⟨40 + (payloads.length + 1),fits⟩ target)
    (rootAt : base' (grown payloads bounded).val.id = wmod 40) :
    target.mem 40 = .val (wmod payloads.length) ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload → target.mem (41 + index) = .val payload) := by
  have sourceLength : (grown payloads bounded).heap.len (grown payloads bounded).val .dyn = payloads.length := by
    dsimp only [grown,array]
    rw [primitive_array_source]
    simp only [Grown.alloc,Heap.len,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,values,List.length_map]
  constructor
  · have header : target.mem (base' (grown payloads bounded).val.id).val =
        .val (wmod ((grown payloads bounded).heap.len (grown payloads bounded).val .dyn)) :=
      (allocated.heap.arrays .dyn (grown payloads bounded).val).length rfl
    rw [rootAt,sourceLength] at header
    exact header
  · intro index payload selected
    have item : (MObj.elems .dyn ((grown payloads bounded).heap.get (grown payloads bounded).val))[index]? = some (indexValue payload) := by
      dsimp only [grown,array]
      rw [primitive_array_source]
      simp only [Grown.alloc,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,MVal.wk,values,
        List.getElem?_map,selected,Option.map_some]
    have contents : ReprV .uint (indexValue payload) (target.mem ((base' (grown payloads bounded).val.id).val + 1 + index)) :=
      (allocated.heap.arrays .dyn (grown payloads bounded).val).elements index (indexValue payload) item
    obtain ⟨word,stored,equal⟩ := contents
    have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst word
    rw [rootAt] at stored
    exact stored

theorem certificate_inhabited : CheckedStoragePathCertificate := checkedStoragePath

theorem declaration (payloads : List (Fin W)) (bounded : payloads.length < 128) (fits : 40 + (payloads.length + 1) < W) :
    ∃ target : Machine, run (checkedStoragePathDeclareCode 1 (path 0)) (machine payloads) = .ok target 0 ∧
      target.mem 0 = .val (wmod (40 + payloads.length + 1)) ∧ target.mem 3 = w[40] ∧
      target.mem 1 = w[16] ∧ target.mem 2 = w[16] ∧ target.mem 17 = w[7] ∧
      target.mem 40 = .val (wmod payloads.length) ∧ target.stack = [w[77]] ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload → target.mem (41 + index) = .val payload) := by
  obtain ⟨base',target,_,ran,_,allocated,_,stack,rootAt,localAt,below⟩ :=
    checked_storage_path_declaration_success (state payloads bounded) bases (wmod 40) (machine payloads) (path 0) reference
      (values payloads) (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide)
      (represented payloads bounded) (allocator payloads) (by decide) rfl (resolved payloads bounded) (found payloads bounded)
      (by simpa only [values,List.length_map] using fits) (by decide)
  have allocator' : Objects.AllocatorRepr (grown payloads bounded).heap base' 8 ⟨40 + (payloads.length + 1),fits⟩ target := by
    simpa only [values,List.length_map] using allocated
  change base' (grown payloads bounded).val.id = wmod 40 at rootAt
  obtain ⟨header,contents⟩ := payload_observations payloads bounded base' target fits allocator' rootAt
  refine ⟨target,ran,?_,localAt,below 1 (by decide) (by decide) (by decide),below 2 (by decide) (by decide) (by decide),
    below 17 (by decide) (by decide) (by decide),header,stack,contents⟩
  refine allocator'.free.cell.trans ?_
  apply congrArg Word.val
  apply Fin.ext
  change 40 + (payloads.length + 1) = (40 + payloads.length + 1) % W
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem rebinding (payloads : List (Fin W)) (bounded : payloads.length < 128) (fits : 40 + (payloads.length + 1) < W) :
    ∃ target : Machine, run (checkedStoragePathRebindCode 1 destination (path 0)) (machine payloads) = .ok target 0 ∧
      target.mem 0 = .val (wmod (40 + payloads.length + 1)) ∧ target.mem 2 = w[40] ∧
      target.mem 1 = w[16] ∧ target.mem 17 = w[7] ∧ target.mem 40 = .val (wmod payloads.length) ∧
      target.stack = [w[77]] ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload → target.mem (41 + index) = .val payload) := by
  obtain ⟨base',target,_,ran,_,allocated,_,stack,rootAt,localAt,below,_,_⟩ :=
    checked_storage_path_rebind_success (state payloads bounded) bases (wmod 40) (machine payloads) destination (path 0) reference
      (values payloads) (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide)
      (represented payloads bounded) (allocator payloads) (by decide) rfl (resolved payloads bounded) (found payloads bounded)
      (by simpa only [values,List.length_map] using fits)
  have allocator' : Objects.AllocatorRepr (grown payloads bounded).heap base' 8 ⟨40 + (payloads.length + 1),fits⟩ target := by
    simpa only [values,List.length_map] using allocated
  change base' (grown payloads bounded).val.id = wmod 40 at rootAt
  obtain ⟨header,contents⟩ := payload_observations payloads bounded base' target fits allocator' rootAt
  refine ⟨target,ran,?_,localAt,below 1 (by decide) (by decide) (by decide),below 17 (by decide) (by decide) (by decide),header,stack,contents⟩
  refine allocator'.free.cell.trans ?_
  apply congrArg Word.val
  apply Fin.ext
  change 40 + (payloads.length + 1) = (40 + payloads.length + 1) % W
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem old_source_alias (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    TEnv.get (.there .here : Idx Γ (.mem leaf)) (after payloads bounded).env = some (old.wk (grown payloads bounded).ext) := by
  with_unfolding_all rfl

theorem actual_source_rebinding (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    TRun.rebindMem destination (.copy (path 0) rfl) (state payloads bounded) =
      .ok ⟨after payloads bounded,(grown payloads bounded).ext⟩ :=
  runtime_path_array_rebind_source (state payloads bounded) destination (path 0) reference (values payloads)
    (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide) (resolved payloads bounded) (found payloads bounded)

theorem pair_declaration (left right : Fin W) : ∃ target : Machine,
    run (checkedStoragePathDeclareCode 1 (path 0)) (machine [left,right]) = .ok target 0 ∧
      target.mem 0 = w[43] ∧ target.mem 3 = w[40] ∧ target.mem 41 = .val left ∧ target.mem 42 = .val right ∧ target.mem 17 = w[7] := by
  obtain ⟨target,ran,cursor,localAt,_,_,old,_,_,contents⟩ :=
    declaration [left,right] (by change 2 < 128; decide) (by change 40 + (2 + 1) < W; decide)
  exact ⟨target,ran,cursor,localAt,contents 0 left rfl,contents 1 right rfl,old⟩

theorem empty_rebind : ∃ target : Machine,
    run (checkedStoragePathRebindCode 1 destination (path 0)) (machine []) = .ok target 0 ∧
      target.mem 0 = w[41] ∧ target.mem 2 = w[40] ∧ target.mem 1 = w[16] ∧ target.mem 40 = w[0] ∧ target.mem 17 = w[7] := by
  obtain ⟨target,ran,cursor,localAt,alias,old,length,_,_⟩ := rebinding [] (by decide) (by decide)
  exact ⟨target,ran,cursor,localAt,alias,length,old⟩

private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))

theorem long_rebind : ∃ target : Machine,
    run (checkedStoragePathRebindCode 1 destination (path 0)) (machine long) = .ok target 0 ∧
      target.mem 0 = w[105] ∧ target.mem 2 = w[40] ∧ target.mem 1 = w[16] ∧ target.mem 17 = w[7] ∧ target.mem 104 = w[64] := by
  obtain ⟨target,ran,cursor,localAt,alias,old,_,_,contents⟩ :=
    rebinding long (by rw [long,List.length_ofFn]; decide) (by rw [long,List.length_ofFn]; decide)
  exact ⟨target,ran,cursor,localAt,alias,old,contents 63 (wmod 64) (by decide +kernel)⟩

theorem invalid_declaration (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    TRun.declMem leaf (some (.copy (path 1) rfl)) rfl (state payloads bounded) = .error .revert ∧
      run (checkedStoragePathDeclareCode 1 (path 1)) (machine payloads) = .revert :=
  checked_storage_path_declaration_refusal (state payloads bounded) (machine payloads) (path 1) (core payloads bounded) rfl (by with_unfolding_all rfl)

theorem invalid_rebind (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    TRun.rebindMem destination (.copy (path 1) rfl) (state payloads bounded) = .error .revert ∧
      run (checkedStoragePathRebindCode 1 destination (path 1)) (machine payloads) = .revert :=
  checked_storage_path_rebind_refusal (state payloads bounded) (machine payloads) destination (path 1) (core payloads bounded) rfl (by with_unfolding_all rfl)

theorem invalid_empty : run (checkedStoragePathDeclareCode 1 (path 1)) (machine []) = .revert :=
  (invalid_declaration [] (by decide)).2

theorem old_pointer_rejected (target : Machine)
    (ran : run (checkedStoragePathRebindCode 1 destination (path 0)) (machine [wmod 11,wmod 23]) = .ok target 0) : target.mem 2 ≠ w[16] := by
  obtain ⟨actual,execution,_,localAt,_,_,_,_,_⟩ := rebinding [wmod 11,wmod 23] (by decide) (by decide)
  rw [ran] at execution
  have same : target.mem 2 = actual.mem 2 := congrArg (fun machine => machine.mem 2) (Out.ok.inj execution).1
  rw [same,localAt]
  decide

private def saturated (payloads : List (Fin W)) : Machine := writeMachine (machine payloads) 0 (.val wMax)
private theorem saturated_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.StateRepr 128 1 8 (Frag.init Γ) (state payloads bounded) bases (saturated payloads) := by
  have initial : Objects.StateRepr 128 1 8 (Frag.init Γ) (state payloads bounded) bases (machine payloads) := represented payloads bounded
  refine ⟨initial.core.congrMem ?_,initial.heap.localWrite 0 (by decide) (.val wMax),?_,initial.locals⟩
  · intro level lower upper
    exact upd_other _ _ (by change level ≠ 0; omega)
  · intro R index
    obtain ⟨reference,found,word⟩ := initial.pointers index
    refine ⟨reference,found,?_⟩
    change upd (machine payloads).mem 0 (.val wMax) (cellOf 1 index) = _
    rw [upd_other _ _ (by have lower : 1 ≤ lvl 1 index := le_lvl 1 index; change lvl 1 index ≠ 0; omega)]
    exact word
private theorem saturated_allocator (payloads : List (Fin W)) :
    Objects.AllocatorRepr heap bases 8 wMax (saturated payloads) := by
  have initial : Objects.AllocatorRepr heap bases 8 (wmod 40) (machine payloads) := allocator payloads
  have high : 40 ≤ wMax.val := by decide
  refine ⟨initial.heap.localWrite 0 (by decide) (.val wMax),⟨by decide,by omega,?_,?_⟩,?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (initial.free.zero address (by change 40 ≤ address; omega))
  · intro R reference
    have live : (bases reference.id).val + Objects.cells heap reference ≤ 40 := initial.live reference
    exact Nat.le_trans live high

theorem capacity_refusal (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    (path 0).resolveT (state payloads bounded) = .ok reference ∧
    ¬ wMax.val + ((values payloads).length + 1) < W ∧
    run (checkedStoragePathDeclareCode 1 (path 0)) (saturated payloads) = .revert ∧
    run (checkedStoragePathRebindCode 1 destination (path 0)) (saturated payloads) = .revert := by
  have nofit : ¬ wMax.val + ((values payloads).length + 1) < W := by
    change ¬ (W - 1 + (_ + 1) < W)
    have positive : 0 < W := W_pos
    omega
  refine ⟨resolved payloads bounded,nofit,?_,?_⟩
  · rcases checked_storage_path_declaration (state payloads bounded) bases wMax (saturated payloads) (path 0) reference
      (values payloads) (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide)
      (saturated_repr payloads bounded) (saturated_allocator payloads) (by decide) rfl
      (resolved payloads bounded) (found payloads bounded) (by decide) with ⟨fits,result⟩ | failed
    · exact (nofit fits).elim
    · exact failed.2
  · rcases checked_storage_path_rebind (state payloads bounded) bases wMax (saturated payloads) destination (path 0) reference
      (values payloads) (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide)
      (saturated_repr payloads bounded) (saturated_allocator payloads) (by decide) rfl
      (resolved payloads bounded) (found payloads bounded) with ⟨fits,result⟩ | failed
    · exact (nofit fits).elim
    · exact failed.2

theorem empty_capacity_refusal :
    run (checkedStoragePathDeclareCode 1 (path 0)) (saturated []) = .revert ∧
    run (checkedStoragePathRebindCode 1 destination (path 0)) (saturated []) = .revert :=
  (capacity_refusal [] (by decide)).2.2

theorem bounds_before_capacity (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    TRun.declMem leaf (some (.copy (path 1) rfl)) rfl (state payloads bounded) = .error .revert ∧
    run (checkedStoragePathDeclareCode 1 (path 1)) (saturated payloads) = .revert :=
  checked_storage_path_declaration_refusal (state payloads bounded) (saturated payloads) (path 1)
    (saturated_repr payloads bounded).core rfl (by with_unfolding_all rfl)

#print axioms certificate_inhabited
#print axioms declaration
#print axioms rebinding
#print axioms old_source_alias
#print axioms actual_source_rebinding
#print axioms pair_declaration
#print axioms empty_rebind
#print axioms long_rebind
#print axioms invalid_declaration
#print axioms invalid_rebind
#print axioms invalid_empty
#print axioms old_pointer_rejected
#print axioms capacity_refusal
#print axioms empty_capacity_refusal
#print axioms bounds_before_capacity
end Solidity.Backend.MemoryCopies.CheckedStoragePathControls
