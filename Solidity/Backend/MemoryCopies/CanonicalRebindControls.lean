import Solidity.Backend.MemoryCopies.CanonicalRebind
import Solidity.Backend.MemoryCopies.AliasBinding
import Solidity.Evm.Correct

/-! Two locals initially alias a populated old array. A real storage copy
redirects one to a fresh populated leaf; an alias rebind allocates nothing. -/
namespace Solidity.Backend.MemoryCopies.CanonicalRebindControls
open Evm Evm.Memory Semantics
private abbrev leaf : RefTy := .array (.prim .uint)
private def C : Contract := {vars := [("matrix",.ref (.array (.ref leaf)))]}
private def root : C.rootType "matrix" = some (.ref (.array (.ref leaf))) := by decide +kernel
private def value (payload : Fin W) : PrimTy.uint.Denote := indexValue payload
private def matrixValue (payload : Fin W) : SVal (.ref (.array (.ref leaf))) :=
  .array (.cons (singletonArrayValue .uint (value payload)) .nil) .nil (by decide)
private abbrev H : HTy := [leaf]
private abbrev Γ : Ctx := [.mem leaf,.mem leaf]
private def old : HRef H leaf := ⟨0,rfl⟩
private def heap : Heap H := (⟨[indexValue (wmod 7)],by decide⟩,())
private def state (payload : Fin W) : State C Γ :=
  {storage := .cons (matrixValue payload) .nil,H := H,heap := heap,env := (some old,(some old,()))}
private def store (payload : Fin W) : WordStore :=
  ⟨fun slot => if slot = .root 0 ∨ slot = .data (.root 0) 0 then wmod 1 else payload⟩
private def machine (payload : Fin W) : Machine :=
  {Machine.init with store := store payload,stack := [w[77]],mem := fun address =>
    if address = 0 then w[40] else if address = 1 ∨ address = 2 then w[16]
    else if address = 7 then w[99] else if address = 16 then w[1] else if address = 17 then w[7] else w[0]}
private def bases : Nat → Fin W := fun _ => wmod 16
private def path (index : Nat) : SPath C Γ (.ref leaf) :=
  .loc (.index (.arr .dyn) (.loc (.root "matrix" root))
    (.simple (.lit (indexValue (wmod index)).val (indexValue (wmod index)).property)))
private def reference : SRef C (.ref leaf) := (SRef.ofRoot "matrix" root).index (.arr .dyn) (indexValue (wmod 0))
private def destination : Idx Γ (.mem leaf) := .here
private def aliasPath : MPath C Γ (.ref leaf) := .var (.there .here) rfl
private def alias : SelectedAlias 1 (Frag.init Γ) aliasPath := selectedAlias 1 (Frag.init Γ) aliasPath rfl
private theorem refs {R : RefTy} (reference : HRef H R) : R = leaf ∧ HEq reference old := by
  rcases reference with ⟨index,selected⟩
  cases index with
  | zero => cases selected; exact ⟨rfl,HEq.rfl⟩
  | succ index => cases selected

private theorem leaf_repr (payload : Fin W) :
    ReprAt (store payload) 2 (.ref leaf) (.data (.root 0) 0) (singletonArrayValue .uint (value payload)) := by
  refine .array rfl (by decide) ?_
  intro index item selected
  simp only [SVec.toList_cons,SVec.toList_nil] at selected
  cases index with
  | zero => cases selected; exact .prim (ReprV.uint_of rfl)
  | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at selected; cases selected

private theorem storage_repr (payload : Fin W) : ReprStore C 2 (store payload) (state payload).storage := by
  intro name type found
  change (if name = "matrix" then some (.ref (.array (.ref leaf))) else none) = some type at found
  split at found
  · rename_i same
    subst name
    cases found
    change ReprAt (store payload) 2 (.ref (.array (.ref leaf))) (.root 0) (matrixValue payload)
    refine .array rfl (by decide) ?_
    intro index item selected
    simp only [SVec.toList_cons,SVec.toList_nil] at selected
    cases index with
    | zero => cases selected; exact leaf_repr payload
    | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at selected; cases selected
  · cases found

private theorem core (payload : Fin W) : Sim C 2 1 (Frag.init Γ) (state payload) (machine payload) := by
  have initial : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0,W_pos⟩) (Machine.init (fun _ => 0) ⟨0,W_pos⟩) :=
    Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨storage_repr payload,?_,?_,initial.net,initial.netSelf,by unfold Lmax; decide,?_,initial.env,initial.funds,initial.oracle⟩
  all_goals intro p index
  all_goals cases index with
    | there index => cases index with
      | there index => nomatch index

private theorem heap_repr (payload : Fin W) : Objects.HeapRepr heap bases 8 (machine payload) := by
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

private theorem represented (payload : Fin W) : Objects.StateRepr 2 1 8 (Frag.init Γ) (state payload) bases (machine payload) := by
  refine ⟨core payload,heap_repr payload,?_,by decide⟩
  intro R index
  cases index with
  | here => exact ⟨old,rfl,rfl⟩
  | there index => cases index with
    | here => exact ⟨old,rfl,rfl⟩
    | there index => nomatch index

private theorem allocator (payload : Fin W) : Objects.AllocatorRepr heap bases 8 (wmod 40) (machine payload) := by
  refine ⟨heap_repr payload,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro address above
    change 40 ≤ address at above
    simp only [machine,if_neg (show address ≠ 0 by omega),
      if_neg (show ¬ (address = 1 ∨ address = 2) by omega),if_neg (show address ≠ 7 by omega),
      if_neg (show address ≠ 16 by omega),if_neg (show address ≠ 17 by omega)]
  · intro R reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    decide +kernel

private theorem resolved (payload : Fin W) : (path 0).resolveT (state payload) = .ok reference := by
  with_unfolding_all rfl
private theorem found (payload : Fin W) :
    (state payload).storage.find reference = some (singletonArrayValue .uint (value payload)) := by
  with_unfolding_all rfl
private def grown (payload : Fin W) := (singletonArrayValue .uint (value payload)).copyStToM heap rfl
private def after (payload : Fin W) := ((state payload).adopt (grown payload)).1.setLocal destination (some (grown payload).val)

theorem inhabited : CanonicalRebindCertificate := canonicalRebind

theorem copy_result (payload : Fin W) :
    CanonicalRebindResult 2 1 8 (Frag.init Γ) (state payload) bases (wmod 40) (machine payload)
      destination (path 0) (value payload) (by decide) :=
  canonical_rebind_correct (state payload) bases (wmod 40) (machine payload) destination (path 0) reference (value payload)
    (represented payload) (allocator payload) (by decide) rfl (resolved payload) (found payload) (by decide)

theorem old_source_alias (payload : Fin W) :
    TEnv.get (.there .here : Idx Γ (.mem leaf)) (after payload).env = some (old.wk (grown payload).ext) := by
  with_unfolding_all rfl

theorem fresh_source_binding (payload : Fin W) :
    TRun.rebindMem destination (.copy (path 0) rfl) (state payload) =
      .ok ⟨after payload,(grown payload).ext⟩ ∧ (grown payload).val.id = 1 ∧
    (grown payload).heap.get (old.wk (grown payload).ext) = MObj.wk (grown payload).ext leaf (heap.get old) := by
  refine ⟨canonical_rebind_source (state payload) destination (path 0) reference (value payload)
    (resolved payload) (found payload),by with_unfolding_all rfl,?_⟩
  exact (SVal.keeps_copyStToM _ rfl heap) old

theorem copied_target (payload : Fin W) :
    ∃ target, run (canonicalRebindCode 1 destination (path 0)) (machine payload) = .ok target 0 ∧
      target.mem 0 = w[42] ∧ target.mem 2 = w[40] ∧ target.mem 1 = w[16] ∧
      target.mem 17 = w[7] ∧ target.mem 40 = w[1] ∧ target.mem 41 = .val payload ∧
      target.mem 7 = w[99] ∧ target.stack = [w[77]] := by
  obtain ⟨base',target,_,ran,_,allocated,_,stack,rootAt,localAt,below,_,_⟩ := copy_result payload
  have length : target.mem (base' (grown payload).val.id).val = w[1] := by
    have header : target.mem (base' (grown payload).val.id).val = .val (wmod ((grown payload).heap.len (grown payload).val .dyn)) :=
      (allocated.heap.arrays .dyn (grown payload).val).length rfl
    dsimp only [grown] at header
    rw [singleton_copy_length] at header
    exact header
  have item : (MObj.elems .dyn ((grown payload).heap.get (grown payload).val))[0]? = some (value payload) := by
    dsimp only [grown]
    rw [singleton_copy_source]
    with_unfolding_all rfl
  have contents : ReprV .uint (value payload) (target.mem ((base' (grown payload).val.id).val + 1)) :=
    (allocated.heap.arrays .dyn (grown payload).val).elements 0 (value payload) item
  obtain ⟨word,stored,equal⟩ := contents
  have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
  subst word
  change base' (grown payload).val.id = wmod 40 at rootAt
  rw [rootAt] at length stored
  exact ⟨target,ran,allocated.free.cell,localAt,below 1 (by decide) (by decide) (by decide),
    below 17 (by decide) (by decide) (by decide),length,stored,below 7 (by decide) (by decide) (by decide),stack⟩

private def observe : Evm.Out → Option (Evm.Word × Evm.Word × Evm.Word × Evm.Word)
  | .ok target _ => some (target.mem 0,target.mem 1,target.mem 2,target.mem 17)
  | _ => none

theorem alias_target (payload : Fin W) :
    observe (run (alias.code destination) (machine payload)) = some (w[40],w[16],w[16],w[7]) := by
  with_unfolding_all rfl

theorem alias_source (payload : Fin W) :
    TRun.rebindMem destination (.alias aliasPath) (state payload) =
      .ok ⟨(state payload).setLocal destination (some old),List.prefix_refl _⟩ := by
  with_unfolding_all rfl

theorem alias_certificate (payload : Fin W) :
    AliasBindingOutcome 2 1 8 (Frag.init Γ) (state payload) bases (machine payload) aliasPath destination (alias.code destination) :=
  alias.execute (represented payload) destination

theorem copy_is_not_alias (payload : Fin W) :
    observe (run (canonicalRebindCode 1 destination (path 0)) (machine payload)) ≠
      observe (run (alias.code destination) (machine payload)) := by
  obtain ⟨target,ran,free,installed,other,previous,_,_,_,_⟩ := copied_target payload
  rw [ran,alias_target]
  change some (target.mem 0,target.mem 1,target.mem 2,target.mem 17) ≠ _
  rw [free,other,installed,previous]
  decide

theorem invalid_path (payload : Fin W) :
    TRun.rebindMem destination (.copy (path 1) rfl) (state payload) = .error .revert ∧
    run (canonicalRebindCode 1 destination (path 1)) (machine payload) = .revert :=
  canonical_rebind_refusal (state payload) (machine payload) destination (path 1) (core payload) rfl (by with_unfolding_all rfl)

#print axioms inhabited
#print axioms copy_result
#print axioms old_source_alias
#print axioms fresh_source_binding
#print axioms copied_target
#print axioms alias_target
#print axioms alias_source
#print axioms alias_certificate
#print axioms copy_is_not_alias
#print axioms invalid_path
end Solidity.Backend.MemoryCopies.CanonicalRebindControls
