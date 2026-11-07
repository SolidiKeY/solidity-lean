import Solidity.Backend.MemoryCopies.LoadedSingleton
import Solidity.Evm.Correct

/-! Actual storage-root and element reads feed singleton-copy code. Different
stored words execute identical code; an out-of-bounds read reverts first. -/
namespace Solidity.Backend.MemoryCopies.LoadedSingletonControls
open Evm Evm.Memory Semantics
private def C : Contract := {vars := [("stored",.ref (.array (.prim .uint)))]}
private def root : C.rootType "stored" = some (.ref (.array (.prim .uint))) := by decide +kernel
private def value (payload : Fin W) : PrimTy.uint.Denote := indexValue payload
private def state (payload : Fin W) : State C [] :=
  {State.init C with storage := .cons (singletonArrayValue .uint (value payload)) .nil}
private def store (payload : Fin W) : WordStore :=
  ⟨fun slot => if slot = .root 0 then wmod 1 else payload⟩
private def machine (payload : Fin W) : Machine :=
  {Machine.init with
    store := store payload
    stack := [w[77]]
    mem := fun address => if address = 0 then w[40] else if address = 7 then w[99] else w[0]}
private def bases : Nat → Fin W := fun _ => wmod 0
private def path {Γ : Ctx} : SPath C Γ (.ref (.array (.prim .uint))) := .loc (.root "stored" root)
private def expression {Γ : Ctx} (index : Nat) : Val C Γ .uint :=
  .read (.index (.arr .dyn) path (.simple (.lit (indexValue (wmod index)).val (indexValue (wmod index)).property)))
private theorem noRefs {R : RefTy} (reference : HRef [] R) : False := by
  simpa only [List.getElem?_nil,reduceCtorEq] using reference.get?

private theorem storage_repr (payload : Fin W) : ReprStore C 2 (store payload) (state payload).storage := by
  intro name type found
  change (if name = "stored" then some (.ref (.array (.prim .uint))) else none) = some type at found
  split at found
  · rename_i same
    subst name
    cases found
    change ReprAt (store payload) 2 (.ref (.array (.prim .uint))) (.root 0) (singletonArrayValue .uint (value payload))
    refine .array rfl (by decide) ?_
    intro index item selected
    simp only [SVec.toList_cons,SVec.toList_nil] at selected
    cases index with
    | zero => cases selected; exact .prim (ReprV.uint_of rfl)
    | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at selected; cases selected
  · cases found

private theorem core (payload : Fin W) : Sim C 2 1 (Frag.init []) (state payload) (machine payload) := by
  have initial : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0,W_pos⟩) (Machine.init (fun _ => 0) ⟨0,W_pos⟩) :=
    Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  exact ⟨storage_repr payload,(fun index => nomatch index),(fun index => nomatch index),
    initial.net,initial.netSelf,by unfold Lmax; decide,(fun index => nomatch index),initial.env,initial.funds,initial.oracle⟩

private theorem heap_repr (payload : Fin W) : Objects.HeapRepr (state payload).heap bases 8 (machine payload) :=
  ⟨⟨fun reference => (noRefs reference).elim,fun reference => (noRefs reference).elim,
      fun reference _ _ => (noRefs reference).elim⟩,
    (fun _ reference => (noRefs reference).elim),(fun reference => (noRefs reference).elim),
    (fun reference _ => (noRefs reference).elim)⟩

private theorem represented (payload : Fin W) : Objects.StateRepr 2 1 8 (Frag.init []) (state payload) bases (machine payload) :=
  ⟨core payload,heap_repr payload,(fun index => nomatch index),by decide⟩

private theorem allocator (payload : Fin W) : Objects.AllocatorRepr (state payload).heap bases 8 (wmod 40) (machine payload) := by
  refine ⟨heap_repr payload,⟨by decide,by decide,rfl,?_⟩,fun reference => (noRefs reference).elim⟩
  intro address above
  change 40 ≤ address at above
  simp only [machine,if_neg (show address ≠ 0 by omega),if_neg (show address ≠ 7 by omega)]

private theorem found (payload : Fin W) :
    (state payload).storage.find (SRef.ofRoot "stored" root) = some (singletonArrayValue .uint (value payload)) := by
  with_unfolding_all rfl

private theorem evaluated (payload : Fin W) : (expression 0).evalT (state payload) = .ok (value payload) := by
  with_unfolding_all rfl

theorem certificate_inhabited : LoadedSingletonCertificate := loadedSingleton

theorem source_read (payload : Fin W) : (expression 0).evalT (state payload) = .ok (value payload) := evaluated payload

theorem storage_copy_source (payload : Fin W) :
    (MRhs.copy (path (Γ := [])) rfl).evalT (state payload) =
      .ok ((state payload).copyStToMG (singletonArrayValue .uint (value payload)) rfl) :=
  storage_singleton_rhs (state payload) path (SRef.ofRoot "stored" root) (value payload) rfl (found payload)

theorem emits_storage_load : Instr.sload ∈ compileVal 1 (expression (Γ := []) 0) := by
  rw [expression,Evm.compileVal]
  exact List.mem_append_right _ (List.mem_cons_self ..)

/-- A complete actual storage-copy declaration, with its loaded value and root. -/
theorem declaration (payload : Fin W) :
    ∃ target, run (loadedSingletonDeclareCode 1 (expression (Γ := []) 0)) (machine payload) = .ok target 0 ∧
      target.mem 0 = w[42] ∧ target.mem 1 = w[40] ∧ target.mem 40 = w[1] ∧
      target.mem 41 = .val payload ∧ target.mem 7 = w[99] ∧ target.stack = [w[77]] := by
  let grown := (singletonArrayValue .uint (value payload)).copyStToM (state payload).heap rfl
  obtain ⟨base',target,source,ran,reached,allocated,extension,stack,rootAt,localAt,below⟩ :=
    loaded_singleton_declare_correct (expression 0) (value payload) (state payload) bases (wmod 40) (machine payload)
      (represented payload) (allocator payload) (by decide) (by decide +kernel) (evaluated payload)
      path (SRef.ofRoot "stored" root) rfl (found payload) (by decide) (by decide)
  have length : target.mem (base' grown.val.id).val = w[1] := by
    have header : target.mem (base' grown.val.id).val = .val (wmod (grown.heap.len grown.val .dyn)) :=
      (allocated.heap.arrays .dyn grown.val).length rfl
    rw [singleton_copy_length] at header
    exact header
  have item : (MObj.elems .dyn (grown.heap.get grown.val))[0]? = some (value payload) := by
    dsimp only [grown]
    rw [singleton_copy_source]
    with_unfolding_all rfl
  have contents : ReprV .uint (value payload) (target.mem ((base' grown.val.id).val + 1)) :=
    (allocated.heap.arrays .dyn grown.val).elements 0 (value payload) item
  obtain ⟨word,stored,equal⟩ := contents
  have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
  subst word
  rw [rootAt] at length stored
  exact ⟨target,ran,allocated.free.cell,localAt,length,stored,below 7 (by decide) (by decide) (by decide),stack⟩

theorem uint11 : ∃ target, run (loadedSingletonDeclareCode 1 (expression (Γ := []) 0)) (machine (wmod 11)) = .ok target 0 ∧
    target.mem 41 = w[11] := by
  obtain ⟨target,ran,_,_,_,stored,_,_⟩ := declaration (wmod 11)
  exact ⟨target,ran,stored⟩

theorem uint23 : ∃ target, run (loadedSingletonDeclareCode 1 (expression (Γ := []) 0)) (machine (wmod 23)) = .ok target 0 ∧
    target.mem 41 = w[23] := by
  obtain ⟨target,ran,_,_,_,stored,_,_⟩ := declaration (wmod 23)
  exact ⟨target,ran,stored⟩

theorem out_of_bounds_source (payload : Fin W) : (expression 1).evalT (state payload) = .error .revert := by
  with_unfolding_all rfl

theorem out_of_bounds_target (payload : Fin W) :
    run (loadedSingletonCopyCode 1 (expression (Γ := []) 1)) (machine payload) = .revert :=
  loaded_singleton_refusal (expression 1) (state payload) (machine payload) (core payload)
    (by decide +kernel) (out_of_bounds_source payload)

theorem wrong_literal_rejected (target : Machine)
    (ran : run (loadedSingletonDeclareCode 1 (expression (Γ := []) 0)) (machine (wmod 23)) = .ok target 0) :
    target.mem 41 ≠ w[11] := by
  obtain ⟨actual,execution,stored⟩ := uint23
  rw [ran] at execution
  cases execution
  rw [stored]
  decide

#print axioms certificate_inhabited
#print axioms source_read
#print axioms storage_copy_source
#print axioms emits_storage_load
#print axioms declaration
#print axioms uint11
#print axioms uint23
#print axioms out_of_bounds_source
#print axioms out_of_bounds_target
#print axioms wrong_literal_rejected
end Solidity.Backend.MemoryCopies.LoadedSingletonControls
