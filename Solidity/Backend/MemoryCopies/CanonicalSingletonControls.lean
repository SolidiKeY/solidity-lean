import Solidity.Backend.MemoryCopies.CanonicalSingleton
import Solidity.Evm.Correct

/-! Canonical copies select a singleton leaf below a real nested dynamic storage
path. The outer out-of-bounds path refuses in source and emitted declaration. -/
namespace Solidity.Backend.MemoryCopies.CanonicalSingletonControls
open Evm Evm.Memory Semantics
private abbrev leaf : RefTy := .array (.prim .uint)
private def C : Contract := {vars := [("matrix",.ref (.array (.ref leaf)))]}
private def root : C.rootType "matrix" = some (.ref (.array (.ref leaf))) := by decide +kernel
private def value (payload : Fin W) : PrimTy.uint.Denote := indexValue payload
private def matrixValue (payload : Fin W) : SVal (.ref (.array (.ref leaf))) :=
  .array (.cons (singletonArrayValue .uint (value payload)) .nil) .nil (by decide)
private def state (payload : Fin W) : State C [] :=
  {State.init C with storage := .cons (matrixValue payload) .nil}
private def store (payload : Fin W) : WordStore :=
  ⟨fun slot => if slot = .root 0 ∨ slot = .data (.root 0) 0 then wmod 1 else payload⟩
private def machine (payload : Fin W) : Machine :=
  {Machine.init with
    store := store payload
    stack := [w[77]]
    mem := fun address => if address = 0 then w[40] else if address = 7 then w[99] else w[0]}
private def bases : Nat → Fin W := fun _ => wmod 0
private def path {Γ : Ctx} (index : Nat) : SPath C Γ (.ref leaf) :=
  .loc (.index (.arr .dyn) (.loc (.root "matrix" root))
    (.simple (.lit (indexValue (wmod index)).val (indexValue (wmod index)).property)))
private def reference : SRef C (.ref leaf) := (SRef.ofRoot "matrix" root).index (.arr .dyn) (indexValue (wmod 0))
private theorem noRefs {R : RefTy} (reference : HRef [] R) : False := by
  simpa only [List.getElem?_nil,reduceCtorEq] using reference.get?

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


private theorem resolved (payload : Fin W) : (path 0).resolveT (state payload) = .ok reference := by
  with_unfolding_all rfl
private theorem found (payload : Fin W) :
    (state payload).storage.find reference = some (singletonArrayValue .uint (value payload)) := by
  with_unfolding_all rfl

theorem certificate_inhabited : CanonicalSingletonCertificate := canonicalSingleton

theorem path_supported (index : Nat) : spathIn (Frag.init []) false (path (Γ := []) index) = true := rfl

theorem nested_lookup (payload : Fin W) :
    (state payload).storage.find reference = some (singletonArrayValue .uint (value payload)) := found payload

theorem derived_evaluation (payload : Fin W) :
    (canonicalSingletonExpression (path 0)).evalT (state payload) = .ok (value payload) :=
  canonical_singleton_evaluation (state payload) (path 0) reference (value payload) (resolved payload) (found payload)

theorem source_copy (payload : Fin W) :
    (MRhs.copy (path (Γ := []) 0) rfl).evalT (state payload) =
      .ok ((state payload).copyStToMG (singletonArrayValue .uint (value payload)) rfl) :=
  storage_singleton_rhs (state payload) (path 0) reference (value payload) (resolved payload) (found payload)

theorem emits_load : Instr.sload ∈ Evm.compileVal 1 (canonicalSingletonExpression (path (Γ := []) 0)) :=
  canonical_singleton_load 1 (path 0)

theorem declaration (payload : Fin W) :
    ∃ target, run (canonicalSingletonCode 1 (path (Γ := []) 0)) (machine payload) = .ok target 0 ∧
      target.mem 0 = w[42] ∧ target.mem 1 = w[40] ∧ target.mem 40 = w[1] ∧
      target.mem 41 = .val payload ∧ target.mem 7 = w[99] ∧ target.stack = [w[77]] := by
  let grown := (singletonArrayValue .uint (value payload)).copyStToM (state payload).heap rfl
  obtain ⟨base',target,source,ran,reached,allocated,extension,stack,rootAt,localAt,below⟩ :=
    canonical_singleton_declaration (state payload) bases (wmod 40) (machine payload) (path 0) reference (value payload)
      (represented payload) (allocator payload) (by decide) (path_supported 0) (resolved payload) (found payload)
      (by decide) (by decide)
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

theorem stored23 : ∃ target, run (canonicalSingletonCode 1 (path (Γ := []) 0)) (machine (wmod 23)) = .ok target 0 ∧
    target.mem 41 = w[23] := by
  obtain ⟨target,ran,_,_,_,stored,_,_⟩ := declaration (wmod 23)
  exact ⟨target,ran,stored⟩

theorem wrong_literal (target : Machine)
    (ran : run (canonicalSingletonCode 1 (path (Γ := []) 0)) (machine (wmod 23)) = .ok target 0) : target.mem 41 ≠ w[11] := by
  obtain ⟨actual,execution,stored⟩ := stored23
  rw [ran] at execution
  cases execution
  rw [stored]
  decide

theorem invalid_path (payload : Fin W) : (path 1).resolveT (state payload) = .error .revert := by
  with_unfolding_all rfl

theorem invalid_source (payload : Fin W) :
    TRun.declMem leaf (some (.copy (path (Γ := []) 1) rfl)) rfl (state payload) = .error .revert :=
  (canonical_singleton_refusal (state payload) (machine payload) (path 1) (core payload)
    (path_supported 1) (invalid_path payload)).1

theorem invalid_target (payload : Fin W) : run (canonicalSingletonCode 1 (path (Γ := []) 1)) (machine payload) = .revert :=
  (canonical_singleton_refusal (state payload) (machine payload) (path 1) (core payload)
    (path_supported 1) (invalid_path payload)).2

#print axioms certificate_inhabited
#print axioms path_supported
#print axioms nested_lookup
#print axioms derived_evaluation
#print axioms source_copy
#print axioms emits_load
#print axioms declaration
#print axioms stored23
#print axioms wrong_literal
#print axioms invalid_path
#print axioms invalid_source
#print axioms invalid_target
end Solidity.Backend.MemoryCopies.CanonicalSingletonControls
