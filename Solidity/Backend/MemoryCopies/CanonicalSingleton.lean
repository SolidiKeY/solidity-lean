import Solidity.Backend.MemoryCopies.CanonicalSingletonInterface

/-! Existing storage paths choose their own index-zero expression. Successful
lookup and supported resolution derive evaluation, rather than assume its value. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem canonical_singleton_supported {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (frag : Frag Γ) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (supported : spathIn frag false path = true) : valIn frag (canonicalSingletonExpression path) = true := by
  change (true && spathIn frag false path && true) = true
  rw [supported]
  rfl

theorem canonical_singleton_evaluation {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (value : primitive.Denote)
    (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (singletonArrayValue primitive value)) :
    (canonicalSingletonExpression path).evalT state = .ok value := by
  let zero : PrimTy.uint.Denote := ⟨0,by decide⟩
  have checked : state.storage.checkIndex reference (.arr .dyn) zero = some () := by
    rw [Storage.checkIndex,found]
    with_unfolding_all rfl
  have indexed : state.storage.find (reference.index (.arr .dyn) zero) = some (.prim value) := by
    rw [SRef.index,Storage.find_appendM,found]
    with_unfolding_all rfl
  dsimp only [zero] at checked indexed
  simp only [canonicalSingletonExpression,Val.evalT,Loc.resolveT,resolved,Simple.evalT,PrimTy.ofLit,
    checked,indexed,TRes.ofOpt,bind,Except.bind,pure,Except.pure,SVal.view_prim]

theorem canonical_singleton_failed_evaluation {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (refused : path.resolveT state = .error .revert) :
    (canonicalSingletonExpression path).evalT state = .error .revert := by
  simp only [canonicalSingletonExpression,Val.evalT,Loc.resolveT,refused,bind,Except.bind]

theorem canonical_singleton_declaration {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    {L b frame : Nat} {frag : Frag Γ} (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (value : primitive.Denote)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (singletonArrayValue primitive value))
    (fits : cursor.val + 2 < W) (locals : b + (Γ.length + 1) ≤ frame) :
    CanonicalSingletonResult L b frame frag state base cursor machine path value fits :=
  loaded_singleton_declare_correct (canonicalSingletonExpression path) value state base cursor machine
    represented allocator positive (canonical_singleton_supported frag path supported)
    (canonical_singleton_evaluation state path reference value resolved found) path reference resolved found fits locals

theorem canonical_singleton_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    {L b : Nat} {frag : Frag Γ} (state : State C Γ) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive))))
    (represented : Sim C L b frag state machine) (supported : spathIn frag false path = true)
    (refused : path.resolveT state = .error .revert) :
    TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state = .error .revert ∧
      run (canonicalSingletonCode b path) machine = .revert := by
  constructor
  · simp only [TRun.declMem,MRhs.evalT,refused,bind,Except.bind]
  · exact run_append_revert (loaded_singleton_refusal (canonicalSingletonExpression path) state machine represented
      (canonical_singleton_supported frag path supported) (canonical_singleton_failed_evaluation state path refused))

def canonicalSingleton : CanonicalSingletonCertificate :=
  ⟨canonical_singleton_supported,canonical_singleton_evaluation,canonical_singleton_declaration,canonical_singleton_refusal⟩

theorem canonical_singleton_load {C : Contract} {Γ : Ctx} {primitive : PrimTy} (b : Nat)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) :
    Instr.sload ∈ Evm.compileVal b (canonicalSingletonExpression path) := by
  rw [canonicalSingletonExpression,Evm.compileVal]
  exact List.mem_append_right _ (List.mem_cons_self ..)

#print axioms canonical_singleton_supported
#print axioms canonical_singleton_evaluation
#print axioms canonical_singleton_failed_evaluation
#print axioms canonical_singleton_declaration
#print axioms canonical_singleton_refusal
#print axioms canonicalSingleton
#print axioms canonical_singleton_load
end Solidity.Backend.MemoryCopies
