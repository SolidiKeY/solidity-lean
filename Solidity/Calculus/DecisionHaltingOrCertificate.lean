import Solidity.Calculus.DecisionHaltingOrReason
import Solidity.Calculus.CloseFrame

/-! # Positive-key partial-OR certificates
These source certificates leave guard reconstruction and decision dispatch unchanged.
-/
namespace Solidity.Decide.ResidueReason
namespace PartialOrRoots
variable {C : Contract}

/-- A positive first key and zero second key bypass the partial subtraction. -/
theorem sourceGuard_positive (sp : PartialOrRoots C) (σ : State C [])
    (key : PrimTy.uint.Denote) (hk : 0 < key.1) :
    holds ((σ.push (t := .val .uint) key).push
      (t := .val .uint) (uintOfNat 0))
      (.eq sp.sourceGuard (.app0 (.lit true))) := by
  have hz : decide (key.1 ≤ 0) = false := decide_eq_false (by omega)
  change ((some (decide (key.1 ≤ 0))).bind
    (fun x => binopT (p := .bool) .and rfl x _)).bind
    (fun x => binopT (p := .bool) .or rfl x (some (decide (key.1 ≤ key.1)))) = some true
  rw [hz]
  change some (decide (key.1 ≤ key.1)) = some true
  simp only [Int.le_refl, decide_true]

/-- Instantiate the actual two-binder antecedent; no scalar definedness premise. -/
theorem sourceClaim_positive_valid (sp : PartialOrRoots C) (first second : Var)
    (value key : PrimTy.uint.Denote) (hk : 0 < key.1) :
    Fml.Valid (sp.sourceClaim first second value key value) := by
  intro σ h
  exact h key (uintOfNat 0) (sp.sourceGuard_positive σ key hk)

/-- Every mapping key reads zero in an actual initialized storage, in any context. -/
theorem mapRead_initial (sp : PartialOrRoots C) {Γ : Ctx} (σ : State C Γ)
    (hs : σ.storage = Storage.init C) (key : Tm C Γ (.val .uint))
    (value : PrimTy.uint.Denote) (hk : key.eval σ = some value) :
    (sp.mapRead key).eval σ = some (uintOfNat 0) := by
  simp only [mapRead, Tm.eval_app2, Tm.eval_app0, Op0.eval_eq_evalM,
    Op0.evalM, Op2.eval_eq_evalM, Op2.evalM, hk, Option.bind_eq_bind,
    Option.bind_some, Storage.atT, CloseS.checkIndex_map_root]
  change (σ.storage.find ((SRef.ofRoot sp.mapping sp.mappingType :
    SRef C (.ref (.mapping .uint (.prim .uint)))).index .map value)).bind
      (fun v => some v.view) = some (uintOfNat 0)
  rw [hs]
  rw [Storage.find_init_total _ (by simp only [CloseS.index_append, CloseS.path_append,
    CloseS.path_ofRoot, Path.append_nil, Path.index_map, Path.total])]
  rfl

/-- The zero-valued block has a concrete inhabitant, regardless of guard halting. -/
theorem sourceBlock_initial (sp : PartialOrRoots C) (first second : Var) :
    holds (State.init C) (sp.sourceBlock first second (uintOfNat 0)) := by
  intro i j _hg
  exact (holds_eq_of_eval (x := uintOfNat 0) (y := uintOfNat 0)
    (sp.mapRead_initial _ rfl _ i rfl) (by rfl)).mpr rfl

/-- An initialized mapping refutes every nonzero result, including at key zero. -/
theorem sourceClaim_initial_refutes (sp : PartialOrRoots C) (first second : Var)
    (key result : PrimTy.uint.Denote) (hr : uintOfNat 0 ≠ result) :
    ¬ holds (State.init C) (sp.sourceClaim first second (uintOfNat 0) key result) := by
  intro h
  have hc : holds (State.init C)
      (.eq (sp.mapRead (.app0 (.lit key))) (.app0 (.lit result))) :=
    h (sp.sourceBlock_initial first second)
  exact hr ((holds_eq_of_eval (x := uintOfNat 0) (y := result)
    (sp.mapRead_initial _ rfl _ key rfl) (by rfl)).mp hc)

end PartialOrRoots

/-- Transport the exact source equation; the result literal must match the block. -/
theorem PartialOrBlockAt.valid_positive {C : Contract} {sp : PartialOrRoots C}
    {value key : PrimTy.uint.Denote} {φ : Fml C []}
    (w : PartialOrBlockAt sp value key value φ) (hk : 0 < key.1) : Fml.Valid φ := by
  rw [w.equation]
  exact sp.sourceClaim_positive_valid w.first w.second value key hk

/-- The hash-free source family needs no hash-model assumption. -/
theorem PartialOrBlockAt.validH_positive {C : Contract} {sp : PartialOrRoots C}
    {value key : PrimTy.uint.Denote} {φ : Fml C []}
    (w : PartialOrBlockAt sp value key value φ) (hk : 0 < key.1) : Fml.ValidH φ :=
  fun σ => (Fml.holdsH_iff σ φ w.hashFree).mpr (w.valid_positive hk σ)


/-- Transport the concrete initialized-state countermodel along the full source equation. -/
theorem PartialOrBlockAt.initial_refutes {C : Contract} {sp : PartialOrRoots C}
    {key result : PrimTy.uint.Denote} {φ : Fml C []}
    (w : PartialOrBlockAt sp (uintOfNat 0) key result φ)
    (hr : uintOfNat 0 ≠ result) : ¬ holds (State.init C) φ := by
  rw [w.equation]
  exact sp.sourceClaim_initial_refutes w.first w.second key result hr

/-- The same concrete countermodel uses the unchanged hash-free observation. -/
theorem PartialOrBlockAt.initial_refutesH {C : Contract} {sp : PartialOrRoots C}
    {key result : PrimTy.uint.Denote} {φ : Fml C []}
    (w : PartialOrBlockAt sp (uintOfNat 0) key result φ)
    (hr : uintOfNat 0 ≠ result) : ¬ Fml.holdsH (State.init C) φ :=
  fun h => w.initial_refutes hr ((Fml.holdsH_iff (State.init C) φ w.hashFree).mp h)

end Solidity.Decide.ResidueReason
