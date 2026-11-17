import Solidity.Semantics.IntrinsicStorage.Preimages.Ops

namespace Solidity.Examples.IntrinsicStorage.Preimages.Ops
open Solidity.Semantics Solidity.Semantics.IntrinsicStorage Solidity.Storage

-- A failed actual storage read skips its continuation without losing the audit.
example {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    (e : THalt) (h : TRes.ofOpt (st.find r) = .error e) (f : SVal T → Audit Nat) :
    (Audit.read st r >>= f).result = .error e ∧
    (Audit.read st r >>= f).inputs = (Audit.read st r).inputs := by
  constructor
  · rw [Audit.result_bind, Audit.result_read, h]
    rfl
  · exact Audit.failed_bind _ f ((Audit.result_read st r).trans h)

example {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    {v : SVal T} (hv : st.find r = some v) {p : Pre}
    (hp : ValueInput v (reference r) p) (e : THalt) :
    encoded p ∈ (Audit.follow (Audit.read st r)
      (fun _ => (Audit.lift (.error e) : Audit Nat))).inputs.hashed := by
  apply Inputs.slot_hashed
  exact Audit.follow_slots _ _ (Audit.read_value st r hv hp)

-- Both overwritten and replacement aggregate preimages survive a later operation.
example {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    (v old : SVal T) (hv : st.find r = some old) {p q : Pre}
    (hp : ValueInput old (reference r) p) (hq : ValueInput v (reference r) q)
    (f : Solidity.Storage C → Audit Nat) :
    encoded p ∈ (Audit.write st r v >>= f).inputs.hashed ∧
    encoded q ∈ (Audit.write st r v >>= f).inputs.hashed := by
  constructor
  · exact Inputs.slot_hashed _ (Audit.bind_slots_left _ _ (Audit.write_old st r v hv hp))
  · exact Inputs.slot_hashed _ (Audit.bind_slots_left _ _ (Audit.write_value st r v hq))

-- A successful read followed by a write includes the write destination preimages.
example {C : Contract} {T : Ty} (st : Solidity.Storage C) (src dst : SRef C T)
    {v : SVal T} (hv : st.find src = some v) {p : Pre}
    (hp : ValueInput v (reference dst) p) :
    encoded p ∈ (Audit.read st src >>= fun x => Audit.write st dst x).inputs.hashed := by
  apply Inputs.slot_hashed
  apply Audit.bind_slots_right (x := v)
  · rw [Audit.result_read, hv]
    rfl
  · exact Audit.write_value st dst v hp

-- Memory evaluation and a destination write preserve the complete result, including errors.
example {C : Contract} {Γ : Ctx} (σ : State C Γ) {T : Ty}
    (s : MSrc C Γ T) (dst : SRef C T) :
    (Observe.memorySource σ s >>= fun v =>
      Audit.write σ.storage dst (MVal.copyMToSt σ.heap v)).result =
    (s.mvalT σ >>= fun v => TRes.ofOpt (σ.storage.write dst (MVal.copyMToSt σ.heap v))) := by
  simp only [Audit.result_bind, Observe.memorySource_result, Audit.result_write]

-- Alias-producing push may change storage; the following read uses that returned storage.
example {C : Contract} {Γ : Ctx} (σ : State C Γ) {R : RefTy} (r : ARhs C Γ R) :
    (Observe.aliasRhs σ r >>= fun pair => Audit.read pair.1 pair.2).result =
    (r.evalT σ >>= fun pair => TRes.ofOpt (pair.1.find pair.2)) := by
  simp only [Audit.result_bind, Observe.aliasRhs_result, Audit.result_read]

-- A memory RHS may grow the heap; hashing uses its returned state and reference together.
example {C : Contract} {Γ : Ctx} (σ : State C Γ) {R : RefTy} (r : MRhs C Γ R) :
    (Observe.memoryRhs σ r >>= fun g => Audit.hashing g.st .keccak g.val).result =
    (r.evalT σ >>= fun g => .ok (g.st.heap.hash .keccak g.val)) := by
  simp only [Audit.result_bind, Observe.memoryRhs_result, Audit.result_hashing]

-- Argument prefixes are evaluated before the final expression.
example {C : Contract} {Γ ps : Ctx} (σ : State C Γ) (as : Args C Γ ps)
    (p : PrimTy) (x : Var) (e : Val C Γ p) :
    (Observe.args σ (.snoc as p x e)).result =
    (as.evalT σ >>= fun env => e.evalT σ >>= fun v => .ok (v, env)) := by
  rw [Observe.args_result]
  rfl

-- A failing argument prefix propagates its error.
example {C : Contract} {Γ ps : Ctx} (σ : State C Γ) (as : Args C Γ ps)
    (p : PrimTy) (x : Var) (e : Val C Γ p) (err : THalt)
    (h : as.evalT σ = .error err) :
    (Observe.args σ (.snoc as p x e)).result = .error err := by
  rw [Observe.args_result]
  change (as.evalT σ >>= fun env => e.evalT σ >>= fun v => .ok (v, env)) = .error err
  rw [h]
  rfl

/-- The audited sequence for evaluating a RHS and applying an op-assignment (`l op= e`). -/
noncomputable def storeStep {C : Contract} {Γ : Ctx} {p : PrimTy}
    (op : BinOp) (l : OpLoc C Γ p) (e : Val C Γ p) : Observe.Step C Γ Γ := fun σ => do
  let v ← Observe.value σ e
  Observe.storeOp σ op l v

-- Compare the complete state-changing sequence, without assuming success.
example {C : Contract} {Γ : Ctx} {p : PrimTy} (σ : State C Γ)
    (op : BinOp) (l : OpLoc C Γ p) (e : Val C Γ p) :
    (storeStep op l e σ).result = (e.evalT σ >>= fun v => l.storeT σ op v) := by
  simp only [storeStep, Audit.result_bind, Observe.value_result, Observe.storeOp_result]

-- Increment/decrement preserves both the resulting storage and the expression value.
example {C : Contract} {Γ : Ctx} {p : PrimTy} (σ : State C Γ)
    (op : IncDec) (l : OpLoc C Γ p) :
    (Audit.map (fun out => (out.1.st.storage, out.2)) (Observe.bumpOp σ op l)).result =
    (l.bumpT σ op).map (fun out => (out.1.st.storage, out.2)) := by
  rw [Audit.result_map_direct, Observe.bumpOp_result]

-- A reverted source preserves its error and collected inputs when sequenced.
example {C : Contract} {Γ : Ctx} (σ : State C Γ) {T : Ty} (s : Src C Γ T)
    (e : THalt) (h : s.valueT σ = .error e) (f : SVal T → Audit Nat) :
    (Observe.source σ s >>= f).result = .error e ∧
    (Observe.source σ s >>= f).inputs = (Observe.source σ s).inputs := by
  constructor
  · rw [Audit.result_bind, Observe.source_result, h]
    rfl
  · exact Audit.failed_bind _ f ((Observe.source_result σ s).trans h)

end Solidity.Examples.IntrinsicStorage.Preimages.Ops
