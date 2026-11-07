import Solidity.Lowering.V07.ContextMapWrite
import Solidity.Lowering.V07.Conversions

/-! UDVT local assignment/identity transport for integer underlying types.
No Source wrap/unwrap expression semantics or frontend selection is invented. -/
namespace Solidity.Lowering.V07.UdvtAssignment

def value {D : Source.Layout} (d : Source.DeclName) (t : Source.IntTy)
    (underlying : D.underlying d = .int t) (x : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) :
    Source.Val D (.udvt d) := .udvt (underlying.symm ▸ (.int x hx : Source.Val D (.int t)))

def Rel {D : Source.Layout} (d : Source.DeclName) (t : Source.IntTy)
    (source : Source.Val D (.udvt d)) (target : (integerPrim t).Denote) : Prop :=
  source.key = PrimTy.num? target

theorem key_cast {D : Source.Layout} {σ τ : Source.STy} (h : σ = τ) (v : Source.Val D σ) :
    (h ▸ v).key = v.key := by
  cases h
  rfl

theorem value_key {D : Source.Layout} (d : Source.DeclName) (t : Source.IntTy)
    (underlying : D.underlying d = .int t) (x : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) :
    (value d t underlying x hx).key = some x := by
  change (underlying.symm ▸ (.int x hx : Source.Val D (.int t))).key = some x
  rw [key_cast]
  rfl

theorem value_related {D : Source.Layout} (d : Source.DeclName) (t : Source.IntTy)
    (underlying : D.underlying d = .int t) (x : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) :
    Rel d t (value d t underlying x hx) (integerValue t x hx) := by
  unfold Rel
  rw [value_key,integer_observe]

theorem read_value {D : Source.Layout} (d : Source.DeclName) (t : Source.IntTy)
    (underlying : D.underlying d = .int t) (x : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (v : (integerPrim t).Denote) (related : Rel d t (value d t underlying x hx) v) :
    v = integerValue t x hx := by
  unfold Rel at related
  rw [value_key] at related
  obtain ⟨sign,bits,valid⟩ := t
  cases sign
  all_goals
    apply Subtype.ext
    exact (Option.some.inj related).symm

theorem nominal_implicit (E : Source.Env) (d e : Source.DeclName) :
    (Source.STy.udvt d).implicit E.isBase E.mapFree (.udvt e) = (d == e) := rfl

theorem nominal_refused {D : Source.Layout} (d e : Source.DeclName) (different : d ≠ e)
    (v : Source.Val D (.udvt d)) :
    Source.convVal (.udvt e) v = .error (.stuck "user-defined value type") := by
  change (if h : d = e then pure (h ▸ v) else Source.stuck "user-defined value type") = _
  rw [dif_neg different]
  rfl

theorem source_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source mid : Source.EMState E Γ) (d : Source.DeclName)
    (expr : Source.RExpr E Γ (.udvt d)) (v : Source.Val E.layout (.udvt d))
    (read : (Source.evalE G F fuel expr).run source = (.ok (.val v),mid)) :
    (Source.evalE G F (fuel+1) (.conv expr (Or.inr rfl))).run source = (.ok (.val v),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  change (Source.convRV F fuel (.udvt d) (.val v)).run mid = _
  change (if h : (Source.STy.udvt d) = .udvt d then
    (pure (h ▸ (Source.RVal.val v)) : Source.EM E Γ (Source.RVal E.layout (.udvt d))) else _).run mid = _
  rw [dif_pos rfl]
  rfl

theorem source_assignment {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source : Source.EMState E Γ) (d : Source.DeclName)
    (i r : Source.Idx Γ (.udvt d)) (v : Source.Val E.layout (.udvt d)) (read : source.1.get r = v) :
    (Source.evalE G F (fuel+3) (.conv (.assign (.local i) (.local r)) (Or.inr rfl))).run source =
      (.ok (.val v),(source.1.set i v,source.2)) :=
  source_run G F (fuel+2) source _ d _ v (source_assign_local_run G F fuel source i r v read)

theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (t : Source.IntTy) (underlying : E.layout.underlying d = .int t)
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.udvt d)) (n : (integerPrim t).Denote),
      R (.udvt d) (.val (integerPrim t)) v n → Rel d t v n)
    (i r : Source.Idx srcΓ (.udvt d)) (j k : Idx Γ (.val (integerPrim t)))
    (writeMap : m.slot i = ⟨.val (integerPrim t),j⟩) (readMap : m.slot r = ⟨.val (integerPrim t),k⟩)
    (x : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (read : source.1.get r = value d t underlying x hx) :
    (Source.evalE G F (fuel+3) (.conv (.assign (.local i) (.local r)) (Or.inr rfl))).run source =
      (.ok (.val (value d t underlying x hx)),(source.1.set i (value d t underlying x hx),source.2)) ∧
    (assignLocalOperand j k).run target =
      .ok (⟨target.setLocal j (integerValue t x hx),List.prefix_refl _⟩,.prim (integerValue t x hx)) ∧
    Rel d t (value d t underlying x hx) (integerValue t x hx) ∧
    m.Related R (source.1.set i (value d t underlying x hx)) (TEnv.set j (integerValue t x hx) target.env) := by
  have point := reflect _ _ (ContextMap.value_at m R source.1 target.env aligned r k readMap)
  rw [read] at point
  have targetRead := read_value d t underlying x hx _ point
  have post : m.Related R (source.1.set i (source.1.get r))
      (TEnv.set j (TEnv.get k target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i r j k writeMap readMap
  rw [read,targetRead] at post
  exact ⟨source_assignment G F fuel source d i r _ read,
    assign_local_operand_run target j k _ targetRead,value_related d t underlying x hx,post⟩

/-- info: 'Solidity.Lowering.V07.UdvtAssignment.key_cast' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignment.key_cast

/-- info: 'Solidity.Lowering.V07.UdvtAssignment.value_key' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignment.value_key

/-- info: 'Solidity.Lowering.V07.UdvtAssignment.value_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignment.value_related

/-- info: 'Solidity.Lowering.V07.UdvtAssignment.read_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignment.read_value

/-- info: 'Solidity.Lowering.V07.UdvtAssignment.nominal_implicit' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignment.nominal_implicit

/-- info: 'Solidity.Lowering.V07.UdvtAssignment.nominal_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignment.nominal_refused

/-- info: 'Solidity.Lowering.V07.UdvtAssignment.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignment.source_run

/-- info: 'Solidity.Lowering.V07.UdvtAssignment.source_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignment.source_assignment

/-- info: 'Solidity.Lowering.V07.UdvtAssignment.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAssignment.transport

end Solidity.Lowering.V07.UdvtAssignment
