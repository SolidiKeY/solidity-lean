import Solidity.Lowering.V07.SignedNegation

/-! Unchecked signed negation of a local assignment. The actual assignment
precedes negation; a fresh typed local captures the negated expression result.
The caller retains the assigned value, not the negated result. This is an
operational expression clause, not a production frontend or admission proof. -/
namespace Solidity.Lowering.V07.SignedNegationEffects
open SignedWidthCasts (ty)
open SignedNegation (negValue)

def code {C : Contract} {Γ : Ctx} (bits : Nat) (i a : Idx Γ (.val .int)) :
    Prog C Γ (.val .int :: Γ) :=
  .cons (.assignLocal i (.simple (.local a)))
    (.cons (.declLocal .int (.user "v07_negated")
      (some (negValue bits (.simple (.local i))))) .nil)

/-- Operand.run reads the fresh result before dropping its private binder. -/
def operand {C : Contract} {Γ : Ctx} (bits : Nat) (i a : Idx Γ (.val .int)) :
    DeferredSource.Operand C Γ (.prim .int) :=
  ⟨.val .int :: Γ,code bits i a,.val (.simple (.local .here))⟩

theorem source_assignment_run (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E Γ) (i a : Source.Idx Γ (.int (ty bits valid)))
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : source.1.get a = .int x hx) :
    (Source.evalE G {F with checked := false} (fuel+3)
      (.unary .neg (.assign (.local i) (.local a)))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (-x))),
        (source.1.set i (.int x hx),source.2)) := by
  exact SignedNegation.source_of_run bits valid G F (fuel+2) source
    (source.1.set i (.int x hx),source.2) (.assign (.local i) (.local a)) x hx
    (source_assign_local_run G {F with checked := false} fuel source i a (.int x hx) read)

theorem code_run (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (i a : Idx Γ (.val .int))
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : TEnv.get a target.env = integerValue (ty bits valid) x hx) :
    (code bits i a).run target =
      .ok (⟨(target.setLocal i (integerValue (ty bits valid) x hx)).push (t := .val .int)
        (integerValue (ty bits valid) ((ty bits valid).wrap (-x))
          ((ty bits valid).wrap_mem (-x))),List.prefix_refl _⟩ :
        Out C target.H (.val .int :: Γ)) := by
  have assigned : (Stmt.assignLocal i (.simple (.local a))).run target =
      .ok (⟨target.setLocal i (integerValue (ty bits valid) x hx),List.prefix_refl _⟩) := by
    change Except.ok (⟨target.setLocal i (TEnv.get a target.env),List.prefix_refl _⟩ :
      Out C target.H Γ) = _
    rw [read]
  have negated := SignedNegation.value_run bits valid
    (target.setLocal i (integerValue (ty bits valid) x hx)) (.simple (.local i)) x hx
    (congrArg Except.ok (TEnv.get_set i (integerValue (ty bits valid) x hx) target.env))
  have captured : (Stmt.declLocal .int (.user "v07_negated")
      (some (negValue bits (.simple (.local i))))).run
      (target.setLocal i (integerValue (ty bits valid) x hx)) =
      .ok (⟨(target.setLocal i (integerValue (ty bits valid) x hx)).push (t := .val .int)
        (integerValue (ty bits valid) ((ty bits valid).wrap (-x))
          ((ty bits valid).wrap_mem (-x))),List.prefix_refl _⟩) := by
    change (do
      let value ← (negValue bits (.simple (.local i))).evalT
        (target.setLocal i (integerValue (ty bits valid) x hx))
      pure (⟨(target.setLocal i (integerValue (ty bits valid) x hx)).push (t := .val .int) value,
        List.prefix_refl _⟩ : Out C target.H (.val .int :: Γ))) = _
    rw [negated]
    rfl
  unfold code
  rw [Prog.run_cons_ok assigned,Prog.run_cons_ok captured,Prog.run_nil]
  rfl

/-- Initial alignment supplies the target read and every selected postbinding.
No desired execution, output agreement or post-family is supplied as a premise. -/
theorem assignment_transport (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (i a : ι) (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : source.1.get (si a) = .int x hx) :
    (Source.evalE G {F with checked := false} (fuel+3)
      (.unary .neg (.assign (.local (si i)) (.local (si a))))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (-x))),
        (source.1.set (si i) (.int x hx),source.2)) ∧
    (operand bits (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue (ty bits valid) x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap (-x))
          ((ty bits valid).wrap_mem (-x)))) ∧
    IntValueRel (ty bits valid)
      (Source.intWrap (ty bits valid) (-x) : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap (-x))
        ((ty bits valid).wrap_mem (-x))) ∧
    IntegerLocalFamily (ty bits valid) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty bits valid) x hx) target.env) := by
  refine ⟨source_assignment_run bits valid G F fuel source (si i) (si a) x hx read,
    ?_,integer_related _ _ _,?_⟩
  · unfold operand DeferredSource.Operand.run
    rw [code_run bits valid target (ti i) (ti a) x hx (family.read a x hx read)]
    rfl
  · have post := family.write i a
    rw [read,family.read a x hx read] at post
    exact post

end Solidity.Lowering.V07.SignedNegationEffects

/-- info: 'Solidity.Lowering.V07.SignedNegationEffects.source_assignment_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffects.source_assignment_run

/-- info: 'Solidity.Lowering.V07.SignedNegationEffects.code_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffects.code_run

/-- info: 'Solidity.Lowering.V07.SignedNegationEffects.assignment_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffects.assignment_transport
