import Solidity.Lowering.V07.EffectfulCondition
import Solidity.Source.Semantics

/-! G19 client of the existing V07 ContextMap and assignment operand.
Only Boolean local-assignment conditions with a bare-return arm are in scope.
Target positions are derived from the map, not supplied by a caller. No P8a
producer, whole-world relation, general condition or EVM adequacy is assumed. -/
namespace Solidity.Lowering.G19.AssignmentReturnFlag
open Solidity.Lowering.V07

/-- The type equality exposes the existing mapped Boolean slot; no new slot. -/
def boolSlot {srcΓ : Source.RCtx} {Γ : Ctx} (m : ContextMap srcΓ Γ)
    (i : Source.Idx srcΓ .bool) (typed : (m.slot i).1 = .val .bool) : Idx Γ (.val .bool) :=
  Eq.mp (congrArg (fun u => Idx Γ u) typed) (m.slot i).2

/-- Reuse V07's exact prefix. Its fresh captured condition is the control flag
for this one bare-return conditional; no caller binding is used as the flag. -/
def code {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (destination rhs : Source.Idx srcΓ .bool)
    (destinationBool : (m.slot destination).1 = .val .bool)
    (rhsBool : (m.slot rhs).1 = .val .bool) : Prog C Γ (.val .bool :: Γ) :=
  (assignLocalOperand (boolSlot m destination destinationBool) (boolSlot m rhs rhsBool)).code

/-- Concrete reached target, with both indices computed from the same map. -/
def reached {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (destination rhs : Source.Idx srcΓ .bool)
    (destinationBool : (m.slot destination).1 = .val .bool)
    (rhsBool : (m.slot rhs).1 = .val .bool) (target : State C Γ) :
    State C (.val .bool :: Γ) :=
  (target.setLocal (boolSlot m destination destinationBool)
    (TEnv.get (boolSlot m rhs rhsBool) target.env)).push
    (t := .val .bool) (TEnv.get (boolSlot m rhs rhsBool) target.env)

/-- Actual Source statement equation. The fuel offset is derived from its
assignment/if/return equations, not an admitted-source unrolling limit. -/
theorem source_run {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat)
    (ph : Option (Source.Ph E)) {M : Bool} {k : Source.SCtx}
    (ls : Source.Locals E.layout srcΓ) (st : Source.St E)
    (i a : Source.Idx srcΓ .bool) (choice : Bool)
    (read : ls.get a = .bool choice) :
    (Source.execS G F (fuel+3) nps ph (M := M) (k := k)
      (.ifThen (.assign (.local i) (.local a)) (.ret rfl)) ls).run (.nil,st) =
      (.ok (if choice then Source.Out.ret (ls.set i (.bool choice))
        else Source.Out.normal (ls.set i (.bool choice))),(.nil,st)) := by
  have sub : (Source.EM.sub ls (Source.evalE G F (fuel+2)
      (.assign (.local i) (.local a)))).run (.nil,st) =
      (.ok (.val (.bool choice),ls.set i (.bool choice)),(.nil,st)) := by
    have hr : Source.evalE G F (fuel+2) (.assign (.local i) (.local a)) (ls,st) =
        (.ok (.val (.bool choice)),(ls.set i (.bool choice),st)) :=
        source_assign_local_run G F fuel (ls,st) i a (.bool choice) read
    simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,hr]
  rw [Source.execS,Source.Hoare.run_bind,sub]
  cases choice <;> rfl

/-- The same statement still times out at zero resource. -/
theorem source_zero {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (ls : Source.Locals E.layout srcΓ)
    (i a : Source.Idx srcΓ .bool) :
    Source.execS G F 0 nps ph (M := M) (k := k)
      (.ifThen (.assign (.local i) (.local a)) (.ret rfl)) ls =
      Source.EM.halt .timeout := by rfl

/-- Map-guided connection, including the reached heterogeneous-local relation.
The two slot equations are initial typed position facts; the routine universal
boolSlot_spec projection lemma remains assigned to Terra. There are no target
indices, execution or desired preservation premises. -/
theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat)
    (ph : Option (Source.Ph E)) {M : Bool} {k : Source.SCtx}
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      R .bool (.val .bool) v b → v = .bool b)
    (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (map_i : m.slot i = ⟨.val .bool,boolSlot m i hi⟩)
    (map_a : m.slot a = ⟨.val .bool,boolSlot m a ha⟩) :
    (Source.execS G F (fuel+3) nps ph (M := M) (k := k)
      (.ifThen (.assign (.local i) (.local a)) (.ret rfl)) source.1).run (.nil,source.2) =
      (.ok (if (TEnv.get (boolSlot m a ha) target.env : Bool) = true then
        Source.Out.ret (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))
        else Source.Out.normal (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))),
        (.nil,source.2)) ∧
    (code m i a hi ha : Prog C Γ (.val .bool :: Γ)).run target =
      .ok ⟨reached m i a hi ha target,List.prefix_refl _⟩ ∧
    (m.wk (Thin.drop (t := .val .bool) .refl)).Related R
      (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))
      (reached m i a hi ha target).env ∧
    TEnv.get .here (reached m i a hi ha target).env = TEnv.get (boolSlot m a ha) target.env ∧
    (reached m i a hi ha target).glob = target.glob := by
  have reflected : source.1.get a = .bool (TEnv.get (boolSlot m a ha) target.env) :=
    boolReflect _ _ (ContextMap.value_at m R source.1 target.env aligned a _ map_a)
  rcases condition_assignment_transport G F fuel source target m R aligned
    boolReflect i a (boolSlot m i hi) (boolSlot m a ha) map_i map_a with
    ⟨_,targetRun,_,post,globals⟩
  exact ⟨source_run G F fuel nps ph source.1 source.2 i a _ reflected,
    targetRun,post,rfl,globals⟩

end Solidity.Lowering.G19.AssignmentReturnFlag
