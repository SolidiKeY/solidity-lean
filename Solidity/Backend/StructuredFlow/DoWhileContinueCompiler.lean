import Solidity.Backend.StructuredFlow.ForBreakCompiler
import Solidity.Lowering.G19.AssignmentDoWhileContinue

/-! Physical consumption of the existing mapped do-while assignment/continue
certificate. Continue skips an arbitrary body suffix, then literal false exits.
The shared scoped assignment compiler and exact exit frame are reused. -/
namespace Solidity.Backend.StructuredFlow.DoWhileContinueCompiler
open Solidity.Lowering.V07 Solidity.Lowering.G19
open AssignmentReturnFlag (boolSlot)
open AssignmentWhileBreak (code reached)
open ForBreakCompiler (emit exitFrame admitted)

theorem correct {E : Source.Env} {srcΓ tailΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M l u : Bool}
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (v : LTy) → Source.Val E.layout τ → v.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      R .bool (.val .bool) v b → v = .bool b)
    (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (map_i : m.slot i = ⟨.val .bool,boolSlot m i hi⟩)
    (map_a : m.slot a = ⟨.val .bool,boolSlot m a ha⟩)
    (tail : Source.RItems E returns M ⟨true,u⟩ srcΓ tailΓ)
    {L base : Nat} {frame : Evm.Frag Γ} {machine : Evm.Machine}
    (entry : Evm.Sim C L base frame target machine) :
    (Source.execS G F (fuel+6) nps ph (R := returns) (M := M)
      (.doWhile (l := l) (u := u) (AssignmentDoWhileContinue.body i a tail) (.bool false)) source.1).run (.nil,source.2) =
      (.ok (Source.Out.normal (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))),
        (.nil,source.2)) ∧
    (code m i a hi ha : Prog C Γ Γ).run target =
      .ok ⟨reached m i a hi ha target,List.prefix_refl _⟩ ∧
    m.Related R (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))
      (reached m i a hi ha target).env ∧
    (reached m i a hi ha target).glob = target.glob ∧
    Evm.StmtOut C L base (exitFrame frame) false false false
      ((code m i a hi ha : Prog C Γ Γ).run target)
      (Evm.run (emit (C := C) base m i a hi ha) machine) machine ∧
    Evm.run (emit (C := C) base m i a hi ha) machine =
      .ok (MappedCondition.after base m i a hi ha machine) 0 := by
  rcases AssignmentDoWhileContinue.correct G F fuel nps ph (returns := returns) (M := M) (l := l) (u := u)
    source target m R aligned boolReflect i a hi ha map_i map_a tail with
    ⟨src,typed,related,globals⟩
  exact ⟨src,typed,related,globals,Evm.prog_sim _ entry (admitted frame m i a hi ha) entry.bound,
    MappedCondition.run_exact base m i a hi ha machine⟩


end Solidity.Backend.StructuredFlow.DoWhileContinueCompiler
