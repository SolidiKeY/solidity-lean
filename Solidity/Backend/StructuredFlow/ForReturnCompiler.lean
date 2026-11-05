import Solidity.Lowering.G19.AssignmentForReturn
import Solidity.Backend.StructuredFlow.MappedCondition

/-! Actual compiler connection for the mapped for-loop's captured return flag.
This prefix does not execute an EVM RETURN or dispatch a function exit. -/
namespace Solidity.Backend.StructuredFlow.ForReturnCompiler
open Solidity.Lowering.V07 Solidity.Lowering.G19
open AssignmentReturnFlag

def emit {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} (base : Nat)
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) : List Evm.Instr :=
  Evm.compileProg base (code (C := C) m i a hi ha)

theorem code_exact {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} (base : Nat)
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) :
    emit (C := C) base m i a hi ha = MappedCondition.emit base m i a hi ha := by rfl

theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat)
    (ph : Option (Source.Ph E)) {M l u : Bool}
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      R .bool (.val .bool) v b → v = .bool b)
    (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (map_i : m.slot i = ⟨.val .bool,boolSlot m i hi⟩)
    (map_a : m.slot a = ⟨.val .bool,boolSlot m a ha⟩)
    (post : Source.ROptExpr E srcΓ)
    {L base : Nat} {frame : Evm.Frag Γ} {machine : Evm.Machine}
    (entry : Evm.Sim C L base frame target machine) :
    (Source.execS G F (fuel+4) nps ph (M := M)
      (AssignmentForReturn.statement (l := l) (u := u) i a post) source.1).run (.nil,source.2) =
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
    (reached m i a hi ha target).glob = target.glob ∧
    Evm.StmtOut C L base (frame.push (.val .bool) .ok) false false false
      ((code m i a hi ha : Prog C Γ (.val .bool :: Γ)).run target)
      (Evm.run (emit (C := C) base m i a hi ha) machine) machine ∧
    Evm.run (emit (C := C) base m i a hi ha) machine =
      .ok (MappedCondition.after base m i a hi ha machine) 0 := by
  rcases AssignmentForReturn.correct G F fuel nps ph source target m R aligned
    boolReflect i a hi ha map_i map_a post with ⟨src,typed,related,flag,globals⟩
  exact ⟨src,typed,related,flag,globals,MappedCondition.correct m i a hi ha entry,
    MappedCondition.run_exact base m i a hi ha machine⟩

end Solidity.Backend.StructuredFlow.ForReturnCompiler
