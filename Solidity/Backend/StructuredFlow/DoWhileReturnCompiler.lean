import Solidity.Lowering.G19.AssignmentDoWhileReturn
import Solidity.Evm.Correct

/-! Actual core compiler of the mapped do-while assignment/return shape.
The captured true flag classifies Source return; no EVM RETURN is emitted. -/
namespace Solidity.Backend.StructuredFlow.DoWhileReturnCompiler
open Solidity.Lowering.V07 Solidity.Lowering.G19
open AssignmentReturnFlag (boolSlot)
open AssignmentDoWhileReturn (body code reached)

def emit {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} (base : Nat)
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) : List Evm.Instr :=
  Evm.compileProg base (code (C := C) m i a hi ha)

theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M l u : Bool} (source : Source.EMState E srcΓ) (target : State C Γ)
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (v : LTy) → Source.Val E.layout τ → v.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool),
      R .bool (.val .bool) v b → v = .bool b)
    (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (map_i : m.slot i = ⟨.val .bool,boolSlot m i hi⟩)
    (map_a : m.slot a = ⟨.val .bool,boolSlot m a ha⟩)
    (condition : Source.RExpr E srcΓ .bool)
    {L base : Nat} {frame : Evm.Frag Γ} {outFrame : Evm.Frag (.val .bool :: Γ)}
    {machine : Evm.Machine} (entry : Evm.Sim C L base frame target machine)
    (checked : Evm.inFragP frame (code (C := C) m i a hi ha) = some outFrame)
    (capacity : L + Evm.Prog.pushes (code (C := C) m i a hi ha) ≤ Evm.Lmax) :
    (Source.execS G F (fuel+6) nps ph (M := M)
      (.doWhile (l := l) (u := u) (body i a) condition) source.1).run (.nil,source.2) =
      (.ok (Source.Out.ret (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))),
        (.nil,source.2)) ∧
    (code m i a hi ha : Prog C Γ (.val .bool :: Γ)).run target =
      .ok ⟨reached m i a hi ha target,List.prefix_refl _⟩ ∧
    (m.wk (Thin.drop (t := .val .bool) .refl)).Related R
      (source.1.set i (.bool (TEnv.get (boolSlot m a ha) target.env)))
      (reached m i a hi ha target).env ∧
    TEnv.get .here (reached m i a hi ha target).env = true ∧
    (reached m i a hi ha target).glob = target.glob ∧
    Evm.StmtOut C (L + Evm.Prog.pushes (code (C := C) m i a hi ha)) base outFrame
      (Evm.Prog.shrinks (code (C := C) m i a hi ha))
      (Evm.Prog.pays (code (C := C) m i a hi ha))
      (Solidity.Prog.asserts (code (C := C) m i a hi ha))
      ((code (C := C) m i a hi ha).run target)
      (Evm.run (emit (C := C) base m i a hi ha) machine) machine := by
  rcases AssignmentDoWhileReturn.correct G F fuel nps ph (M := M) (l := l) (u := u)
    source target m R aligned boolReflect i a hi ha map_i map_a condition with
    ⟨src,typed,related,flag,globals⟩
  exact ⟨src,typed,related,flag,globals,Evm.prog_sim _ entry checked capacity⟩

end Solidity.Backend.StructuredFlow.DoWhileReturnCompiler
