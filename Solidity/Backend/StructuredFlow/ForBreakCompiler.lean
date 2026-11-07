import Solidity.Lowering.G19.AssignmentForBreak
import Solidity.Backend.StructuredFlow.MappedCondition

/-! The mapped for initializer executes once, break skips the arbitrary post,
and the scoped prefix drops its typed capture. No new compiler arm/semantics. -/
namespace Solidity.Backend.StructuredFlow.ForBreakCompiler
open Solidity.Lowering.V07 Solidity.Lowering.G19
open AssignmentReturnFlag (boolSlot)
open AssignmentWhileBreak (code reached)

def emit {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} (base : Nat)
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) : List Evm.Instr :=
  Evm.compileProg base (code (C := C) m i a hi ha)

theorem code_exact {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} (base : Nat)
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) :
    emit (C := C) base m i a hi ha = MappedCondition.emit base m i a hi ha := by rfl

def exitFrame {Γ : Ctx} (frame : Evm.Frag Γ) : Evm.Frag Γ :=
  (frame.push (.val .bool) .ok).restrict Γ

theorem admitted {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} (frame : Evm.Frag Γ)
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) :
    Evm.inFragP frame (code (C := C) m i a hi ha) = some (exitFrame frame) := by rfl

theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
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
    (post : Source.ROptExpr E srcΓ)
    {L base : Nat} {frame : Evm.Frag Γ} {machine : Evm.Machine}
    (entry : Evm.Sim C L base frame target machine) :
    (Source.execS G F (fuel+4) nps ph (R := returns) (M := M)
      (AssignmentForBreak.statement (l := l) (u := u) i a post) source.1).run (.nil,source.2) =
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
  rcases AssignmentForBreak.correct G F fuel nps ph (returns := returns) (M := M) (l := l) (u := u)
    source target m R aligned boolReflect i a hi ha map_i map_a post with
    ⟨src,typed,related,globals⟩
  exact ⟨src,typed,related,globals,Evm.prog_sim _ entry (admitted frame m i a hi ha) entry.bound,
    MappedCondition.run_exact base m i a hi ha machine⟩

end Solidity.Backend.StructuredFlow.ForBreakCompiler
