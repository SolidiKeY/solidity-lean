import Solidity.Lowering.G19.AssignmentWhileContinue
import Solidity.Evm.Correct

/-! Existing mapped continue/retest lowering connected to the actual loop
compiler and its checked-fragment contract. -/
namespace Solidity.Backend.StructuredFlow.WhileContinueCompiler
open Solidity.Lowering.V07 Solidity.Lowering.G19
open AssignmentReturnFlag (boolSlot)

def emit {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} (base : Nat)
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) : List Evm.Instr :=
  Evm.compileProg base (AssignmentWhileReset.code (C := C) m i a hi ha)

theorem emit_split : ∀ {srcΓ : Solidity.Source.RCtx} {C : Solidity.Contract} {Γ : Solidity.Ctx} (base : Nat)
  (m : Solidity.Lowering.V07.ContextMap srcΓ Γ) (i a : Solidity.Source.Idx srcΓ .bool)
  (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool),
  Solidity.Backend.StructuredFlow.WhileContinueCompiler.emit (C := C) base m i a hi ha =
    Solidity.Evm.compileProg (C := C) base (Solidity.Lowering.G19.AssignmentWhileBreak.code m i a hi ha) ++
      [.loop (Solidity.Evm.compileVal (C := C) base (.simple (.local (Solidity.Lowering.G19.AssignmentReturnFlag.boolSlot m i hi))))
        (Solidity.Evm.compileProg (C := C) base (Solidity.Lowering.G19.AssignmentWhileReset.body m i a hi ha))] := by
  intros
  rfl

theorem correct {E : Source.Env} {srcΓ tailΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M l u : Bool}
    (s : Source.EMState E srcΓ) (t : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (v : LTy) → Source.Val E.layout τ → v.TDenote C t.H → Prop)
    (aligned : m.Related R s.1 t.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool), R .bool (.val .bool) v b → v = .bool b)
    (falseValue : R .bool (.val .bool) (.bool false) false)
    (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (mapI : m.slot i = ⟨.val .bool,boolSlot m i hi⟩)
    (mapA : m.slot a = ⟨.val .bool,boolSlot m a ha⟩)
    (tail : Source.RItems E returns M ⟨true,u⟩ srcΓ tailΓ)
    {L base : Nat} {frame0 frame1 : Evm.Frag Γ} {machine : Evm.Machine}
    (entry : Evm.Sim C L base frame0 t machine)
    (checked : Evm.inFragP frame0 (AssignmentWhileReset.code (C := C) m i a hi ha) = some frame1)
    (capacity : L + Evm.Prog.pushes (AssignmentWhileReset.code (C := C) m i a hi ha) ≤ Evm.Lmax) :
    let choice : Bool := TEnv.get (boolSlot m a ha) t.env
    (Source.execS G F (fuel+8) nps ph (R := returns) (M := M)
      (AssignmentWhileContinue.statement (l := l) i a tail) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (AssignmentWhileReset.sourceAfter s.1 i a choice)),(.nil,s.2)) ∧
    (AssignmentWhileReset.code m i a hi ha : Prog C Γ Γ).run t =
      .ok ⟨AssignmentWhileReset.targetAfter m i a hi ha t,List.prefix_refl _⟩ ∧
    m.Related R (AssignmentWhileReset.sourceAfter s.1 i a choice) (AssignmentWhileReset.targetAfter m i a hi ha t).env ∧
    (AssignmentWhileReset.targetAfter m i a hi ha t).glob = t.glob ∧
    Evm.StmtOut C (L + Evm.Prog.pushes (AssignmentWhileReset.code (C := C) m i a hi ha)) base frame1
      (Evm.Prog.shrinks (AssignmentWhileReset.code (C := C) m i a hi ha)) (Evm.Prog.pays (AssignmentWhileReset.code (C := C) m i a hi ha)) (Solidity.Prog.asserts (AssignmentWhileReset.code (C := C) m i a hi ha))
      ((AssignmentWhileReset.code (C := C) m i a hi ha).run t) (Evm.run (emit (C := C) base m i a hi ha) machine) machine := by
  rcases AssignmentWhileContinue.correct G F fuel nps ph (returns := returns) (M := M) (l := l) (u := u)
    s t m R aligned boolReflect falseValue i a hi ha mapI mapA tail with ⟨src,tgt,related,globals⟩
  exact ⟨src,tgt,related,globals,Evm.prog_sim _ entry checked capacity⟩

theorem loop_false {C : Contract} {Γ : Ctx} (body : Prog C Γ Γ) (t : State C Γ) :
    (Stmt.loop .auto (.simple (.bool false)) body).run t = .ok ⟨t,List.prefix_refl _⟩ := by
  exact TLoop.run_of_iterN (n := 1) rfl

theorem false_guard_run {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) (t : State C Γ) :
    (show Prog C Γ Γ from .cons (.block (AssignmentWhileBreak.code m i a hi ha))
      (.cons (.loop .auto (.simple (.bool false)) (AssignmentWhileReset.body m i a hi ha)) .nil)).run t =
      .ok ⟨AssignmentWhileBreak.reached m i a hi ha t,List.prefix_refl _⟩ := by
  rw [Prog.run_cons_ok (AssignmentWhileReset.block_run m i a hi ha t)]
  dsimp only
  rw [Prog.run_cons_ok (loop_false (AssignmentWhileReset.body m i a hi ha)
    (t.setLocal (boolSlot m i hi) (TEnv.get (boolSlot m a ha) t.env))),Prog.run_nil]
  rfl

end Solidity.Backend.StructuredFlow.WhileContinueCompiler
