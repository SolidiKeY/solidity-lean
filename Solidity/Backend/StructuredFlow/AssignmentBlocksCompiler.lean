import Solidity.Lowering.G19.AssignmentBlocks
import Solidity.Evm.Correct

/-! Actual compiler of ordered Boolean-copy blocks; admission remains the
whole fragment check and native representation/capacity, not syntax alone. -/
namespace Solidity.Backend.StructuredFlow.AssignmentBlocksCompiler
open Solidity.Lowering.V07 Solidity.Lowering.G19
open AssignmentBlocks (statement code sourceAfter targetAfter)

def emit {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} (base : Nat)
    (index : Source.Idx srcΓ .bool → Idx Γ (.val .bool))
    (steps : List (Source.Idx srcΓ .bool × Source.Idx srcΓ .bool)) : List Evm.Instr :=
  Evm.compileProg base (code (C := C) index steps)

theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M : Bool} {k : Source.SCtx}
    (steps : List (Source.Idx srcΓ .bool × Source.Idx srcΓ .bool))
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (Rel : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (index : Source.Idx srcΓ .bool → Idx Γ (.val .bool))
    (maps : ∀ i, m.slot i = ⟨.val .bool,index i⟩) (aligned : m.Related Rel source.1 target.env)
    {L base : Nat} {frame outFrame : Evm.Frag Γ} {machine : Evm.Machine}
    (entry : Evm.Sim C L base frame target machine)
    (checked : Evm.inFragP frame (code (C := C) index steps) = some outFrame)
    (capacity : L + Evm.Prog.pushes (code (C := C) index steps) ≤ Evm.Lmax) :
    (Source.execS G F (fuel+steps.length+4) nps ph (R := returns) (M := M) (k := k)
      (statement steps) source.1).run (.nil,source.2) =
      (.ok (Source.Out.normal (sourceAfter steps source.1)),(.nil,source.2)) ∧
    (code index steps).run target = .ok ⟨targetAfter index steps target,List.prefix_refl _⟩ ∧
    m.Related Rel (sourceAfter steps source.1) (targetAfter index steps target).env ∧
    (targetAfter index steps target).glob = target.glob ∧
    Evm.StmtOut C (L + Evm.Prog.pushes (code (C := C) index steps)) base outFrame
      (Evm.Prog.shrinks (code (C := C) index steps)) (Evm.Prog.pays (code (C := C) index steps))
      (Solidity.Prog.asserts (code (C := C) index steps)) ((code (C := C) index steps).run target)
      (Evm.run (emit (C := C) base index steps) machine) machine := by
  rcases AssignmentBlocks.correct G F fuel nps ph (returns := returns) (M := M) (k := k)
    steps source target m Rel index maps aligned with ⟨src,typed,related,globals⟩
  exact ⟨src,typed,related,globals,Evm.prog_sim _ entry checked capacity⟩

end Solidity.Backend.StructuredFlow.AssignmentBlocksCompiler
