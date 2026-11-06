import Solidity.Backend.StructuredFlow.MappedBranch

/-! Drop the mapped branch's private capture in the existing intrinsic
block, then compile a continuation in the reached caller context. -/
namespace Solidity.Backend.StructuredFlow.ScopedMappedSequence
open Solidity.Evm Solidity.Lowering.V07

def program {srcΓ : Source.RCtx} {C : Contract} {Γ Γ₁ Γ₂ Γ₃ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (left : Prog C (.val .bool :: Γ) Γ₁) (right : Prog C (.val .bool :: Γ) Γ₂)
    (tail : Prog C Γ Γ₃) : Prog C Γ Γ₃ :=
  .cons (.block (MappedBranch.program m i a hi ha left right)) tail

def emit {srcΓ : Source.RCtx} {C : Contract} {Γ Γ₁ Γ₂ Γ₃ : Ctx}
    (base : Nat) (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (left : Prog C (.val .bool :: Γ) Γ₁) (right : Prog C (.val .bool :: Γ) Γ₂)
    (tail : Prog C Γ Γ₃) : List Instr :=
  MappedBranch.emit base m i a hi ha (compileProg base left) (compileProg base right) ++ compileProg base tail

theorem code_exact {srcΓ : Source.RCtx} {C : Contract} {Γ Γ₁ Γ₂ Γ₃ : Ctx}
    (base : Nat) (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (left : Prog C (.val .bool :: Γ) Γ₁) (right : Prog C (.val .bool :: Γ) Γ₂)
    (tail : Prog C Γ Γ₃) :
    emit base m i a hi ha left right tail = compileProg base (program m i a hi ha left right tail) := by
  simp only [emit,program,MappedBranch.code_exact,compileProg,compileStmt]

theorem run_composed {srcΓ : Source.RCtx} {C : Contract} {Γ Γ₁ Γ₂ Γ₃ : Ctx}
    (base : Nat) (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (left : Prog C (.val .bool :: Γ) Γ₁) (right : Prog C (.val .bool :: Γ) Γ₂)
    (tail : Prog C Γ Γ₃) (machine : Machine) :
    run (emit base m i a hi ha left right tail) machine =
      (run (MappedBranch.emit base m i a hi ha (compileProg base left) (compileProg base right)) machine).bind
        (fun next skip => exec (compileProg base tail) skip next) := by
  simp only [emit,run,exec_append]

theorem admitted {srcΓ : Source.RCtx} {C : Contract} {Γ Γ₁ Γ₂ Γ₃ : Ctx}
    (F : Frag Γ) (F₁ : Frag Γ₁) (F₂ : Frag Γ₂) (F₃ : Frag Γ₃)
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (left : Prog C (.val .bool :: Γ) Γ₁) (right : Prog C (.val .bool :: Γ) Γ₂)
    (tail : Prog C Γ Γ₃)
    (hl : inFragP (F.push (.val .bool) .ok) left = some F₁)
    (hr : inFragP (F.push (.val .bool) .ok) right = some F₂)
    (ht : inFragP (((F₁.restrict (.val .bool :: Γ)).meet
      (F₂.restrict (.val .bool :: Γ))).restrict Γ) tail = some F₃) :
    inFragP F (program m i a hi ha left right tail) = some F₃ := by
  change (match (inFragP F (MappedBranch.program m i a hi ha left right)).map (Frag.restrict Γ) with
    | some next => inFragP next tail
    | none => none) = _
  rw [MappedBranch.admitted F F₁ F₂ m i a hi ha left right hl hr]
  exact ht

theorem correct {srcΓ : Source.RCtx} {C : Contract} {Γ Γ₁ Γ₂ Γ₃ : Ctx}
    {L base : Nat} {F : Frag Γ} {F₁ : Frag Γ₁} {F₂ : Frag Γ₂} {F₃ : Frag Γ₃}
    {caller : State C Γ} {machine : Machine}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (left : Prog C (.val .bool :: Γ) Γ₁) (right : Prog C (.val .bool :: Γ) Γ₂)
    (tail : Prog C Γ Γ₃) (entry : Sim C L base F caller machine)
    (hl : inFragP (F.push (.val .bool) .ok) left = some F₁)
    (hr : inFragP (F.push (.val .bool) .ok) right = some F₂)
    (ht : inFragP (((F₁.restrict (.val .bool :: Γ)).meet
      (F₂.restrict (.val .bool :: Γ))).restrict Γ) tail = some F₃)
    (capacity : L + Prog.pushes (program m i a hi ha left right tail) ≤ Lmax) :
    StmtOut C (L + Prog.pushes (program m i a hi ha left right tail)) base F₃
      (Prog.shrinks (program m i a hi ha left right tail))
      (Prog.pays (program m i a hi ha left right tail))
      (Prog.asserts (program m i a hi ha left right tail))
      ((program m i a hi ha left right tail).run caller)
      (run (emit base m i a hi ha left right tail) machine) machine := by
  rw [code_exact]
  exact prog_sim _ entry (admitted F F₁ F₂ F₃ m i a hi ha left right tail hl hr ht) capacity

end Solidity.Backend.StructuredFlow.ScopedMappedSequence
