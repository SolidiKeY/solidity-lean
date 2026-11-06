import Solidity.Backend.StructuredFlow.MappedCondition
import Solidity.Backend.StructuredFlow.BranchSelector

/-! Branch code over the actual V07-mapped effectful condition. The fresh
capture is loaded after both condition writes; escaping arm skips stay exact. -/
namespace Solidity.Backend.StructuredFlow.MappedBranch
open Solidity.Evm Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag

def condition {srcΓ : Source.RCtx} {Γ : Ctx} (b : Nat) (m : ContextMap srcΓ Γ)
    (i a : Source.Idx srcΓ .bool) (hi : (m.slot i).1 = .val .bool)
    (ha : (m.slot a).1 = .val .bool) : List Instr :=
  MappedCondition.emit b m i a hi ha ++ [.mload (cell (b + Γ.length))]

def emit {srcΓ : Source.RCtx} {Γ : Ctx} (b : Nat) (m : ContextMap srcΓ Γ)
    (i a : Source.Idx srcΓ .bool) (hi : (m.slot i).1 = .val .bool)
    (ha : (m.slot a).1 = .val .bool) (left right : List Instr) : List Instr :=
  Branch.emit (condition b m i a hi ha) left right

def program {srcΓ : Source.RCtx} {C : Contract} {Γ Γ₁ Γ₂ : Ctx}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (left : Prog C (.val .bool :: Γ) Γ₁) (right : Prog C (.val .bool :: Γ) Γ₂) :
    Prog C Γ (.val .bool :: Γ) :=
  (code m i a hi ha).join (.cons (.ite (.simple (.local .here)) left right) .nil)

theorem code_exact {srcΓ : Source.RCtx} {C : Contract} {Γ Γ₁ Γ₂ : Ctx}
    (b : Nat) (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (left : Prog C (.val .bool :: Γ) Γ₁) (right : Prog C (.val .bool :: Γ) Γ₂) :
    emit b m i a hi ha (compileProg b left) (compileProg b right) =
      compileProg b (program m i a hi ha left right) := by
  simp only [emit,condition,program,MappedCondition.emit,code,assignLocalOperand,
    Prog.join,compileProg,compileStmt,compileVal,compileSimple,Branch.emit,List.append_assoc,List.append_nil,List.cons_append,List.nil_append,cellOf,lvl,Idx.toNat,List.length_cons,Nat.sub_zero]
  rfl

theorem condition_run {srcΓ : Source.RCtx} {Γ : Ctx}
    (b : Nat) (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) (machine : Machine) :
    run (condition b m i a hi ha) machine =
      .ok ((MappedCondition.after b m i a hi ha machine).push
        (machine.mem (cellOf b (boolSlot m a ha)))) 0 := by
  rw [condition,run_append_ok (MappedCondition.run_exact b m i a hi ha machine)]
  change Solidity.Evm.Out.ok ((MappedCondition.after b m i a hi ha machine).push
    ((MappedCondition.after b m i a hi ha machine).mem (cell (b + Γ.length)))) 0 = _
  simp only [MappedCondition.after,upd_same]

theorem condition_represented {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    {L b : Nat} {F : Frag Γ} {caller : State C Γ} {machine : Machine}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (entry : Sim C L b F caller machine) :
    run (condition b m i a hi ha) machine =
      .ok ((MappedCondition.after b m i a hi ha machine).push
        (.val (bword (TEnv.get (boolSlot m a ha) caller.env)))) 0 := by
  have value : machine.mem (cellOf b (boolSlot m a ha)) =
      .val (bword (TEnv.get (boolSlot m a ha) caller.env)) := entry.vals (boolSlot m a ha)
  rw [condition_run,value]

theorem true_run {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    {L b : Nat} {F : Frag Γ} {caller : State C Γ} {machine : Machine}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (entry : Sim C L b F caller machine)
    (read : TEnv.get (boolSlot m a ha) caller.env = true) (left right : List Instr) :
    run (emit b m i a hi ha left right) machine =
      (run left (MappedCondition.after b m i a hi ha machine)).bind
        (fun next skip => exec ([.jump right.length] ++ right) skip next) := by
  unfold emit
  apply Branch.true_run
  simpa only [read] using condition_represented m i a hi ha entry

theorem true_pending_skip {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    {L b : Nat} {F : Frag Γ} {caller : State C Γ} {machine final : Machine} {skip : Nat}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (entry : Sim C L b F caller machine)
    (read : TEnv.get (boolSlot m a ha) caller.env = true) (left right : List Instr)
    (body : run left (MappedCondition.after b m i a hi ha machine) = .ok final (skip+1)) :
    run (emit b m i a hi ha left right) machine = exec right skip final := by
  rw [true_run m i a hi ha entry read,body]
  rfl

theorem admitted {srcΓ : Source.RCtx} {C : Contract} {Γ Γ₁ Γ₂ : Ctx}
    (F : Frag Γ) (F₁ : Frag Γ₁) (F₂ : Frag Γ₂)
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (left : Prog C (.val .bool :: Γ) Γ₁) (right : Prog C (.val .bool :: Γ) Γ₂)
    (hl : inFragP (F.push (.val .bool) .ok) left = some F₁)
    (hr : inFragP (F.push (.val .bool) .ok) right = some F₂) :
    inFragP F (program m i a hi ha left right) =
      some ((F₁.restrict (.val .bool :: Γ)).meet (F₂.restrict (.val .bool :: Γ))) := by
  simp only [program,code,assignLocalOperand,Prog.join,inFragP,inFrag,Frag.guard,
    valIn,simpleIn,Option.all,ite_true,hl,hr]

theorem correct {srcΓ : Source.RCtx} {C : Contract} {Γ Γ₁ Γ₂ : Ctx}
    {L b : Nat} {F : Frag Γ} {F₁ : Frag Γ₁} {F₂ : Frag Γ₂}
    {caller : State C Γ} {machine : Machine}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (left : Prog C (.val .bool :: Γ) Γ₁) (right : Prog C (.val .bool :: Γ) Γ₂)
    (entry : Sim C L b F caller machine)
    (hl : inFragP (F.push (.val .bool) .ok) left = some F₁)
    (hr : inFragP (F.push (.val .bool) .ok) right = some F₂)
    (capacity : L + Prog.pushes (program m i a hi ha left right) ≤ Lmax) :
    StmtOut C (L + Prog.pushes (program m i a hi ha left right)) b
      ((F₁.restrict (.val .bool :: Γ)).meet (F₂.restrict (.val .bool :: Γ)))
      (Prog.shrinks (program m i a hi ha left right))
      (Prog.pays (program m i a hi ha left right))
      (Prog.asserts (program m i a hi ha left right))
      ((program m i a hi ha left right).run caller)
      (run (emit b m i a hi ha (compileProg b left) (compileProg b right)) machine) machine := by
  rw [code_exact]
  exact prog_sim _ entry (admitted F F₁ F₂ m i a hi ha left right hl hr) capacity

end Solidity.Backend.StructuredFlow.MappedBranch
