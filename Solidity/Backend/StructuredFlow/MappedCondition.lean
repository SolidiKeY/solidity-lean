import Solidity.Evm.Correct
import Solidity.Lowering.G19.AssignmentReturnFlag

/-! Actual published compiler code and reached machine for the V07 mapped
assignment condition. This is a captured-selector prefix, not function exit. -/
namespace Solidity.Backend.StructuredFlow.MappedCondition
open Solidity.Evm Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag

def emit {srcΓ : Source.RCtx} {Γ : Ctx} (b : Nat) (m : ContextMap srcΓ Γ)
    (i a : Source.Idx srcΓ .bool) (hi : (m.slot i).1 = .val .bool)
    (ha : (m.slot a).1 = .val .bool) : List Instr :=
  [.mload (cellOf b (boolSlot m a ha)), .mstore (cellOf b (boolSlot m i hi)),
   .mload (cellOf b (boolSlot m i hi)), .mstore (cell (b + Γ.length))]

def after {srcΓ : Source.RCtx} {Γ : Ctx} (b : Nat) (m : ContextMap srcΓ Γ)
    (i a : Source.Idx srcΓ .bool) (hi : (m.slot i).1 = .val .bool)
    (ha : (m.slot a).1 = .val .bool) (machine : Machine) : Machine :=
  let value := machine.mem (cellOf b (boolSlot m a ha))
  let written := upd machine.mem (cellOf b (boolSlot m i hi)) value
  {machine with mem := upd written (cell (b + Γ.length)) value}


theorem code_exact {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (b : Nat) (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) :
    emit b m i a hi ha = compileProg b (code m i a hi ha : Prog C Γ (.val .bool :: Γ)) := rfl

theorem admitted {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (F : Frag Γ) (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) :
    inFragP F (code m i a hi ha : Prog C Γ (.val .bool :: Γ)) =
      some (F.push (.val .bool) .ok) := rfl

theorem run_exact {srcΓ : Source.RCtx} {Γ : Ctx}
    (b : Nat) (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) (machine : Machine) :
    run (emit b m i a hi ha) machine = .ok (after b m i a hi ha machine) 0 := by
  simp only [emit,after,run,exec,Instr.step,Machine.next,Out.bind,upd_same]

theorem postSim {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    {L b : Nat} {F : Frag Γ} {caller : State C Γ} {machine : Machine}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (entry : Sim C L b F caller machine) :
    Sim C L b (F.push (.val .bool) .ok) (reached m i a hi ha caller)
      (after b m i a hi ha machine) := by
  have value : ReprV .bool (TEnv.get (boolSlot m a ha) caller.env)
      (machine.mem (cellOf b (boolSlot m a ha))) := entry.vals (boolSlot m a ha)
  exact Sim.pushVal (Sim.setLocalVal entry (boolSlot m i hi) value) value

theorem correct {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    {L b : Nat} {F : Frag Γ} {caller : State C Γ} {machine : Machine}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (entry : Sim C L b F caller machine) :
    StmtOut C L b (F.push (.val .bool) .ok) false false false
      ((code m i a hi ha : Prog C Γ (.val .bool :: Γ)).run caller)
      (run (emit b m i a hi ha) machine) machine := by
  rw [code_exact]
  exact prog_sim _ entry (admitted F m i a hi ha) entry.bound

end Solidity.Backend.StructuredFlow.MappedCondition
