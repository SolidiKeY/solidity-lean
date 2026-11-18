import Solidity.Correctness.Lowering.Sim.Stmt.Jump
import Solidity.Correctness.Lowering.Sim.Expr.Frame

/-!
# Statement cases, v2: the frame premise (provisional)

The v1 run clauses (`Sim/Match/Cases.lean`, frozen and unchanged) range over
every Source record and frame, and no body that reads its frame meets them
(`Stmt/Frame.lean`). The v2 obligations are those of `Sim/Expr/Frame.lean`
(`RunSim₂`, `SiteSim₂`, with the bridges `RunSim.frame` and `SiteSim.frame`):
the run clauses under `frameRel`. This file adds what the statement cases
need over them.

* `initial_matching`: at every frame that is checked and not static, every
  Source state of an associated body has a related target state that also
  meets `frameRel`, so the frame premise is satisfiable where it can be.
* `V2.ArmSat`, `V2.StmtArm`: the v1 definitions over `SiteSim₂`. Every v1
  case transfers (`StmtArm.of_v1`), so the jump conjunct holds (`jump_cases`).

Provisional and unfrozen. Not here: `RunSim₂` still asks for v1's initial
matching only; and the cases are still per arm, which `Sim/Match/Cases.lean`
("Limitations") shows unprovable where an arm's output is a part of a body's
elaboration.
-/

namespace Solidity.Correctness.Lowering.Sim.Stmt.V2

open Solidity.Goals (ElabRan elabKernelTotal)
open Solidity.Goals.Shrink.Lowering (Body Emitted)
open Solidity.Lowering.V07 (ContextMap)

/-- **Initial matching under the frame premise**: at a checked, non-static
frame every Source state of an associated body has a related target state
whose transaction is the frame (`frameRel`), at the frame's own instance. -/
theorem initial_matching (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ)
    (h : Sim.diagram.Assoc b u m) (G : Source.Glob b.E) (F : Source.Fr)
    (frame : F.static = false ∧ F.checked = true) (src : Source.EMState b.E b.ctx) :
    ∃ tgt : State u.C u.Γ, m.Related (fun τ v => Sim.diagram.valRel τ v) src.1 tgt.env ∧
      Sim.diagram.globRel src.2 tgt ∧ frameRel G F tgt := by
  have h : Sim.Assoc b u m := h
  obtain ⟨env, related⟩ := h.2.2.1.locals b.E.layout u.C [] src.1
  obtain ⟨storage, fields⟩ := Total.Simulation.fields_onto (cell src.2 F.this) u.C.vars
    fun x T mem => by
      obtain ⟨p, rfl, ty⟩ := h.storageTyped x T mem
      exact ⟨p, rfl, Total.Simulation.read_prim _ _ p ty⟩
  have wide (a : Roadmap.Address) : a.val < 2 ^ 256 :=
    Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) (by decide))
  let word := Total.Simulation.wordDenote
  let tx : TTx :=
    { msgSender := word ⟨_, wide F.sender⟩
      selfAddress := word ⟨_, wide F.this⟩
      msgValue := word F.value
      timestamp := word G.timestamp }
  by_cases fits : Source.Monetary.Fits (src.2.ex.world.accounts F.this).balance
  · exact ⟨⟨storage, [], Heap.empty, env, [], word ⟨_, fits⟩, tx⟩, related,
      ⟨F.this, rfl, fields, fun _ => rfl⟩, rfl, rfl, rfl, rfl, frame⟩
  · exact ⟨⟨storage, [], Heap.empty, env, [], PrimTy.dflt .uint, tx⟩, related,
      ⟨F.this, rfl, fields, fun h => absurd h fits⟩, rfl, rfl, rfl, rfl, frame⟩

variable [FreshNames] (C : Contract)

/-- A statement arm meets the v2 obligations on a family. -/
def ArmSat (arm : RawStmt → ElabM (SProg C)) (family : StmtFamily) : Prop :=
  ∀ s, stmtFamily s = family →
    ∀ sc st P st', ElabRan (arm s) sc st P st' → SiteSim₂ C [s] sc st P st'

/-- Both statement arms of a family meet the v2 obligations. -/
def StmtArm (rc : ElabRec C) (family : StmtFamily) : Prop :=
  ArmSat C (elabStmtPWith C rc) family ∧ ArmSat C (elabStmt1With C rc) family

/-- A v1 case is a v2 case. -/
theorem StmtArm.of_v1 {rc : ElabRec C} {family : StmtFamily} (h : Sim.StmtArm C rc family) :
    StmtArm C rc family :=
  ⟨fun s f sc st P st' ran => (h.1 s f sc st P st' ran).frame,
    fun s f sc st P st' ran => (h.2 s f sc st P st' ran).frame⟩

/-- **The jump case, v2.** -/
theorem jump_cases (kernel : elabKernelTotal) (rc : ElabRec C) : StmtArm C rc .jump :=
  .of_v1 C (Sim.jump_cases C kernel rc)

end Solidity.Correctness.Lowering.Sim.Stmt.V2
