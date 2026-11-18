import Solidity.Correctness.Lowering.Sim.Stmt.Jump

/-!
# Statement cases, v2: the frame premise (provisional)

An additive v2 of the per-run vocabulary, next to the frozen v1
(`Goals/LoweringDiagram.lean`, `Sim/Match/Cases.lean`), which is unchanged.
The v1 forward and backward clauses range over every Source record and frame,
and no body that reads its frame meets them (`Stmt/Frame.lean`). Here they
take a frame relation as a premise.

* `V2.Diagram`: a v1 diagram with a `frameRel`; `V2.Diagram.Simulates` is v1's
  `Simulates` with `frameRel G F tgt` before the run clauses.
* `V2.diagram`: `Sim.diagram` with `Sim.frameRel` (`Sim/Match/Relations.lean`).
* `V2.RunSim`, `SiteSim`, `stmtQ`, `ArmSat`, `StmtArm`: the v1 definitions
  over the v2 run clauses. Every v1 result transfers (`RunSim.of_v1`,
  `StmtArm.of_v1`), so the jump conjunct holds (`jump_cases`).

* `initial_matching`: at every frame that is checked and not static, every
  Source state of an associated body has a related target state that also
  meets `frameRel`, so the frame premise is satisfiable where it can be.

Provisional and unfrozen. Not here: `V2.RunSim` itself still asks for v1's
initial matching only; and the cases are still per arm, which
`Sim/Match/Cases.lean` ("Limitations") shows unprovable where an arm's output
is a part of a body's elaboration.
-/

namespace Solidity.Correctness.Lowering.Sim.Stmt.V2

open Solidity.Goals (ElabRan elabKernelTotal)
open Solidity.Goals.Shrink.Lowering (Body Emitted Production Accepted LowerFresh sourceRun
  Lowered Threaded)
open Solidity.Lowering.V07 (ContextMap IntValueRel integerPrim)
open Solidity.Correctness.Lowering.Checker (Output)

/-- A v1 diagram with a relation between the Source record and frame and the
target state. -/
structure Diagram extends Solidity.Goals.Shrink.Lowering.Diagram where
  frameRel : {E : Source.Env} → {C : Contract} → {Γ : Ctx} →
    Source.Glob E → Source.Fr → State C Γ → Prop

/-- `Sim.diagram` with the frame relation of `Sim/Match/Relations.lean`. -/
def diagram : Diagram where
  toDiagram := Sim.diagram
  frameRel := Sim.frameRel

variable [FreshNames]

/-- The run clauses of v1 at one record, frame and matched pair of states. -/
def Runs (D : Diagram) (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ)
    (emb : Thin u.Γ u.output.program.1) (G : Source.Glob b.E) (F : Source.Fr) (nps : Nat)
    (ph : Option (Source.Ph b.E)) (src : Source.EMState b.E b.ctx) (tgt : State u.C u.Γ) : Prop :=
  (∀ n, (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
    D.Final m emb (sourceRun b G F n nps ph src) (u.output.program.2.runF (D.fuel n) tgt)) ∧
  (∀ n n', n ≤ n' → (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
    sourceRun b G F n' nps ph src = sourceRun b G F n nps ph src) ∧
  (∀ n, u.output.program.2.runF n tgt ≠ .error .diverge →
    ∃ j, D.Final m emb (sourceRun b G F j nps ph src) (u.output.program.2.runF n tgt))

/-- **The per-run obligations, v2**: v1's, the run clauses under `frameRel`. -/
def Diagram.RunSim (D : Diagram) (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ) : Prop :=
  LowerFresh b u ∧
  (∀ src : Source.EMState b.E b.ctx, ∃ tgt : State u.C u.Γ,
    m.Related (fun τ v => D.valRel τ v) src.1 tgt.env ∧ D.globRel src.2 tgt) ∧
  ∃ emb : Thin u.Γ u.output.program.1,
  ∀ (G : Source.Glob b.E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph b.E))
    (src : Source.EMState b.E b.ctx) (tgt : State u.C u.Γ),
    m.Related (fun τ v => D.valRel τ v) src.1 tgt.env → D.globRel src.2 tgt →
    D.frameRel G F tgt → Runs D b u m emb G F nps ph src tgt

/-- **The diagram's obligations, v2**: v1's `Diagram.Simulates` with the run
clauses under `frameRel`. -/
def Diagram.Simulates (D : Diagram) : Prop :=
  (∀ {Dl : Source.Layout} {C : Contract} {H : HTy} (v : Source.Val Dl .bool) (b : Bool),
    D.valRel (C := C) (H := H) .bool (.val .bool) v b → v = .bool b) ∧
  (∀ {Dl : Source.Layout} {C : Contract} {H : HTy} (t : Source.IntTy) (v : Source.Val Dl (.int t))
    (x : (integerPrim t).Denote), D.valRel (C := C) (H := H) (.int t) (.val (integerPrim t)) v x →
      IntValueRel t v x) ∧
  (∀ n n', n ≤ n' → D.fuel n ≤ D.fuel n') ∧
  ∀ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ),
    Production b u → Accepted u → D.Assoc b u m → D.RunSim b u m

/-- The per-run obligations of `V2.diagram`. -/
abbrev RunSim (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ) : Prop := diagram.RunSim b u m

omit [FreshNames] in
/-- A v1 run is a v2 run: the frame premise is dropped. -/
theorem RunSim.of_v1 {b : Body} {u : Emitted} {m : ContextMap b.ctx u.Γ} (h : Sim.RunSim b u m) :
    RunSim b u m :=
  ⟨h.1, h.2.1, h.2.2.elim fun emb runs =>
    ⟨emb, fun G F nps ph src tgt related glob _ => runs G F nps ph src tgt related glob⟩⟩

/-- `RunSim` at every associated production run of the fragment is
`V2.diagram.Simulates`. -/
theorem simulates_of_runs
    (runs : ∀ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ),
      Production b u → Accepted u → Sim.diagram.Assoc b u m → RunSim b u m) :
    diagram.Simulates :=
  ⟨diagram_relations.1, diagram_relations.2.1, diagram_relations.2.2, runs⟩

omit [FreshNames] in
/-- **Initial matching under the frame premise**: at a checked, non-static
frame every Source state of an associated body has a related target state
whose transaction is the frame (`frameRel`), at the frame's own instance. -/
theorem initial_matching (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ)
    (h : Sim.diagram.Assoc b u m) (G : Source.Glob b.E) (F : Source.Fr)
    (frame : F.static = false ∧ F.checked = true) (src : Source.EMState b.E b.ctx) :
    ∃ tgt : State u.C u.Γ, m.Related (fun τ v => diagram.valRel τ v) src.1 tgt.env ∧
      diagram.globRel src.2 tgt ∧ diagram.frameRel G F tgt := by
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

variable (C : Contract)

/-- **The obligations at a site, v2** (v1's `SiteSim` over `V2.RunSim`). -/
def SiteSim (raw : List RawStmt) (sc : ElabScope) (st : ECtx × Nat) (P : SProg C)
    (st' : ECtx × Nat) : Prop :=
  ∀ (b : Body) (Γ : Ctx) (o : Output C Γ) (m : ContextMap b.ctx Γ),
    Elaborated C o raw sc st P st' → Lowered b ⟨C, Γ, o⟩ → Threaded b ⟨C, Γ, o⟩ →
    Accepted ⟨C, Γ, o⟩ → Sim.diagram.Assoc b ⟨C, Γ, o⟩ m → RunSim b ⟨C, Γ, o⟩ m

/-- A statement arm meets the v2 obligations on a family. -/
def ArmSat (arm : RawStmt → ElabM (SProg C)) (family : StmtFamily) : Prop :=
  ∀ s, stmtFamily s = family →
    ∀ sc st P st', ElabRan (arm s) sc st P st' → SiteSim C [s] sc st P st'

/-- Both statement arms of a family meet the v2 obligations. -/
def StmtArm (rc : ElabRec C) (family : StmtFamily) : Prop :=
  ArmSat C (elabStmtPWith C rc) family ∧ ArmSat C (elabStmt1With C rc) family

/-- A v1 case is a v2 case. -/
theorem StmtArm.of_v1 {rc : ElabRec C} {family : StmtFamily} (h : Sim.StmtArm C rc family) :
    StmtArm C rc family :=
  ⟨fun s f sc st P st' ran b Γ o m e l t a assoc =>
      RunSim.of_v1 (h.1 s f sc st P st' ran b Γ o m e l t a assoc),
    fun s f sc st P st' ran b Γ o m e l t a assoc =>
      RunSim.of_v1 (h.2 s f sc st P st' ran b Γ o m e l t a assoc)⟩

/-- **The jump case, v2.** -/
theorem jump_cases (kernel : elabKernelTotal) (rc : ElabRec C) : StmtArm C rc .jump :=
  .of_v1 C (Sim.jump_cases C kernel rc)

end Solidity.Correctness.Lowering.Sim.Stmt.V2
