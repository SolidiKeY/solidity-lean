import Solidity.Correctness.Lowering.Sim.Match.CompositionV2

/-! # The statement-level contract, v2: shape checks, every law a hypothesis -/
namespace Solidity.Examples.Lowering.Sim.StatementV2

open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)
open Solidity.Correctness.Lowering.Sim
open Solidity.Correctness.Lowering.Sim.StatementV2
open Solidity.Correctness.Lowering.Sim.CompositionV2

variable [FreshNames]

/-- **End to end**: the induction, the step, the block and site laws at a
covering, splitting interpretation give the v2 per-run obligation. -/
example (C : Contract) (I : Interp) (induction : AssembledInduction C) (step : KnotStep C I)
    (block : BlockLaw C I) (splits : I.Splits C (elabStmtP C)) (site : SiteLaw C I)
    (fuel : I.fuel = diagram.fuel) (covers : I.Covers C) (b : Body) (Γ : Ctx)
    (o : Solidity.Correctness.Lowering.Checker.Output C Γ) (m : ContextMap b.ctx Γ) (production : Production b ⟨C, Γ, o⟩)
    (accepted : Accepted ⟨C, Γ, o⟩) (assoc : diagram.Assoc b ⟨C, Γ, o⟩ m) :
    RunSim₂ b ⟨C, Γ, o⟩ m :=
  runs₂_of_segments C I (site fuel covers)
    (block _ splits (knot_genSeg C I induction step).2.1) b Γ o m production accepted
    assoc

/-- What later checkpoints prove, once the relation is reviewed. -/
example (C : Contract) (I : Interp) : Prop :=
  SeqLaw ∧ RefinesLaw ∧ MapExt.Laws ∧ ChainAppendLaw ∧ CaptureLaw C I ∧ ClosureLaw C I

/-- The knot's `hoistTop`, free under v1 `RecSim`, is derived from its `hoist`. -/
example (C : Contract) : (elabRec C ()).hoistTop = hoistTopWith C (hoist C) :=
  (assembled_fields C (hoist C) (elabStmtP C) _).2.2.1

/-- A simulating statement arm meets the `CasesV2` statement conclusion. -/
example (C : Contract) (I : Interp) (sites : Sites C I) (splits : I.Splits C (elabStmtP C))
    (rc : ElabRec C) (arm : Solidity.Goals.ElabSat (stmtQ C I) (elabStmtPWith C rc)) :
    Stmt.V2.ArmSat C (elabStmtPWith C rc) .assign :=
  armSat_of_stmt C I sites splits.single _ arm _

/-- A part's final matching with no Source local pushed is the diagram's. -/
example {E : Source.Env} {Γs : Source.RCtx} {C : Contract} {Γ Γ' : Ctx} {H : HTy}
    (m : ContextMap Γs Γ) (emb : Thin Γ Γ') (G : Source.Glob E) (F : Source.Fr)
    (src : SrcRes E Γs Γs) (tgt : TRes (Out C H Γ'))
    (ext : MapExt (base := Γs) (pre := []) (pre' := []) m emb (m.wk emb))
    (h : SegFinal (m.wk emb) G F src tgt) : diagram.Final m emb src tgt :=
  h.final ext

end Solidity.Examples.Lowering.Sim.StatementV2
