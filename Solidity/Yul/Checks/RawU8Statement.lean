import Solidity.Yul.RawU8Statement
import Solidity.Yul.Checks.LocalU8Statement
/-! Checked/coherent Source agreement, raw dirty copies and pipeline-specific
partial effects. Refusal is coherence/certificate-only, not frontend admission.
Zero preservation concerns word views, not capture metadata. -/
namespace Solidity.Yul.Checks.RawU8Statement
namespace Old
export Solidity.Yul.Checks.LocalU8Representation (env Ty Ctx x arg flag orderExpr order timeout assign sum readX)
end Old
def ctx : Solidity.Source.Ctx :=
 {env:=Old.env,scope:=none,locals:=[("x",Old.Ty),("arg",Old.Ty),("flag",.bool)]}
def clean : Solidity.Source.Locals Old.env.layout ctx.tys :=
 .cons (.int 1 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool true) .nil))
def xCell : WordCell (localExternalTypes ctx) := .scalar ⟨.unsigned 0,.here⟩
def argCell : WordCell (localExternalTypes ctx) := .scalar ⟨.unsigned 0,.there .here⟩
def flagCell : WordCell (localExternalTypes ctx) := .scalar ⟨.boolean,.there (.there .here)⟩
def initial (a b flag : Nat) (world : Solidity.Source.St Old.env) : RawFrame.State ctx :=
 RawFrame.write (RawFrame.write (RawFrame.write (RawFrame.ofClean clean world)
  xCell (word a)) argCell (word b)) flagCell (word flag)
def witness : Nonempty (LocalU8Expr.Supported ctx.env ctx.tys Old.orderExpr) := ⟨Old.order⟩
theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8Statement.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8Statement.ctx.env))
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawU8Statement.ctx.env.layout Solidity.Yul.Checks.RawU8Statement.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Statement.ctx.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.order glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)).2 = true ∧
 Solidity.Yul.RawCoherent.observe (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.order glob.pipeline fuel (Solidity.Yul.RawFrame.ofClean locals world)) =
 some ((Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.expr (R:=returns) (M:=modifier) (k:=control) Solidity.Yul.Checks.RawU8Statement.Old.orderExpr) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawU8Statement.ctx.env,world)) := by
  intro glob frame checked fuel nps ph returns modifier control locals world
  exact Solidity.Yul.RawU8Statement.correct Solidity.Yul.Checks.RawU8Statement.ctx Solidity.Yul.Checks.RawU8Statement.Old.orderExpr Solidity.Yul.Checks.RawU8Statement.Old.order glob frame checked fuel nps ph returns modifier control (Solidity.Yul.RawFrame.ofClean locals world) (Solidity.Yul.RawCoherent.coherent_ofClean locals world)

theorem zeroAll : ∀ (pipeline : Solidity.Roadmap.Pipeline) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawU8Statement.ctx), (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.order pipeline 0 state).1 = .error .timeout ∧ Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.order pipeline 0 state).2 = Solidity.Yul.RawFrame.view state := by
  intro pipeline state
  exact ⟨rfl,Solidity.Yul.RawU8Statement.zero_view Solidity.Yul.Checks.RawU8Statement.Old.order pipeline state⟩

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Statement.Old.env), (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.timeout .legacy 5 (Solidity.Yul.Checks.RawU8Statement.initial 257 2 1 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.timeout .legacy 5 (Solidity.Yul.Checks.RawU8Statement.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 257 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.timeout .legacy 5 (Solidity.Yul.Checks.RawU8Statement.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawU8Statement.flagCell).val = 1 ∧ (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.timeout .legacy 5 (Solidity.Yul.Checks.RawU8Statement.initial 257 2 1 world)).2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Statement.Old.env), (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.timeout .viaIR 5 (Solidity.Yul.Checks.RawU8Statement.initial 257 2 1 world)).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.timeout .viaIR 5 (Solidity.Yul.Checks.RawU8Statement.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.timeout .viaIR 5 (Solidity.Yul.Checks.RawU8Statement.initial 257 2 1 world)).2 Solidity.Yul.Checks.RawU8Statement.flagCell).val = 1 ∧ (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.timeout .viaIR 5 (Solidity.Yul.Checks.RawU8Statement.initial 257 2 1 world)).2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem rawCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Statement.Old.env), (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.assign pipeline 3 (Solidity.Yul.Checks.RawU8Statement.initial 2 257 2 world)).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.assign pipeline 3 (Solidity.Yul.Checks.RawU8Statement.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 257 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.assign pipeline 3 (Solidity.Yul.Checks.RawU8Statement.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawU8Statement.argCell).val = 257 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.assign pipeline 3 (Solidity.Yul.Checks.RawU8Statement.initial 2 257 2 world)).2 Solidity.Yul.Checks.RawU8Statement.flagCell).val = 2 ∧ Solidity.Yul.RawCoherent.observe (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.assign pipeline 3 (Solidity.Yul.Checks.RawU8Statement.initial 2 257 2 world)) = none := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem panicPrefix : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Statement.Old.env), (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.sum pipeline 4 (Solidity.Yul.Checks.RawU8Statement.initial 511 1 2 world)).1 = .error (.revert (Solidity.Source.panicData .arithmetic)) ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.sum pipeline 4 (Solidity.Yul.Checks.RawU8Statement.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawU8Statement.xCell).val = 511 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.sum pipeline 4 (Solidity.Yul.Checks.RawU8Statement.initial 511 1 2 world)).2 Solidity.Yul.Checks.RawU8Statement.flagCell).val = 2 ∧ (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawU8Statement.Old.sum pipeline 4 (Solidity.Yul.Checks.RawU8Statement.initial 511 1 2 world)).2.world = world := by
  intro pipeline world
  have arithmetic := Solidity.Yul.Checks.LocalU8Representation.overflow .legacy world
  simp only [Solidity.Yul.Checks.LocalU8Representation.sum,
    Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.Checks.LocalU8Representation.readArg,
    LocalU8Expr.add_legacy,LocalU8Expr.local_read,
    Solidity.Yul.Checks.LocalU8Representation.initial,
    Solidity.Yul.Checks.LocalU8Representation.x,Solidity.Yul.Checks.LocalU8Representation.arg,
    LocalValues.get,Except.bind] at arithmetic
  have prepared : RawCoherent.prepare (initial 511 1 2 world) =
    Solidity.Yul.Checks.LocalU8Representation.initial 511 1
      (.scalar (LocalOperations.boolShape Old.env) (word 2)) world := by rfl
  constructor
  · change (LocalU8Statement.run Old.sum pipeline 4 (RawCoherent.prepare (initial 511 1 2 world))).1 = _
    rw [prepared,LocalU8Statement.step]
    cases pipeline <;>
      simp only [Solidity.Yul.Checks.LocalU8Representation.sum,
        Solidity.Yul.Checks.LocalU8Representation.readX,Solidity.Yul.Checks.LocalU8Representation.readArg,
        LocalU8Expr.add_legacy,LocalU8Expr.add_viaIR,LocalU8Expr.local_read,
        Solidity.Yul.Checks.LocalU8Representation.initial,
        Solidity.Yul.Checks.LocalU8Representation.x,Solidity.Yul.Checks.LocalU8Representation.arg,
        LocalValues.get,Except.bind]
    all_goals rw [arithmetic]; rfl
  · cases pipeline <;> exact ⟨rfl,rfl,rfl⟩

theorem dirtyRefusal : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Statement.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawU8Statement.initial 2 257 2 world) = false := by
  intro world
  rfl

theorem unsupportedSub : ¬ Nonempty (Solidity.Yul.LocalU8Expr.Supported Solidity.Yul.Checks.RawU8Statement.ctx.env Solidity.Yul.Checks.RawU8Statement.ctx.tys (.binary .sub (.local Solidity.Yul.Checks.RawU8Statement.Old.x) (.local Solidity.Yul.Checks.RawU8Statement.Old.arg))) := by
  exact Solidity.Yul.Checks.LocalU8Representation.unsupportedSub

#print axioms Solidity.Yul.RawU8Statement.view
#print axioms Solidity.Yul.RawU8Statement.zero_view
#print axioms Solidity.Yul.RawU8Statement.clean_next
#print axioms Solidity.Yul.RawU8Statement.correct
#print axioms Solidity.Yul.RawU8Statement.localRun_coherent
#print axioms sourceAll
#print axioms zeroAll
#print axioms legacyPartial
#print axioms viaIRPartial
#print axioms rawCopy
#print axioms panicPrefix
#print axioms dirtyRefusal
#print axioms unsupportedSub
end Solidity.Yul.Checks.RawU8Statement
