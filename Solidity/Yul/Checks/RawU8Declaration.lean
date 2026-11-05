import Solidity.Yul.RawU8Declaration
import Solidity.Yul.Checks.RawPreparedInteger
/-! Actual uint8 expression declarations, partial effects and dirty-word refusal.
These are kernel controls, not frontend or external solc admission evidence. -/
namespace Solidity.Yul.Checks.RawU8Declaration
namespace Old
export Solidity.Yul.Checks.RawU8Statement (ctx clean initial xCell argCell flagCell)
export Solidity.Yul.Checks.RawU8Statement.Old (assign timeout)
export Solidity.Yul.Checks.RawPreparedInteger.Old (canonical unsignedCtx grownX grownArg grownFlag)
end Old
def nextCell : WordCell (localExternalTypes Old.unsignedCtx) := .scalar ⟨.unsigned 0,.here⟩
def changed : Solidity.Source.Locals Old.ctx.env.layout Old.ctx.tys :=
 .cons (.int 2 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool true) .nil))
def next (world : Solidity.Source.St Old.ctx.env) : RawFrame.State Old.unsignedCtx :=
 RawFrame.capture (RawFrame.ofClean (.cons (.int 2 (by decide)) changed) world)
 (localWordCells Old.unsignedCtx (LocalValues.ofClean (.cons (.int 2 (by decide)) changed)))
def statement : Solidity.Source.RStmt Old.ctx.env [] false ⟨true,false⟩ Old.ctx.tys Old.unsignedCtx.tys :=
 Solidity.Source.RStmt.declInit (E := Old.ctx.env) (R := []) (M := false)
  (k := ⟨true,false⟩) (Γ := Old.ctx.tys) (τ := LocalU8Expr.Ty)
  Solidity.Yul.Checks.LocalU8Representation.assignExpr (by rfl)
def witness : Nonempty (LocalU8Expr.Supported Old.ctx.env Old.ctx.tys
 (.assign (.local .here) (.local (.there .here)))) := ⟨Old.assign⟩

theorem normal : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env), Solidity.Yul.RawU8Declaration.run "n" Solidity.Yul.Checks.RawU8Declaration.Old.assign pipeline 3 (Solidity.Yul.Checks.RawU8Declaration.Old.canonical world) = .inr (Solidity.Yul.Checks.RawU8Declaration.next world) := by
  intro pipeline world
  rfl

theorem zero : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env), Solidity.Yul.RawU8Declaration.run "n" Solidity.Yul.Checks.RawU8Declaration.Old.assign pipeline 0 (Solidity.Yul.Checks.RawU8Declaration.Old.initial 2 257 2 world) = .inl (.timeout,Solidity.Yul.Checks.RawU8Declaration.Old.initial 2 257 2 world) := by
  intro pipeline world
  rfl

theorem rawCopy : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env), match Solidity.Yul.RawU8Declaration.run "n" Solidity.Yul.Checks.RawU8Declaration.Old.assign pipeline 3 (Solidity.Yul.Checks.RawU8Declaration.Old.initial 2 257 2 world) with
 | .inl _ => False
 | .inr next => (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawU8Declaration.nextCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawU8Declaration.Old.grownX).val = 257 ∧
 (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawU8Declaration.Old.grownArg).val = 257 ∧
 (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawU8Declaration.Old.grownFlag).val = 2 ∧
 Solidity.Yul.RawCoherent.coherent next = false ∧ next.world = world := by
  intro pipeline world
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env),
 (match Solidity.Yul.RawU8Declaration.run "n" Solidity.Yul.Checks.RawU8Declaration.Old.assign glob.pipeline fuel (Solidity.Yul.Checks.RawU8Declaration.Old.canonical world) with
 | .inl failure => Solidity.Yul.RawCoherent.coherent failure.2 = true
 | .inr next => Solidity.Yul.RawCoherent.coherent next = true) ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawU8Declaration.statement Solidity.Yul.Checks.RawU8Declaration.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env,world) = Solidity.Yul.RawPreparedInteger.project
 (Solidity.Yul.RawU8Declaration.run "n" Solidity.Yul.Checks.RawU8Declaration.Old.assign glob.pipeline fuel (Solidity.Yul.Checks.RawU8Declaration.Old.canonical world)) := by
  intro glob frame checked fuel nps ph world
  have actual := RawU8Declaration.correct Old.ctx "n" _ Old.assign [] false ⟨true,false⟩
    glob frame checked fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)
  have clean : (Old.canonical world).clean = Old.clean := rfl
  have worldSame : (Old.canonical world).world = world := rfl
  cases output : RawU8Declaration.run "n" Old.assign glob.pipeline fuel (Old.canonical world) <;>
   simpa only [output,clean,worldSame,statement,
    Solidity.Yul.Checks.LocalU8Representation.assignExpr,
    Solidity.Yul.Checks.LocalU8Representation.x,
    Solidity.Yul.Checks.LocalU8Representation.arg] using actual

theorem sourceNormal : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env),
 (Solidity.Source.execS glob frame 3 nps ph Solidity.Yul.Checks.RawU8Declaration.statement Solidity.Yul.Checks.RawU8Declaration.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env,world) =
 (.ok (.normal (Solidity.Yul.Checks.RawU8Declaration.next world).clean),(Solidity.Source.L0 Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env,world)) := by
  intro glob frame checked nps ph world
  rw [(sourceAll glob frame checked 3 nps ph world).2,normal]
  rfl

theorem negative : ¬ Nonempty (Solidity.Yul.LocalU8Expr.Supported Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env Solidity.Yul.Checks.RawU8Declaration.Old.ctx.tys
 (.binary .sub (.local .here) (.local (.there .here)))) := by
  rintro ⟨proof⟩
  cases proof

theorem legacyPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env), match Solidity.Yul.RawU8Declaration.run "n" Solidity.Yul.Checks.RawU8Declaration.Old.timeout .legacy 5 (Solidity.Yul.Checks.RawU8Declaration.Old.initial 257 2 1 world) with
 | .inr _ => False
 | .inl failure => failure.1 = .timeout ∧
 (Solidity.Yul.RawFrame.view failure.2 Solidity.Yul.Checks.RawU8Declaration.Old.xCell).val = 257 ∧
 (Solidity.Yul.RawFrame.view failure.2 Solidity.Yul.Checks.RawU8Declaration.Old.flagCell).val = 1 ∧ failure.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem viaIRPartial : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawU8Declaration.Old.ctx.env), match Solidity.Yul.RawU8Declaration.run "n" Solidity.Yul.Checks.RawU8Declaration.Old.timeout .viaIR 5 (Solidity.Yul.Checks.RawU8Declaration.Old.initial 257 2 1 world) with
 | .inr _ => False
 | .inl failure => failure.1 = .timeout ∧
 (Solidity.Yul.RawFrame.view failure.2 Solidity.Yul.Checks.RawU8Declaration.Old.xCell).val = 2 ∧
 (Solidity.Yul.RawFrame.view failure.2 Solidity.Yul.Checks.RawU8Declaration.Old.flagCell).val = 1 ∧ failure.2.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩
end Solidity.Yul.Checks.RawU8Declaration
#print axioms Solidity.Yul.RawU8Declaration.correct
#print axioms Solidity.Yul.Checks.RawU8Declaration.normal
#print axioms Solidity.Yul.Checks.RawU8Declaration.zero
#print axioms Solidity.Yul.Checks.RawU8Declaration.rawCopy
#print axioms Solidity.Yul.Checks.RawU8Declaration.sourceAll
#print axioms Solidity.Yul.Checks.RawU8Declaration.sourceNormal
#print axioms Solidity.Yul.Checks.RawU8Declaration.negative
#print axioms Solidity.Yul.Checks.RawU8Declaration.legacyPartial
#print axioms Solidity.Yul.Checks.RawU8Declaration.viaIRPartial
