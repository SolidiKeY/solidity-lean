import Solidity.Backend.Aggregates.G18MappingExpression
import Solidity.Roadmap.Controls

/-! Concrete Source expression clients. The reused G07 Fixed control is
not a full Osaka/precompile/ledger or frontend-admission certificate. This
expression calls none of those external operations. -/
namespace Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls

abbrev Sample := Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample
abbrev sourceEnv := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E

def program (c : Sample) : Source.Program (sourceEnv c) where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []

def globals (c : Sample) (pipeline : Roadmap.Pipeline) : Source.Glob (sourceEnv c) :=
  ⟨program c,pipeline,Roadmap.Controls.toyFixed,fun _ => ⟨0,by decide⟩,
    fun _ _ => false,fun _ => .answer (.success []),⟨101,by decide⟩⟩

theorem baselines : ∀ (sample : Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.Sample) (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat), (Solidity.Source.evalE (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.globals sample pipeline) Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame (fuel+3) (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment sample)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals sample,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state sample) = (.ok (.val (.int sample.a sample.ha)),(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals sample,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState sample)) := by
  intro sample pipeline fuel
  exact Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment_run sample (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.globals sample pipeline) fuel

theorem low_fuel : ∀ pipeline : Solidity.Roadmap.Pipeline, (Solidity.Source.evalE (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.globals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned pipeline) Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame 0 (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned) = (.error .timeout,(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned)) ∧ (Solidity.Source.evalE (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.globals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned pipeline) Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame 1 (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned) = (.error .timeout,(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned)) ∧ (Solidity.Source.evalE (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.globals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned pipeline) Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame 2 (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned) = (.error .timeout,(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned)) := by
  intro pipeline
  exact ⟨rfl,rfl,rfl⟩

theorem wrong_result : (Solidity.Source.evalE (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.globals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned .legacy) Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame 3 (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned) ≠ (.ok (.val (.int 11 (by decide))),(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned)) := by
  intro wrong
  have actual := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment_run Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.globals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned .legacy) 0
  have result := congrArg Prod.fst (actual.symm.trans wrong)
  cases result

theorem wrong_phase : (Solidity.Source.evalE (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.globals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned .legacy) Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame 3 (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned) ≠ (.ok (.val (.int 7 (by decide))),(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned)) := by
  intro wrong
  have actual := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment_run Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.globals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned .legacy) 0
  have lengths := congrArg (fun result => result.2.2.ex.journal.length) (actual.symm.trans wrong)
  change 2 = 1 at lengths
  contradiction

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.baselines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms baselines

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.low_fuel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms low_fuel

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.wrong_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_result

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls.wrong_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_phase
end Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Controls
