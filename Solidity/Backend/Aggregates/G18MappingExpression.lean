import Solidity.Backend.Aggregates.G18SourceMappingControls

/-! Resolved Source mapping assignments over the published evaluator.
These clients are not frontend acceptance or general compiler certificates. -/
namespace Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression

abbrev Sample := Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample

def reference (c : Sample) : Source.RExpr (Controls.E c) [.bool] (.mapping .bool (.int c.ty)) :=
  .state (Solidity.Backend.Aggregates.ScalarMapping.Controls.declaration c.ty) rfl

def read (c : Sample) (key : Bool) : Source.RExpr (Controls.E c) [.bool] (.int c.ty) :=
  .indexMapping (reference c) (.bool key)

def location (c : Sample) (key : Bool) : Source.RLVal (Controls.E c) [.bool] (.int c.ty) :=
  .indexMapping (reference c) (.bool key)

def assignment (c : Sample) : Source.RExpr (Controls.E c) [.bool] (.int c.ty) :=
  .assign (location c false) (read c true)

theorem reference_program : ∀ (c : Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Sample) (G : Solidity.Source.Glob (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c)) (F : Solidity.Source.Fr) (fuel : Nat), Solidity.Source.evalE G F (fuel+1) (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.reference c) = pure (.val (.storRef rfl (Solidity.Backend.Aggregates.ScalarMapping.Controls.declaration c.ty).path)) := by
  intro c G F fuel
  rfl

theorem location_program : ∀ (c : Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Sample) (G : Solidity.Source.Glob (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c)) (F : Solidity.Source.Fr) (fuel : Nat) (key : Bool), Solidity.Source.evalLoc G F (fuel+2) (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.location c key) = pure (.stor (Solidity.Backend.Aggregates.ScalarMapping.Controls.path key)) := by
  intro c G F fuel key
  cases key <;> rfl

theorem read_program : ∀ (c : Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Sample) (G : Solidity.Source.Glob (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c)) (F : Solidity.Source.Fr) (fuel : Nat) (key : Bool), Solidity.Source.evalE G F (fuel+2) (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.read c key) = (do let v ← Solidity.Source.readAt (E := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) (Γ := [.bool]) F (Solidity.Backend.Aggregates.ScalarMapping.Controls.path key) (.int c.ty); pure (.val v)) := by
  intro c G F fuel key
  cases key <;> rfl

theorem assignment_run : ∀ (c : Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Sample) (G : Solidity.Source.Glob (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c)) (fuel : Nat), (Solidity.Source.evalE G Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame (fuel+3) (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment c)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) = (.ok (.val (.int c.a c.ha)),(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState c)) := by
  intro c G fuel
  have hread : (Solidity.Source.readAt (E := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) (Γ := [.bool]) Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame (Solidity.Backend.Aggregates.ScalarMapping.Controls.path true) (.int c.ty)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) = (.ok (.int c.a c.ha),(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c)) := (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.certificate c).1
  have hwrite : (Solidity.Source.writeAt (E := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) (Γ := [.bool]) (τ := .int c.ty) Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (.int c.a c.ha)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) = (.ok (),(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState c)) := (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.certificate c).2.1
  unfold Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment
  rw [Solidity.Source.evalE]
  rw [Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.read_program,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.location_program]
  simp only [bind_assoc,pure_bind,Solidity.Source.getV,Solidity.Source.RVal.get,Solidity.Source.EM.lift,Solidity.Source.writeLoc,Solidity.Source.STy.byRef,Solidity.Source.STy.loc?,Option.isSome_none,Bool.false_eq_true,ite_false]
  rw [Solidity.Source.Hoare.run_bind,hread]
  change ExceptT.run ((Solidity.Source.writeAt (E := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) (Γ := [.bool]) (τ := .int c.ty) Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (.int c.a c.ha)) >>= fun (_ : Unit) => (pure (Solidity.Source.RVal.val (.int c.a c.ha)) : Solidity.Source.EM (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) [.bool] (Solidity.Source.RVal (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c).layout (.int c.ty)))) (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) = _
  rw [Solidity.Source.Hoare.run_bind,hwrite]
  rfl

theorem static_run : ∀ (c : Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.Sample) (G : Solidity.Source.Glob (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c)) (fuel : Nat), (Solidity.Source.evalE G {Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame with static := true} (fuel+3) (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment c)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) = (.error (.revert []),(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c)) := by
  intro c G fuel
  have hread : (Solidity.Source.readAt (E := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) (Γ := [.bool]) {Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame with static := true} (Solidity.Backend.Aggregates.ScalarMapping.Controls.path true) (.int c.ty)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) = (.ok (.int c.a c.ha),(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c)) := (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.certificate c).1
  have hwrite : (Solidity.Source.writeAt (E := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) (Γ := [.bool]) (τ := .int c.ty) {Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame with static := true} (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (.int c.a c.ha)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) = (.error (.revert []),(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c)) := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.refused (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) [.bool] _ (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c) (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (.int c.a c.ha) rfl rfl
  unfold Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment
  rw [Solidity.Source.evalE]
  rw [Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.read_program,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.location_program]
  simp only [bind_assoc,pure_bind,Solidity.Source.getV,Solidity.Source.RVal.get,Solidity.Source.EM.lift,Solidity.Source.writeLoc,Solidity.Source.STy.byRef,Solidity.Source.STy.loc?,Option.isSome_none,Bool.false_eq_true,ite_false]
  rw [Solidity.Source.Hoare.run_bind,hread]
  change ExceptT.run ((Solidity.Source.writeAt (E := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) (Γ := [.bool]) (τ := .int c.ty) {Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame with static := true} (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (.int c.a c.ha)) >>= fun (_ : Unit) => (pure (Solidity.Source.RVal.val (.int c.a c.ha)) : Solidity.Source.EM (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) [.bool] (Solidity.Source.RVal (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c).layout (.int c.ty)))) (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) = _
  rw [Solidity.Source.Hoare.run_bind,hwrite]

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.reference_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_program

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.location_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms location_program

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.read_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms read_program

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.assignment_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms assignment_run

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression.static_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms static_run
end Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Expression
