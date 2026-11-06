import Solidity.Yul.RawPreparedInteger
import Solidity.Yul.Checks.RawTypedScope

/-! Actual integer declaration/frame boundaries and a concrete grown consumer.
Source projection is stored-clean; dirty older words are independently retained.
This does not claim the enclosing integer block's final composition. -/
namespace Solidity.Yul.Checks.RawPreparedInteger
namespace Old
export Solidity.Yul.Checks.RawControlGrowingBlock.Old (ctx env canonical clean captured)
export Solidity.Yul.Checks.RawTypedScope (signed8 unsignedCtx signedCtx newCell signedCell grownX grownArg grownFlag)
end Old
def boundU : Solidity.Source.IntTy.u8.lo ≤ (255 : Int) ∧ (255 : Int) ≤ Solidity.Source.IntTy.u8.hi := by decide
def boundS : Old.signed8.lo ≤ (-128 : Int) ∧ (-128 : Int) ≤ Old.signed8.hi := by decide
def nextUnsigned (world : Solidity.Source.St Old.env) : RawFrame.State Old.unsignedCtx :=
 RawDeclarationFrame.ofSnapshot
  ⟨.cons (.int 255 boundU) Old.clean,LocalValues.ofClean (.cons (.int 255 boundU) Old.clean),world⟩
def nextSigned (world : Solidity.Source.St Old.env) : RawFrame.State Old.signedCtx :=
 RawDeclarationFrame.ofSnapshot
  ⟨.cons (.int (-128) boundS) Old.clean,LocalValues.ofClean (.cons (.int (-128) boundS) Old.clean),world⟩
def copyExpr : Solidity.Source.RExpr Old.env Old.unsignedCtx.tys LocalU8Expr.Ty :=
 .assign (.local (.there .here)) (.local .here)
def copyProof : LocalU8Expr.Supported Old.env Old.unsignedCtx.tys copyExpr :=
 .assign (.there .here) (.local .here)
def changed : Solidity.Source.Locals Old.env.layout Old.ctx.tys :=
 .cons (.int 255 boundU) (.cons (.int 2 (by decide)) (.cons (.bool true) .nil))
def afterCopy (world : Solidity.Source.St Old.env) : RawFrame.State Old.unsignedCtx :=
 RawDeclarationFrame.ofSnapshot
  ⟨.cons (.int 255 boundU) changed,LocalValues.ofClean (.cons (.int 255 boundU) changed),world⟩
def statement : Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.unsignedCtx.tys :=
 .declInit (τ := .int Solidity.Source.IntTy.u8) (.const (Solidity.Source.Q.ofInt 255))
  (RawIntegerInitialization.admissible Old.env Solidity.Source.IntTy.u8 255 boundU)
def witness : Nonempty (RawFrame.State Old.signedCtx) :=
 ⟨nextSigned (Solidity.Source.St.init Old.env)⟩

theorem unsignedActual : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedInteger.Old.env), Solidity.Yul.RawPreparedInteger.run "n" Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawPreparedInteger.boundU 2 (Solidity.Yul.Checks.RawPreparedInteger.Old.canonical world) = .inr (Solidity.Yul.Checks.RawPreparedInteger.nextUnsigned world) := by
  intro world
  rfl

theorem signedActual : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedInteger.Old.env), Solidity.Yul.RawPreparedInteger.run "n" Solidity.Yul.Checks.RawPreparedInteger.Old.signed8 (-128) Solidity.Yul.Checks.RawPreparedInteger.boundS 2 (Solidity.Yul.Checks.RawPreparedInteger.Old.canonical world) = .inr (Solidity.Yul.Checks.RawPreparedInteger.nextSigned world) := by
  intro world
  rfl

theorem unsignedCoherent : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedInteger.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawPreparedInteger.nextUnsigned world) = true := by
  intro world
  exact (RawCoherent.coherent_iff _).mpr rfl

theorem signedWord : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedInteger.Old.env), (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawPreparedInteger.nextSigned world) Solidity.Yul.Checks.RawPreparedInteger.Old.signedCell).val = 2^256-128 := by
  intro world
  rfl

theorem unsignedWord : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedInteger.Old.env), (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawPreparedInteger.nextUnsigned world) Solidity.Yul.Checks.RawPreparedInteger.Old.newCell).val = 255 := by
  intro world
  rfl

theorem dirtyBits : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedInteger.Old.env), match Solidity.Yul.RawPreparedInteger.run "n" Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawPreparedInteger.boundU 2 (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) with
 | .inl _ => False
 | .inr next => (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawPreparedInteger.Old.newCell).val = 255 ∧
   (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawPreparedInteger.Old.grownX).val = 2 ∧
   (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawPreparedInteger.Old.grownArg).val = 257 ∧
   (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawPreparedInteger.Old.grownFlag).val = 2 ∧ next.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem dirtyRefuses : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedInteger.Old.env), match Solidity.Yul.RawPreparedInteger.run "n" Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawPreparedInteger.boundU 2 (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) with
 | .inl _ => False
 | .inr next => Solidity.Yul.RawCoherent.coherent next = false := by
  intro world
  rfl

theorem timeouts : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedInteger.Old.env), Solidity.Yul.RawPreparedInteger.run "n" Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawPreparedInteger.boundU 0 (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) = .inl (.timeout,Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) ∧
 Solidity.Yul.RawPreparedInteger.run "n" Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawPreparedInteger.boundU 1 (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) = .inl (.timeout,Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) := by
  intro world
  exact ⟨rfl,rfl⟩

theorem rangeRefusals : ¬ (Solidity.Source.IntTy.u8.lo ≤ (256 : Int) ∧ (256 : Int) ≤ Solidity.Source.IntTy.u8.hi) ∧
 ¬ (Solidity.Source.IntTy.u8.lo ≤ (-1 : Int) ∧ (-1 : Int) ≤ Solidity.Source.IntTy.u8.hi) ∧
 ¬ (Solidity.Yul.Checks.RawPreparedInteger.Old.signed8.lo ≤ (-129 : Int) ∧ (-129 : Int) ≤ Solidity.Yul.Checks.RawPreparedInteger.Old.signed8.hi) ∧
 ¬ (Solidity.Yul.Checks.RawPreparedInteger.Old.signed8.lo ≤ (128 : Int) ∧ (128 : Int) ≤ Solidity.Yul.Checks.RawPreparedInteger.Old.signed8.hi) := by
  decide

theorem consumer : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedInteger.Old.env),
 Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawPreparedInteger.copyProof pipeline 3 (Solidity.Yul.Checks.RawPreparedInteger.nextUnsigned world) =
 (.ok (),Solidity.Yul.Checks.RawPreparedInteger.afterCopy world) := by
  intro pipeline world
  rfl

theorem consumerScope : ∀ (pipeline : Solidity.Roadmap.Pipeline) (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedInteger.Old.env),
 Solidity.Yul.RawTypedScope.drop (Solidity.Yul.RawU8Statement.run Solidity.Yul.Checks.RawPreparedInteger.copyProof pipeline 3 (Solidity.Yul.Checks.RawPreparedInteger.nextUnsigned world)).2 =
 Solidity.Yul.Checks.RawPreparedInteger.Old.captured Solidity.Yul.Checks.RawPreparedInteger.changed world := by
  intro pipeline world
  rw [consumer]
  rfl

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawPreparedInteger.Old.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawPreparedInteger.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedInteger.Old.env),
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawPreparedInteger.statement Solidity.Yul.Checks.RawPreparedInteger.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawPreparedInteger.Old.env,world) = Solidity.Yul.RawPreparedInteger.project
 (Solidity.Yul.RawPreparedInteger.run "n" Solidity.Source.IntTy.u8 255 Solidity.Yul.Checks.RawPreparedInteger.boundU fuel (Solidity.Yul.Checks.RawPreparedInteger.Old.canonical world)) := by
  intro glob frame fuel nps ph world
  exact RawPreparedInteger.source_correct Old.ctx "n" Solidity.Source.IntTy.u8 255 boundU [] false ⟨true,false⟩ glob frame fuel nps ph (Old.canonical world)

theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawPreparedInteger.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawPreparedInteger.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedInteger.Old.env),
 (Solidity.Source.execS glob frame 2 nps ph Solidity.Yul.Checks.RawPreparedInteger.statement Solidity.Yul.Checks.RawPreparedInteger.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawPreparedInteger.Old.env,world) =
 (.ok (.normal (.cons (.int 255 Solidity.Yul.Checks.RawPreparedInteger.boundU) Solidity.Yul.Checks.RawPreparedInteger.Old.clean)),(Solidity.Source.L0 Solidity.Yul.Checks.RawPreparedInteger.Old.env,world)) := by
  intro glob frame nps ph world
  rw [sourceAll, unsignedActual]
  rfl
end Solidity.Yul.Checks.RawPreparedInteger

#print axioms Solidity.Yul.RawPreparedInteger.run_zero
#print axioms Solidity.Yul.RawPreparedInteger.run_one
#print axioms Solidity.Yul.RawPreparedInteger.run_success
#print axioms Solidity.Yul.RawPreparedInteger.coherent_result
#print axioms Solidity.Yul.RawPreparedInteger.source_correct
#print axioms Solidity.Yul.Checks.RawPreparedInteger.unsignedActual
#print axioms Solidity.Yul.Checks.RawPreparedInteger.signedActual
#print axioms Solidity.Yul.Checks.RawPreparedInteger.unsignedCoherent
#print axioms Solidity.Yul.Checks.RawPreparedInteger.signedWord
#print axioms Solidity.Yul.Checks.RawPreparedInteger.unsignedWord
#print axioms Solidity.Yul.Checks.RawPreparedInteger.dirtyBits
#print axioms Solidity.Yul.Checks.RawPreparedInteger.dirtyRefuses
#print axioms Solidity.Yul.Checks.RawPreparedInteger.timeouts
#print axioms Solidity.Yul.Checks.RawPreparedInteger.rangeRefusals
#print axioms Solidity.Yul.Checks.RawPreparedInteger.consumer
#print axioms Solidity.Yul.Checks.RawPreparedInteger.consumerScope
#print axioms Solidity.Yul.Checks.RawPreparedInteger.sourceAll
#print axioms Solidity.Yul.Checks.RawPreparedInteger.sourceCompletes
