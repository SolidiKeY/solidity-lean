import Solidity.Yul.RawControlDeclaration
import Solidity.Yul.Checks.RawGrowingForPost

/-! Nonliteral growing initializer controls. The left expression writes an older
Boolean; a later child can time out after that write. Raw local copies retain
dirty words, with no clean Source readback claim. -/
namespace Solidity.Yul.Checks.RawControlDeclaration
namespace Old
export Solidity.Yul.Checks.RawGrowingBlock.Old (ctx env grown initial clean canonical)
export Solidity.Yul.Checks.RawGrowingBlock (captured)
end Old

def flagIndex : Solidity.Source.Idx Old.ctx.tys .bool := .there (.there .here)
def expr : Solidity.Source.RExpr Old.env Old.ctx.tys .bool :=
 .binary .or (.assign (.local flagIndex) (.bool false))
   (.unary .not (.unary .not (.local flagIndex)))
def proof : LocalBoolControl.Supported Old.env Old.ctx.tys expr :=
 .or (.assign flagIndex (.base (.literal false)))
   (.not (.not (.base (.local flagIndex))))
def read : LocalBoolControl.Supported Old.env Old.ctx.tys (.local flagIndex) :=
 .base (.local flagIndex)
def changed : Solidity.Source.Locals Old.env.layout Old.ctx.tys :=
 .cons (.int 1 (by decide)) (.cons (.int 2 (by decide)) (.cons (.bool false) .nil))
def next (world : Solidity.Source.St Old.env) : RawFrame.State Old.grown :=
 Solidity.Yul.Checks.RawGrowingForPost.frame false changed world
def dirtyNext (world : Solidity.Source.St Old.env) : RawFrame.State Old.grown :=
 RawCoherent.capture (RawFrame.ofClean (.cons (.bool false) Old.clean) world)
  (((RawCoherent.prepare (Old.initial 2 257 2 world)).1.get flagIndex,
     (RawCoherent.prepare (Old.initial 2 257 2 world)).1),world)
def tmpCell : WordCell (localExternalTypes Old.grown) := .scalar ⟨.boolean,.here⟩
def argCell : WordCell (localExternalTypes Old.grown) :=
 .scalar ⟨.unsigned 0,.there (.there .here)⟩
def flagCell : WordCell (localExternalTypes Old.grown) :=
 .scalar ⟨.boolean,.there (.there (.there .here))⟩
def statement : Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys Old.grown.tys :=
 .declInit (τ := .bool) expr (by rfl)
def witness : Nonempty (LocalBoolControl.Supported Old.env Old.ctx.tys expr) := ⟨proof⟩
end Solidity.Yul.Checks.RawControlDeclaration

namespace Solidity.Yul.Checks.RawControlDeclaration
theorem normal : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlDeclaration.Old.env), Solidity.Yul.RawControlDeclaration.run "tmp" Solidity.Yul.Checks.RawControlDeclaration.proof 6 (Solidity.Yul.Checks.RawControlDeclaration.Old.canonical world) = .inr (Solidity.Yul.Checks.RawControlDeclaration.next world) := by
  intro world
  rfl

theorem «partial» : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlDeclaration.Old.env), Solidity.Yul.RawControlDeclaration.run "tmp" Solidity.Yul.Checks.RawControlDeclaration.proof 4 (Solidity.Yul.Checks.RawControlDeclaration.Old.canonical world) = .inl (.timeout,Solidity.Yul.Checks.RawControlDeclaration.Old.captured Solidity.Yul.Checks.RawControlDeclaration.changed world) := by
  intro world
  rfl

theorem zero : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlDeclaration.Old.env), Solidity.Yul.RawControlDeclaration.run "tmp" Solidity.Yul.Checks.RawControlDeclaration.proof 0 (Solidity.Yul.Checks.RawControlDeclaration.Old.canonical world) = .inl (.timeout,Solidity.Yul.Checks.RawControlDeclaration.Old.canonical world) := by
  intro world
  rfl

theorem one : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlDeclaration.Old.env), Solidity.Yul.RawControlDeclaration.run "tmp" Solidity.Yul.Checks.RawControlDeclaration.proof 1 (Solidity.Yul.Checks.RawControlDeclaration.Old.canonical world) = .inl (.timeout,Solidity.Yul.Checks.RawControlDeclaration.Old.captured Solidity.Yul.Checks.RawControlDeclaration.Old.clean world) := by
  intro world
  rfl

theorem dirtyActual : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlDeclaration.Old.env), Solidity.Yul.RawControlDeclaration.run "tmp" Solidity.Yul.Checks.RawControlDeclaration.read 3 (Solidity.Yul.Checks.RawControlDeclaration.Old.initial 2 257 2 world) = .inr (Solidity.Yul.Checks.RawControlDeclaration.dirtyNext world) := by
  intro world
  rfl

theorem dirtyBits : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlDeclaration.Old.env), (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawControlDeclaration.dirtyNext world) Solidity.Yul.Checks.RawControlDeclaration.tmpCell).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawControlDeclaration.dirtyNext world) Solidity.Yul.Checks.RawControlDeclaration.argCell).val = 257 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawControlDeclaration.dirtyNext world) Solidity.Yul.Checks.RawControlDeclaration.flagCell).val = 2 ∧ (Solidity.Yul.Checks.RawControlDeclaration.dirtyNext world).world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem dirtyRefuses : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlDeclaration.Old.env), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawControlDeclaration.dirtyNext world) = false := by
  intro world
  rfl

theorem scopeRetains : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawControlDeclaration.Old.env), Solidity.Yul.RawGrowingBlock.drop (Solidity.Yul.Checks.RawControlDeclaration.next world) = Solidity.Yul.Checks.RawControlDeclaration.Old.captured Solidity.Yul.Checks.RawControlDeclaration.changed world := by
  intro world
  exact Solidity.Yul.Checks.RawGrowingForPost.dropFrame false changed world

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlDeclaration.Old.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlDeclaration.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlDeclaration.Old.env),
 (match Solidity.Yul.RawControlDeclaration.run "tmp" Solidity.Yul.Checks.RawControlDeclaration.proof fuel (Solidity.Yul.Checks.RawControlDeclaration.Old.canonical world) with
 | .inl failure => Solidity.Yul.RawCoherent.coherent failure.2 = true
 | .inr next => Solidity.Yul.RawCoherent.coherent next = true) ∧
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawControlDeclaration.statement Solidity.Yul.Checks.RawControlDeclaration.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawControlDeclaration.Old.env,world) =
 Solidity.Yul.RawDeclarationFrame.project
   (Solidity.Yul.RawControlDeclaration.run "tmp" Solidity.Yul.Checks.RawControlDeclaration.proof fuel (Solidity.Yul.Checks.RawControlDeclaration.Old.canonical world)) := by
  intro glob frame fuel nps ph world
  have locals : (Old.canonical world).clean = Old.clean := by rfl
  have worldSame : (Old.canonical world).world = world := by rfl
  have law := Solidity.Yul.RawControlDeclaration.correct Old.ctx "tmp" expr proof [] false
    ⟨true,false⟩ glob frame fuel nps ph (Old.canonical world)
    (Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent world)
  constructor
  · cases actual : Solidity.Yul.RawControlDeclaration.run "tmp" proof fuel (Old.canonical world) with
    | inl failure =>
      rw [actual] at law
      exact law.1
    | inr next =>
      rw [actual] at law
      exact law.1
  · simpa only [statement,locals,worldSame] using law.2


theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlDeclaration.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlDeclaration.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlDeclaration.Old.env),
 (Solidity.Source.execS glob frame 6 nps ph Solidity.Yul.Checks.RawControlDeclaration.statement Solidity.Yul.Checks.RawControlDeclaration.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawControlDeclaration.Old.env,world) =
 (.ok (.normal (.cons (.bool false) Solidity.Yul.Checks.RawControlDeclaration.changed)),(Solidity.Source.L0 Solidity.Yul.Checks.RawControlDeclaration.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

theorem sourcePartial : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlDeclaration.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlDeclaration.Old.env)) (world : Solidity.Source.St Solidity.Yul.Checks.RawControlDeclaration.Old.env),
 (Solidity.Source.execS glob frame 4 nps ph Solidity.Yul.Checks.RawControlDeclaration.statement Solidity.Yul.Checks.RawControlDeclaration.Old.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawControlDeclaration.Old.env,world) =
 (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.RawControlDeclaration.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

end Solidity.Yul.Checks.RawControlDeclaration
#print axioms Solidity.Yul.RawControlDeclaration.correct
#print axioms Solidity.Yul.Checks.RawControlDeclaration.normal
#print axioms Solidity.Yul.Checks.RawControlDeclaration.«partial»
#print axioms Solidity.Yul.Checks.RawControlDeclaration.zero
#print axioms Solidity.Yul.Checks.RawControlDeclaration.one
#print axioms Solidity.Yul.Checks.RawControlDeclaration.dirtyActual
#print axioms Solidity.Yul.Checks.RawControlDeclaration.dirtyBits
#print axioms Solidity.Yul.Checks.RawControlDeclaration.dirtyRefuses
#print axioms Solidity.Yul.Checks.RawControlDeclaration.scopeRetains
#print axioms Solidity.Yul.Checks.RawControlDeclaration.sourceAll
#print axioms Solidity.Yul.Checks.RawControlDeclaration.sourceCompletes
#print axioms Solidity.Yul.Checks.RawControlDeclaration.sourcePartial
