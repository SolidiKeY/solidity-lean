import Solidity.Yul.RawPreparedDeclaration
import Solidity.Yul.Checks.RawDeclarationFrame
/-! Kernel controls for exact-word prepared declarations and a concrete checked
consumer in the grown context. Declaration/body laws are separate; this is not
whole growing-loop or frontend admission. -/
namespace Solidity.Yul.Checks.RawPreparedDeclaration
namespace Old
export Solidity.Yul.Checks.RawDeclarationFrame.Old (ctx env initial clean)
export Solidity.Yul.Checks.RawDeclarationFrame (grown tmp x arg flag declaration)
end Old
def canonical (world : Solidity.Source.St Old.env) : RawFrame.State Old.ctx :=
 Old.initial 1 2 1 world
def next (world : Solidity.Source.St Old.env) : RawFrame.State Old.grown :=
 RawDeclarationFrame.ofSnapshot
  ⟨.cons (.bool true) (canonical world).clean,
   (.clean (.bool true),(RawCoherent.prepare (canonical world)).1),world⟩
def test : LocalBoolControl.Supported Old.env Old.grown.tys (.local .here) := .base (.local .here)
def breakBody : RawCheckedAdapter.Adapter Old.grown [] false false .brk :=
 Solidity.Yul.RawCheckedAdapter.fromAdapter (RawSourceAdapter.body .break_)
def loop := Solidity.Yul.RawCheckedAdapterLoop.loop test breakBody
def witness : Nonempty (RawCheckedAdapter.Adapter Old.grown [] false false
 (.whileLoop (l := true) (.local .here) .brk)) := ⟨loop⟩
end Solidity.Yul.Checks.RawPreparedDeclaration

namespace Solidity.Yul.Checks.RawPreparedDeclaration
theorem canonicalCoherent : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedDeclaration.Old.env),Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawPreparedDeclaration.canonical world) = true := by
  intro world
  rfl

theorem nextActual : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedDeclaration.Old.env),Solidity.Yul.RawPreparedDeclaration.run "tmp" true 2 (Solidity.Yul.Checks.RawPreparedDeclaration.canonical world) = .inr (Solidity.Yul.Checks.RawPreparedDeclaration.next world) := by
  intro world
  rfl

theorem nextCoherent : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedDeclaration.Old.env),Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawPreparedDeclaration.next world) = true := by
  intro world
  exact Solidity.Yul.RawPreparedDeclaration.coherent_result Old.ctx "tmp" true 2
    (canonical world) (canonicalCoherent world)

theorem canonicalWords : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedDeclaration.Old.env),match Solidity.Yul.RawPreparedDeclaration.run "tmp" true 2 (Solidity.Yul.Checks.RawPreparedDeclaration.canonical world) with
 | .inl _ => False
 | .inr state => (Solidity.Yul.RawFrame.view state Solidity.Yul.Checks.RawPreparedDeclaration.Old.tmp).val = 1 ∧
   (Solidity.Yul.RawFrame.view state Solidity.Yul.Checks.RawPreparedDeclaration.Old.x).val = 1 ∧
   (Solidity.Yul.RawFrame.view state Solidity.Yul.Checks.RawPreparedDeclaration.Old.arg).val = 2 ∧
   (Solidity.Yul.RawFrame.view state Solidity.Yul.Checks.RawPreparedDeclaration.Old.flag).val = 1 ∧ state.world = world := by
  intro world
  rw [nextActual]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem dirtyAll : ∀ (fuel : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedDeclaration.Old.env),
 Solidity.Yul.RawPreparedDeclaration.run "tmp" true fuel (Solidity.Yul.Checks.RawPreparedDeclaration.Old.initial 2 257 2 world) = Solidity.Yul.RawDeclarationFrame.run "tmp" true fuel (Solidity.Yul.Checks.RawPreparedDeclaration.Old.initial 2 257 2 world) := by
  intro fuel world
  exact Solidity.Yul.RawPreparedDeclaration.dirty_agrees Old.ctx "tmp" true fuel
    (Old.initial 2 257 2 world) (Solidity.Yul.Checks.RawCheckedAdapterLoop.dirtyBoundary world)

theorem dirtyBits : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedDeclaration.Old.env),match Solidity.Yul.RawPreparedDeclaration.run "tmp" true 2 (Solidity.Yul.Checks.RawPreparedDeclaration.Old.initial 2 257 2 world) with
 | .inl _ => False
 | .inr state => (Solidity.Yul.RawFrame.view state Solidity.Yul.Checks.RawPreparedDeclaration.Old.tmp).val = 1 ∧
   (Solidity.Yul.RawFrame.view state Solidity.Yul.Checks.RawPreparedDeclaration.Old.x).val = 2 ∧
   (Solidity.Yul.RawFrame.view state Solidity.Yul.Checks.RawPreparedDeclaration.Old.arg).val = 257 ∧
   (Solidity.Yul.RawFrame.view state Solidity.Yul.Checks.RawPreparedDeclaration.Old.flag).val = 2 ∧ state.world = world := by
  intro world
  rw [dirtyAll]
  exact Solidity.Yul.Checks.RawDeclarationFrame.dirtyTrue world

theorem dirtyRefuses : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedDeclaration.Old.env),match Solidity.Yul.RawPreparedDeclaration.run "tmp" true 2 (Solidity.Yul.Checks.RawPreparedDeclaration.Old.initial 2 257 2 world) with
 | .inl _ => False | .inr state => Solidity.Yul.RawCoherent.coherent state ≠ true := by
  intro world
  rw [dirtyAll]
  exact Solidity.Yul.Checks.RawDeclarationFrame.coherenceRefuses world

theorem timeoutRetains : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedDeclaration.Old.env),Solidity.Yul.RawPreparedDeclaration.run "tmp" true 0 (Solidity.Yul.Checks.RawPreparedDeclaration.canonical world) = .inl (.timeout,Solidity.Yul.Checks.RawPreparedDeclaration.canonical world) ∧
 Solidity.Yul.RawPreparedDeclaration.run "tmp" true 1 (Solidity.Yul.Checks.RawPreparedDeclaration.canonical world) = .inl (.timeout,Solidity.Yul.Checks.RawPreparedDeclaration.canonical world) := by
  intro world
  exact ⟨rfl,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawPreparedDeclaration.Old.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawPreparedDeclaration.Old.env))
 (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedDeclaration.Old.env),
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawPreparedDeclaration.Old.declaration Solidity.Yul.Checks.RawPreparedDeclaration.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawPreparedDeclaration.Old.env,world) =
 Solidity.Yul.RawDeclarationFrame.project (Solidity.Yul.RawPreparedDeclaration.run "tmp" true fuel (Solidity.Yul.Checks.RawPreparedDeclaration.canonical world)) := by
  intro glob frame fuel nps ph world
  exact Solidity.Yul.RawPreparedDeclaration.source_correct Old.ctx "tmp" true [] false ⟨true,false⟩
    glob frame fuel nps ph (canonical world)

theorem consumerSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawPreparedDeclaration.Old.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawPreparedDeclaration.Old.env))
 (world : Solidity.Source.St Solidity.Yul.Checks.RawPreparedDeclaration.Old.env),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawPreparedDeclaration.loop.run glob.pipeline fuel (Solidity.Yul.Checks.RawPreparedDeclaration.next world)).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
 (Solidity.Source.RStmt.whileLoop (R := []) (M := false) (u := false) (l := true)
 (.local (.here : Solidity.Source.Idx Solidity.Yul.Checks.RawPreparedDeclaration.Old.grown.tys .bool)) .brk) (Solidity.Yul.Checks.RawPreparedDeclaration.next world).clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawPreparedDeclaration.Old.env,world) =
 Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawPreparedDeclaration.loop.run glob.pipeline fuel (Solidity.Yul.Checks.RawPreparedDeclaration.next world)) := by
  intro glob frame checked fuel nps ph world
  exact loop.correct glob frame checked fuel nps ph (next world) (nextCoherent world)

end Solidity.Yul.Checks.RawPreparedDeclaration
#print axioms Solidity.Yul.RawPreparedDeclaration.input_words
#print axioms Solidity.Yul.RawPreparedDeclaration.run_zero
#print axioms Solidity.Yul.RawPreparedDeclaration.run_one
#print axioms Solidity.Yul.RawPreparedDeclaration.run_success
#print axioms Solidity.Yul.RawPreparedDeclaration.coherent_result
#print axioms Solidity.Yul.RawPreparedDeclaration.source_correct
#print axioms Solidity.Yul.RawPreparedDeclaration.dirty_agrees
#print axioms Solidity.Yul.Checks.RawPreparedDeclaration.canonicalCoherent
#print axioms Solidity.Yul.Checks.RawPreparedDeclaration.nextActual
#print axioms Solidity.Yul.Checks.RawPreparedDeclaration.nextCoherent
#print axioms Solidity.Yul.Checks.RawPreparedDeclaration.canonicalWords
#print axioms Solidity.Yul.Checks.RawPreparedDeclaration.dirtyAll
#print axioms Solidity.Yul.Checks.RawPreparedDeclaration.dirtyBits
#print axioms Solidity.Yul.Checks.RawPreparedDeclaration.dirtyRefuses
#print axioms Solidity.Yul.Checks.RawPreparedDeclaration.timeoutRetains
#print axioms Solidity.Yul.Checks.RawPreparedDeclaration.sourceAll
#print axioms Solidity.Yul.Checks.RawPreparedDeclaration.consumerSource
