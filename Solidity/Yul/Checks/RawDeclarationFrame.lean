import Solidity.Yul.RawDeclarationFrame
import Solidity.Yul.Checks.RawCheckedInitializedForPost
/-! Kernel-only raw declaration growth witnesses. Older dirty bits are retained;
stored clean projection is separate. No dirty-read or frontend admission claim. -/
namespace Solidity.Yul.Checks.RawDeclarationFrame
namespace Old
export Solidity.Yul.Checks.RawCheckedInitializedForPost.Old (ctx env initial clean)
end Old
def grown := Old.ctx.push "tmp" .bool
def tmp : WordCell (localExternalTypes grown) := .scalar ⟨.boolean,.here⟩
def x : WordCell (localExternalTypes grown) := .scalar ⟨.unsigned 0,.there .here⟩
def arg : WordCell (localExternalTypes grown) := .scalar ⟨.unsigned 0,.there (.there .here)⟩
def flag : WordCell (localExternalTypes grown) := .scalar ⟨.boolean,.there (.there (.there .here))⟩
def declaration : Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys grown.tys :=
 .declInit (.bool true) (by rfl)
def witness : Nonempty (Solidity.Source.RStmt Old.env [] false ⟨true,false⟩ Old.ctx.tys grown.tys) := ⟨declaration⟩
end Solidity.Yul.Checks.RawDeclarationFrame

namespace Solidity.Yul.Checks.RawDeclarationFrame
theorem dirtyTrue : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawDeclarationFrame.Old.env),match Solidity.Yul.RawDeclarationFrame.run "tmp" true 2 (Solidity.Yul.Checks.RawDeclarationFrame.Old.initial 2 257 2 world) with | .inl _ => False | .inr next => (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawDeclarationFrame.tmp).val = 1 ∧ (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawDeclarationFrame.x).val = 2 ∧ (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawDeclarationFrame.arg).val = 257 ∧ (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawDeclarationFrame.flag).val = 2 ∧ next.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem dirtyFalse : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawDeclarationFrame.Old.env),match Solidity.Yul.RawDeclarationFrame.run "tmp" false 2 (Solidity.Yul.Checks.RawDeclarationFrame.Old.initial 2 257 2 world) with | .inl _ => False | .inr next => (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawDeclarationFrame.tmp).val = 0 ∧ (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawDeclarationFrame.x).val = 2 ∧ (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawDeclarationFrame.arg).val = 257 ∧ (Solidity.Yul.RawFrame.view next Solidity.Yul.Checks.RawDeclarationFrame.flag).val = 2 ∧ next.world = world := by
  intro world
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem cleanBackup : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawDeclarationFrame.Old.env),match Solidity.Yul.RawDeclarationFrame.run "tmp" true 2 (Solidity.Yul.Checks.RawDeclarationFrame.Old.initial 2 257 2 world) with | .inl _ => False | .inr next => next.clean = Solidity.Source.Locals.cons (.bool true) Solidity.Yul.Checks.RawDeclarationFrame.Old.clean := by
  intro world
  rfl

theorem coherenceRefuses : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawDeclarationFrame.Old.env),match Solidity.Yul.RawDeclarationFrame.run "tmp" true 2 (Solidity.Yul.Checks.RawDeclarationFrame.Old.initial 2 257 2 world) with | .inl _ => False | .inr next => Solidity.Yul.RawCoherent.coherent next ≠ true := by
  intro world
  change false ≠ true
  decide

theorem timeoutRetains : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.RawDeclarationFrame.Old.env),Solidity.Yul.RawDeclarationFrame.run "tmp" true 0 (Solidity.Yul.Checks.RawDeclarationFrame.Old.initial 2 257 2 world) =
 .inl (.timeout,Solidity.Yul.Checks.RawDeclarationFrame.Old.initial 2 257 2 world) ∧
 Solidity.Yul.RawDeclarationFrame.run "tmp" true 1 (Solidity.Yul.Checks.RawDeclarationFrame.Old.initial 2 257 2 world) =
 .inl (.timeout,Solidity.Yul.Checks.RawDeclarationFrame.Old.initial 2 257 2 world) := by
  intro world
  exact ⟨rfl,rfl⟩

theorem sourceAll : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawDeclarationFrame.Old.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawDeclarationFrame.Old.env))
 (world : Solidity.Source.St Solidity.Yul.Checks.RawDeclarationFrame.Old.env),
 (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawDeclarationFrame.declaration Solidity.Yul.Checks.RawDeclarationFrame.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawDeclarationFrame.Old.env,world) =
 Solidity.Yul.RawDeclarationFrame.project (Solidity.Yul.RawDeclarationFrame.run "tmp" true fuel (Solidity.Yul.Checks.RawDeclarationFrame.Old.initial 2 257 2 world)) := by
  intro glob frame fuel nps ph world
  exact Solidity.Yul.RawDeclarationFrame.source_correct Old.ctx "tmp" true [] false ⟨true,false⟩
    glob frame fuel nps ph (Old.initial 2 257 2 world)

theorem sourceCompletes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawDeclarationFrame.Old.env) (frame : Solidity.Source.Fr)
 (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawDeclarationFrame.Old.env))
 (world : Solidity.Source.St Solidity.Yul.Checks.RawDeclarationFrame.Old.env),
 (Solidity.Source.execS glob frame 2 nps ph Solidity.Yul.Checks.RawDeclarationFrame.declaration Solidity.Yul.Checks.RawDeclarationFrame.Old.clean).run
 (Solidity.Source.L0 Solidity.Yul.Checks.RawDeclarationFrame.Old.env,world) =
 (.ok (.normal (.cons (.bool true) Solidity.Yul.Checks.RawDeclarationFrame.Old.clean)),(Solidity.Source.L0 Solidity.Yul.Checks.RawDeclarationFrame.Old.env,world)) := by
  intro glob frame nps ph world
  rfl

end Solidity.Yul.Checks.RawDeclarationFrame
#print axioms Solidity.Yul.RawDeclarationFrame.view_snapshot
#print axioms Solidity.Yul.RawDeclarationFrame.clean_snapshot
#print axioms Solidity.Yul.RawDeclarationFrame.world_snapshot
#print axioms Solidity.Yul.RawDeclarationFrame.frame_roundtrip
#print axioms Solidity.Yul.RawDeclarationFrame.coherent_iff
#print axioms Solidity.Yul.RawDeclarationFrame.run_zero
#print axioms Solidity.Yul.RawDeclarationFrame.run_one
#print axioms Solidity.Yul.RawDeclarationFrame.run_success
#print axioms Solidity.Yul.RawDeclarationFrame.source_correct
#print axioms Solidity.Yul.Checks.RawDeclarationFrame.dirtyTrue
#print axioms Solidity.Yul.Checks.RawDeclarationFrame.dirtyFalse
#print axioms Solidity.Yul.Checks.RawDeclarationFrame.cleanBackup
#print axioms Solidity.Yul.Checks.RawDeclarationFrame.coherenceRefuses
#print axioms Solidity.Yul.Checks.RawDeclarationFrame.timeoutRetains
#print axioms Solidity.Yul.Checks.RawDeclarationFrame.sourceAll
#print axioms Solidity.Yul.Checks.RawDeclarationFrame.sourceCompletes
