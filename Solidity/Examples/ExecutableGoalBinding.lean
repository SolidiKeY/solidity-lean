import Solidity.Tools.ExecutableGoalBinding
import Solidity.Frontend.ExecutableAst.Shared.ObligationCapture

/-! # Executable goal-binding examples

Checks exact-target refutation, true-target refusal, retained-value identity,
argument identity and storage-layout rebinding. The compact contracts below
are structural examples; they do not certify compiler output or source locations.
-/
open Lean Elab Command Meta Solidity Solidity.Tools
namespace ExecutableBindingControls

def C : Contract := { vars := [] }
def candidate : Cand C := { st := .nil, args := [] }
def pair : GoalPair := ⟨C, C, .ff, .ff⟩
def same : SameCandidate pair :=
  ⟨candidate, candidate, HEq.rfl, rfl, rfl, rfl, rfl⟩
def failure : SelectedFailure pair := ⟨same, rfl, rfl⟩
theorem exactTarget : ¬ Fml.Valid pair.executableFormula := failure.refuted

def truePair : GoalPair := ⟨C, C, .ff, .tt⟩
theorem trueTargetRefused (w : SelectedFailure truePair) : False := by
  have h := w.executableFailure
  change Tri.tt = Tri.ff at h
  cases h

theorem wrongValuesRefused :
    ¬ RetainedValuesBinding C candidate [(Var.user "foreign", .bool true)] := by
  intro h
  have e := h.sourceValues
  change [(Var.user "foreign", Semantics.CallValue.bool true)] = [] at e
  cases e

def foreignCandidate : Cand C := { candidate with args := [("foreign", .bool true)] }
theorem changedArgumentsRefused (r : SameCandidate pair)
    (hi : r.imported = candidate) (he : r.executable = foreignCandidate) : False := by
  have h := r.arguments
  rw [hi, he] at h
  change [] = [("foreign", Semantics.CallValue.bool true)] at h
  cases h

open Solidity.Frontend.ExecutableAst.Shared

/-- Injected callbacks for a structural builder test; not runtime callbacks. -/
def noLoops : BodyLoopLowerer := fun _ _ raw => pure raw
def noPre : PlainEntryPre := fun _ _ => .tt

example :
    (obligationCapture noLoops noPre C "missing" false false).map (fun r => r.formula) =
      .error "missing function" :=
  obligationCapture_forget noLoops noPre C "missing" false false

run_cmd do
  let emptyFunction : FunDecl := { params := [], body := [] }
  let executable : Contract := { vars := [], funs := [("noop", emptyFunction)] }
  match obligationCapture noLoops noPre executable "noop" false false with
  | .error reason => throwError "structural positive capture refused: {reason}"
  | .ok _ => logInfo "EXECUTABLE_BINDING actual builder positive capture confirmed (injected callbacks)"


#print axioms Solidity.Tools.RetainedValuesBinding.failure
#print axioms Solidity.Frontend.ExecutableAst.Shared.obligationCapture_forget
#print axioms Solidity.Tools.SelectedFailure.refuted
#print axioms ExecutableBindingControls.exactTarget
#print axioms ExecutableBindingControls.trueTargetRefused
#print axioms ExecutableBindingControls.wrongValuesRefused
#print axioms ExecutableBindingControls.changedArgumentsRefused


def layoutImported : Contract := { vars := [("x", .prim .uint), ("flag", .prim .bool)] }
def layoutExecutable : Contract :=
  { layoutImported with
    evalOrder := EvalOrder.viaIR
    funs := [("different", { params := [], body := [] })] }
def layoutCandidate : Cand layoutImported :=
  { st := .cons (.prim (PrimTy.ofIntD .uint 37)) (.cons (.prim true) .nil),
    args := [("flag", .bool true)],
    tx := { msgSender := PrimTy.ofIntD .uint 9, timestamp := PrimTy.ofIntD .uint 17 },
    net := [(PrimTy.ofIntD .uint 7, 16)], bal := PrimTy.ofIntD .uint 3 }
def layoutPair : GoalPair := ⟨layoutImported, layoutExecutable, .ff, .tt⟩
def layoutRelation : SameCandidate layoutPair :=
  SameCandidate.ofLayout layoutPair layoutCandidate rfl

theorem layoutCandidatePreserved :
    layoutRelation.imported = layoutCandidate ∧
    layoutRelation.executable.st = layoutCandidate.st ∧
    layoutRelation.executable.args = layoutCandidate.args ∧
    layoutRelation.executable.tx = layoutCandidate.tx ∧
    layoutRelation.executable.net = layoutCandidate.net ∧
    layoutRelation.executable.bal = layoutCandidate.bal :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wrongLayoutRefused (h : layoutImported.vars = C.vars) : False := by
  change [("x", Ty.prim PrimTy.uint), ("flag", Ty.prim PrimTy.bool)] = [] at h
  cases h

-- A same-candidate relation cannot supply the missing executable failure.
theorem layoutRelationDoesNotRefuteTrue (w : SelectedFailure layoutPair) : False := by
  have h := w.executableFailure
  change Tri.tt = Tri.ff at h
  cases h

run_cmd do
  for name in [``Cand.rebindLayout_storage, ``Cand.rebindLayout_argInts,
      ``Cand.rebindLayout_vals, ``SameCandidate.ofLayout_imported,
      ``layoutCandidatePreserved, ``wrongLayoutRefused, ``layoutRelationDoesNotRefuteTrue] do
    let axioms ← collectAxioms name
    unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "candidate layout control has nonstandard axioms"
    logInfo m!"EXECUTABLE_BINDING layout control axioms: {name}: {axioms}"


end ExecutableBindingControls
