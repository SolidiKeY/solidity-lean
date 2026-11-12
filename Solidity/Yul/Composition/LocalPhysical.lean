import Solidity.Yul.Composition.PhysicalFrames
import Solidity.Yul.LocalBlock

/-! Compatible actual Source boundary: represented physical action FIRST,
then the actual raw LOCAL pure runner ONLY after physical success. Raw outcomes are not old EMState values
and cannot be silently cleaned/resumed. The world/physical journals remain the
actual producer carriers; no Yul call or whole Source dispatch is invented. -/
namespace Solidity.Yul.Composition
open Solidity.Yul.Views
open Solidity.Roadmap (Address)

/-- Retains the complete physical result (including both journals and halt).
Executes the actual represented Source.applyOp before entering the actual
raw local runner, with the SAME Source context and complete resulting St. -/
def representedThenLocal (ctx : Source.Ctx)
    (ps ts : (a : Address) → List (ScalarPath ctx.env.layout (ctx.env.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState ctx.env ctx.tys)
    (r : ResidualJournal complementCarrierOwnership) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) :=
  let step := representedSourceStep ps ts q before F p s r
  (step,step.1.1.1.map (fun _ => runLocalBlock ctx code policy fuel (LocalState.ofClean step.1.1.2)))

/-- Every horizon observes the ENTIRE raw word state and legal control, not
just a selected scalar. This is not dirty ordinary-Source evaluation. -/
theorem represented_local_projection (ctx : Source.Ctx)
    (ps ts : (a : Address) → List (ScalarPath ctx.env.layout (ctx.env.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState ctx.env ctx.tys)
    (r : ResidualJournal complementCarrierOwnership) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) :
    (representedThenLocal ctx ps ts q before F p s r code policy fuel).2.map (fun result => result.map LocalBlockOutcome.project) =
      (representedSourceStep ps ts q before F p s r).1.1.1.map (fun _ => WordAdapter.run code policy fuel ⟨Fin.elim0,localWordCells ctx
        (LocalValues.ofClean (representedSourceStep ps ts q before F p s r).1.1.2.1)⟩) := by
  unfold representedThenLocal
  dsimp only
  cases result : (representedSourceStep ps ts q before F p s r).1.1.1 with
  | error reason => simp only [result,Except.map]
  | ok value =>
      simp only [result,Except.map]
      exact congrArg Except.ok (runLocalBlock_projection ctx code policy fuel _)

/-- Completion retains the complete actual Source.St of the physical phase. -/
theorem represented_local_source (ctx : Source.Ctx)
    (ps ts : (a : Address) → List (ScalarPath ctx.env.layout (ctx.env.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState ctx.env ctx.tys)
    (r : ResidualJournal complementCarrierOwnership) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) {result}
    (done : (representedThenLocal ctx ps ts q before F p s r code policy fuel).2 = .ok (some result)) :
    result.state.2 = (representedSourceStep ps ts q before F p s r).1.1.2.2 := by
  cases outcome : (representedSourceStep ps ts q before F p s r).1.1.1 with
  | error reason =>
      simp only [representedThenLocal,outcome,Except.map] at done
      cases done
  | ok value =>
      have finished : runLocalBlock ctx code policy fuel
          (LocalState.ofClean (representedSourceStep ps ts q before F p s r).1.1.2) = some result := by
        simpa only [representedThenLocal,outcome,Except.map,Except.ok.injEq] using done
      exact runLocalBlock_world ctx code policy fuel _ finished

/-- Changing ONLY St rebases the actual completed result while preserving raw
LocalValues and control exactly, including exhaustion at every horizon.
It does not establish literal identity with old clean LocalValues. -/
theorem local_rebase (ctx : Source.Ctx) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) (locals : LocalValues ctx.env ctx.tys) (first last : Source.St ctx.env) :
    runLocalBlock ctx code policy fuel (locals,last) =
      (runLocalBlock ctx code policy fuel (locals,first)).map
        (fun result => ⟨(result.state.1,last),result.flow⟩) := by
  unfold runLocalBlock
  cases WordAdapter.run code policy fuel ⟨Fin.elim0,localWordCells ctx locals⟩ <;> rfl

/-- Nonword locals are not overwritten by complete raw-cell writeback. -/
theorem represented_local_nonword (ctx : Source.Ctx)
    (ps ts : (a : Address) → List (ScalarPath ctx.env.layout (ctx.env.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState ctx.env ctx.tys)
    (r : ResidualJournal complementCarrierOwnership) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) {result}
    (done : (representedThenLocal ctx ps ts q before F p s r code policy fuel).2 = .ok (some result))
    (ref : SourceLocalRef ctx) {kind} (shape : DeclaredSourceTypeD ctx.env ref.ty kind)
    (zero : wordCellWidth kind = 0) :
    result.state.1.get ref.index =
      (LocalValues.ofClean (representedSourceStep ps ts q before F p s r).1.1.2.1).get ref.index := by
  cases outcome : (representedSourceStep ps ts q before F p s r).1.1.1 with
  | error reason =>
      simp only [representedThenLocal,outcome,Except.map] at done
      cases done
  | ok value =>
      have finished : runLocalBlock ctx code policy fuel
          (LocalState.ofClean (representedSourceStep ps ts q before F p s r).1.1.2) = some result := by
        simpa only [representedThenLocal,outcome,Except.map,Except.ok.injEq] using done
      exact runLocalBlock_nonword ctx code policy fuel _ finished ref shape zero

/-- A static physical error halts before ANY local execution, at every fuel;
source and BOTH physical journals remain the exact original values. -/
theorem represented_local_static (ctx : Source.Ctx)
    (ps ts : (a : Address) → List (ScalarPath ctx.env.layout (ctx.env.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before) (s : Source.EMState ctx.env ctx.tys)
    (r : ResidualJournal complementCarrierOwnership) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) (static : F.static = true) :
    representedThenLocal ctx ps ts q before F p s r code policy fuel =
      ((((.error (.revert []),s),r),before),.error (.revert [])) := by
  unfold representedThenLocal
  rw [representedSourceStep_static F p s r static]
  rfl

#print axioms represented_local_static
#print axioms represented_local_projection
#print axioms represented_local_source
#print axioms local_rebase
#print axioms represented_local_nonword
end Solidity.Yul.Composition
