import Solidity.Yul.Compilation.SourceLoop
/-! Inversion of ACTUAL original source completions for the existing normal
loop compiler slice. Finite guards/count are derived, not assumed. Component
certificates retain their real total-normal source laws. No new source evaluator
or Source/G24, early-control, native/resource or divergence adequacy is supplied. -/
namespace Solidity.Yul.Compilation.SourceLoopCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions SourceLoop

variable {c : Solidity.Yul.Control} {n fc fp fb : Nat}
 {test : Solidity.Yul.Expr [] [] n 1}
 {step : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
 {work : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}

theorem repeat_shift {α : Type} (f : α → α) (count : Nat) (a : α) :
 Nat.repeat f count (f a) = Nat.repeat f (count+1) a := by
 induction count with
 | zero => rfl
 | succ count ih => exact congrArg f ih

/-- Any completed source horizon, even below a component certificate's own
horizon, recovers the same real finite normal iteration sequence. Existing
completion uniqueness identifies the actual intermediate values and flows. -/
theorem completed (condition : Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (fuel : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalLoop fuel .nil True.intro test condition.profile step post.profile work body.profile
   (sourceLocals locals) = some result) :
 ∃ count, (∀ j, j < count → condition.value (Nat.repeat (next body post) j locals) ≠ 0) ∧
 condition.value (Nat.repeat (next body post) count locals) = 0 ∧
 result = ⟨sourceLocals (Nat.repeat (next body post) count locals),.normal⟩ := by
 induction fuel generalizing locals result with
 | zero => cases ran
 | succ fuel ih =>
   rewrite [evalLoop] at ran
   obtain ⟨values,tested,after⟩ := Option.bind_eq_some_iff.mp ran
   have same : values = (fun _ => (condition.value locals).toFin) :=
    evalExpr_completed_unique .nil True.intro test condition.profile (sourceLocals locals)
     tested (condition.source locals)
   subst values
   change (if (condition.value locals).toNat = 0 then _ else _) = some result at after
   by_cases zero : condition.value locals = 0
   · have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
     rewrite [if_pos zn] at after
     refine ⟨0,?_,zero,(Option.some.inj after).symm⟩
     intro j bound
     omega
   · have nz : (condition.value locals).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
     rewrite [if_neg nz] at after
     obtain ⟨afterBody,worked,continued⟩ := Option.bind_eq_some_iff.mp after
     change evalStmt fuel .nil True.intro work body.profile (sourceLocals locals) = some afterBody at worked
     have same : afterBody = ⟨sourceLocals (body.update locals),.normal⟩ :=
      evalStmt_completed_unique .nil True.intro work body.profile (sourceLocals locals)
       worked (body.source locals)
     subst afterBody
     change Option.bind (applyStmtRun (evalStmtNode fuel step) .nil True.intro post.profile
       (sourceLocals (body.update locals))) _ = some result at continued
     obtain ⟨afterPost,stepped,remaining⟩ := Option.bind_eq_some_iff.mp continued
     change evalStmt fuel .nil True.intro step post.profile (sourceLocals (body.update locals)) = some afterPost at stepped
     have same : afterPost = ⟨sourceLocals (next body post locals),.normal⟩ :=
      evalStmt_completed_unique .nil True.intro step post.profile (sourceLocals (body.update locals))
       stepped (post.source (body.update locals))
     subst afterPost
     change evalLoop fuel .nil True.intro test condition.profile step post.profile work body.profile
       (sourceLocals (next body post locals)) = some result at remaining
     obtain ⟨count,running,stopped,final⟩ := ih (next body post locals) result remaining
     refine ⟨count+1,?_,?_,?_⟩
     · intro j bound
       cases j with
       | zero => exact zero
       | succ j => simpa only [repeat_shift] using running j (by omega)
     · simpa only [repeat_shift] using stopped
     · simpa only [repeat_shift] using final

/-- A completed original skip-initialized for supplies its finite guard/count
witness; no syntactic termination test or chosen source horizon is required. -/
theorem for_completed (condition : Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (fuel : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt fuel .nil True.intro (Solidity.Yul.Stmt.for_ (c := c) .skip test step work)
  ⟨True.intro,condition.profile,post.profile,body.profile⟩ (sourceLocals locals) = some result) :
 ∃ count, (∀ j, j < count → condition.value (Nat.repeat (next body post) j locals) ≠ 0) ∧
 condition.value (Nat.repeat (next body post) count locals) = 0 ∧
 result = ⟨sourceLocals (Nat.repeat (next body post) count locals),.normal⟩ := by
 cases fuel with
 | zero => cases ran
 | succ fuel =>
   cases fuel with
   | zero => cases ran
   | succ fuel =>
     rewrite [SourceLoop.for_skip fuel condition post body] at ran
     exact completed condition post body (fuel+1) locals result ran

/-- Actual completion at ANY original horizon compiles to the actual emitted
model artifact. Neither a finite turn count, guard sequence nor target run is
an input premise. This is the existing normal-component slice only. -/
theorem source_to_model (condition : Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : SourceLoop.emit condition post body depth = some block)
 (selected : WordControl.blockCode block = some code)
 (fuel : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt fuel .nil True.intro (Solidity.Yul.Stmt.for_ (c := c) .skip test step work)
  ⟨True.intro,condition.profile,post.profile,body.profile⟩ (sourceLocals locals) = some result)
 (newer : Vector Scalar.Word depth) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ final : Vector Scalar.Word n, result = ⟨sourceLocals final,.normal⟩ ∧
 Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := (newer.toList++final.toList).map coreWord++caller} 0 := by
 obtain ⟨count,running,stopped,final⟩ := for_completed condition post body fuel locals result ran
 exact ⟨Nat.repeat (next body post) count locals,final,
  (SourceLoop.compiled_finite condition post body depth block code emitted selected
    count locals newer m caller running stopped).2⟩


/-- The existing full-word local representation is injective. -/
theorem sourceLocals_injective {n : Nat} : Function.Injective (@sourceLocals n) := by
 intro a b same
 apply Vector.ext
 intro i hi
 have words := congrFun same (⟨i,hi⟩ : Fin n)
 apply BitVec.eq_of_toNat_eq
 exact congrArg Fin.val words

/-- info: 'Solidity.Yul.Compilation.SourceLoopCompletion.repeat_shift' does not depend on any axioms -/
#guard_msgs in
#print axioms repeat_shift
/-- info: 'Solidity.Yul.Compilation.SourceLoopCompletion.sourceLocals_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sourceLocals_injective
/-- info: 'Solidity.Yul.Compilation.SourceLoopCompletion.completed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completed
/-- info: 'Solidity.Yul.Compilation.SourceLoopCompletion.for_completed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms for_completed
/-- info: 'Solidity.Yul.Compilation.SourceLoopCompletion.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_to_model
end Solidity.Yul.Compilation.SourceLoopCompletion
