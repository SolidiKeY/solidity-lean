import Solidity.Backend.Selection.BranchLayout

/-! Bounded branch packets at their exact whole-expansion coordinates. -/
namespace Solidity.Backend.Selection.ExecutionTrace.BranchLayout.Placement

theorem condition_run (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (input output : Scalar.Stack) (actual : Scalar.run p.condition input = some output)
    (capacity : Scalar.stackBound p.condition (input.length : Int) = true) :
    Safe (encode out.code) p.condition.length ⟨p.pc p.before,input⟩ ⟨p.pc p.checked,output⟩ := by
  exact scalar_items p.items p.before
    (p.header ++ p.yesItems ++ p.join ++ [.tag p.label] ++ p.noItems ++ [.tag (p.label + 1)] ++ p.after)
    p.condition out assembly p.condition_split input output actual capacity

theorem test_nonzero (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (word : Scalar.Word) (tail : Scalar.Stack) (nonzero : word ≠ 0)
    (room : tail.length + 2 ≤ 1024) :
    Safe (encode out.code) 3 ⟨p.pc p.checked,word :: tail⟩ ⟨p.pc p.yesPre,tail⟩ := by
  obtain ⟨target,found,safe⟩ := test_items p.items p.checked
    (p.yesItems ++ p.join ++ [.tag p.label] ++ p.noItems ++ [.tag (p.label + 1)] ++ p.after)
    p.label out assembly p.header_split word tail room
  have flag : (word == 0) = false := Bool.eq_false_iff.mpr (fun equal => nonzero (beq_iff_eq.mp equal))
  simpa only [flag, Bool.false_eq_true, if_false] using safe

theorem test_zero (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (tail : Scalar.Stack) (room : tail.length + 2 ≤ 1024) :
    Safe (encode out.code) 3 ⟨p.pc p.checked,0 :: tail⟩ ⟨p.pc p.falsePre,tail⟩ := by
  obtain ⟨target,found,safe⟩ := test_items p.items p.checked
    (p.yesItems ++ p.join ++ [.tag p.label] ++ p.noItems ++ [.tag (p.label + 1)] ++ p.after)
    p.label out assembly p.header_split 0 tail room
  have target_at : target = p.falsePre.length := Option.some.inj (found.symm.trans (p.false_index out assembly))
  rw [target_at] at safe
  simpa only [beq_self_eq_true, if_true, p.false_pc out assembly] using safe

theorem join_run (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (tail : Scalar.Stack) (room : tail.length + 1 ≤ 1024) :
    Safe (encode out.code) 2 ⟨p.pc (p.yesPre ++ p.yesItems),tail⟩ ⟨p.pc p.endPre,tail⟩ := by
  obtain ⟨target,found,safe⟩ := jump_items p.items (p.yesPre ++ p.yesItems)
    (.tag p.label :: (p.noItems ++ [.tag (p.label + 1)] ++ p.after)) (p.label + 1)
    out assembly p.join_split tail room
  have target_at : target = p.endPre.length := Option.some.inj (found.symm.trans (p.end_index out assembly))
  rw [target_at, p.end_pc out assembly] at safe
  exact safe

theorem false_tag (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (tail : Scalar.Stack) (room : tail.length ≤ 1024) :
    Safe (encode out.code) 1 ⟨p.pc p.falsePre,tail⟩ ⟨p.pc p.noPre,tail⟩ := by
  exact tag_items p.items p.falsePre (p.noItems ++ [.tag (p.label + 1)] ++ p.after)
    p.label out assembly p.false_split tail room

theorem end_tag (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (tail : Scalar.Stack) (room : tail.length ≤ 1024) :
    Safe (encode out.code) 1 ⟨p.pc p.endPre,tail⟩ ⟨p.pc (p.endPre ++ [.tag (p.label + 1)]),tail⟩ := by
  exact tag_items p.items p.endPre p.after (p.label + 1) out assembly p.end_split tail room

theorem yes_run {n m : Nat} (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (certificate : ControlCertificate p.yes n m) (input output : Scalar.Stack)
    (height : input.length = n) (actual : StructuredExec p.yes input output) :
    ∃ count, Safe (encode out.code) count
      ⟨p.pc p.yesPre,input⟩ ⟨p.pc (p.yesPre ++ p.yesItems),output⟩ := by
  exact realize_items certificate p.items p.yesPre
    (p.join ++ [.tag p.label] ++ p.noItems ++ [.tag (p.label + 1)] ++ p.after)
    (p.label + 2) out assembly p.yes_split input output height actual

theorem no_run {n m : Nat} (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (certificate : ControlCertificate p.no n m) (input output : Scalar.Stack)
    (height : input.length = n) (actual : StructuredExec p.no input output) :
    ∃ count, Safe (encode out.code) count
      ⟨p.pc p.noPre,input⟩ ⟨p.pc p.endPre,output⟩ := by
  exact realize_items certificate p.items p.noPre ([.tag (p.label + 1)] ++ p.after)
    p.noLabel out assembly p.no_split input output height actual

#print axioms yes_run
#print axioms no_run

#print axioms condition_run
#print axioms test_nonzero
#print axioms test_zero
#print axioms join_run
#print axioms false_tag
#print axioms end_tag

end Solidity.Backend.Selection.ExecutionTrace.BranchLayout.Placement
