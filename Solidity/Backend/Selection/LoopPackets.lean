import Solidity.Backend.Selection.LoopLayout

/-! Actual loop head, body and backedge traces with every packet bound. -/
namespace Solidity.Backend.Selection.ExecutionTrace.LoopLayout.Placement

theorem head_tag (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (tail : Scalar.Stack) (room : tail.length ≤ 1024) :
    Safe (encode out.code) 1 ⟨p.pc p.before,tail⟩ ⟨p.pc p.conditionPre,tail⟩ :=
  BranchLayout.tag_items p.items p.before
    (p.condition.map Item.instr ++ p.header ++ p.bodyItems ++ p.back ++ [.tag (p.label + 1)] ++ p.after)
    p.label out assembly p.head_split tail room

theorem condition_run (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (input output : Scalar.Stack) (actual : Scalar.run p.condition input = some output)
    (capacity : Scalar.stackBound p.condition (input.length : Int) = true) :
    Safe (encode out.code) p.condition.length
      ⟨p.pc p.conditionPre,input⟩ ⟨p.pc p.checked,output⟩ :=
  BranchLayout.scalar_items p.items p.conditionPre
    (p.header ++ p.bodyItems ++ p.back ++ [.tag (p.label + 1)] ++ p.after)
    p.condition out assembly p.condition_split input output actual capacity

theorem test_nonzero (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (word : Scalar.Word) (tail : Scalar.Stack) (nonzero : word ≠ 0)
    (room : tail.length + 2 ≤ 1024) :
    Safe (encode out.code) 3 ⟨p.pc p.checked,word :: tail⟩ ⟨p.pc p.bodyPre,tail⟩ := by
  obtain ⟨target,found,trace⟩ := BranchLayout.test_items p.items p.checked
    (p.bodyItems ++ p.back ++ [.tag (p.label + 1)] ++ p.after)
    (p.label + 1) out assembly p.header_split word tail room
  have flag : (word == 0) = false := Bool.eq_false_iff.mpr (fun equal => nonzero (beq_iff_eq.mp equal))
  simpa only [flag, Bool.false_eq_true, if_false] using trace

theorem test_zero (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (tail : Scalar.Stack) (room : tail.length + 2 ≤ 1024) :
    Safe (encode out.code) 3 ⟨p.pc p.checked,0 :: tail⟩ ⟨p.pc p.endPre,tail⟩ := by
  obtain ⟨target,found,trace⟩ := BranchLayout.test_items p.items p.checked
    (p.bodyItems ++ p.back ++ [.tag (p.label + 1)] ++ p.after)
    (p.label + 1) out assembly p.header_split 0 tail room
  have target_at : target = p.endPre.length := Option.some.inj (found.symm.trans (p.end_index out assembly))
  rw [target_at] at trace
  simpa only [beq_self_eq_true, if_true, p.end_pc out assembly] using trace

theorem body_run {n : Nat} (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (certificate : ControlCertificate p.body n n) (input output : Scalar.Stack)
    (height : input.length = n) (actual : StructuredExec p.body input output) :
    ∃ count, Safe (encode out.code) count ⟨p.pc p.bodyPre,input⟩ ⟨p.pc p.backPre,output⟩ :=
  BranchLayout.realize_items certificate p.items p.bodyPre
    (p.back ++ [.tag (p.label + 1)] ++ p.after) (p.label + 2) out assembly p.body_split
    input output height actual

theorem backedge (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (tail : Scalar.Stack) (room : tail.length + 1 ≤ 1024) :
    Safe (encode out.code) 2 ⟨p.pc p.backPre,tail⟩ ⟨p.pc p.before,tail⟩ := by
  obtain ⟨target,found,trace⟩ := BranchLayout.jump_items p.items p.backPre
    (.tag (p.label + 1) :: p.after) p.label out assembly p.back_split tail room
  have target_at : target = p.before.length := Option.some.inj (found.symm.trans (p.head_index out assembly))
  rw [target_at, p.head_pc out assembly] at trace
  exact trace

theorem end_tag (p : Placement) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (tail : Scalar.Stack) (room : tail.length ≤ 1024) :
    Safe (encode out.code) 1 ⟨p.pc p.endPre,tail⟩ ⟨p.pc (p.endPre ++ [.tag (p.label + 1)]),tail⟩ :=
  BranchLayout.tag_items p.items p.endPre p.after (p.label + 1) out assembly p.end_split tail room

#print axioms head_tag
#print axioms condition_run
#print axioms test_nonzero
#print axioms test_zero
#print axioms body_run
#print axioms backedge
#print axioms end_tag

end Solidity.Backend.Selection.ExecutionTrace.LoopLayout.Placement
