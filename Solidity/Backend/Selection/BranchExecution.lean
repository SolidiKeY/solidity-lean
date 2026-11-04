import Solidity.Backend.Selection.BranchPackets

/-! Whole execution of conditional blocks through existing byte-PC control. -/
namespace Solidity.Backend.Selection.ExecutionTrace

/-- Both actual condition outcomes reach their selected body and execute its
join tag, retaining bounds on every fetched instruction boundary. -/
def iteCertificate {n m : Nat} (condition : LabelExec.Code n (n + 1))
    {left right : Block} (yes : ControlCertificate left n m)
    (no : ControlCertificate right n m) (testRoom : n + 2 ≤ 1024)
    (joinRoom : m + 1 ≤ 1024) :
    ControlCertificate (.ite condition.instructions left right) n m where
  shape := .ite yes.shape no.shape testRoom
  room := ⟨yes.room,no.room,joinRoom⟩
  realize := by
    intro before after label out assembly input output height execution
    let p : BranchLayout.Placement := ⟨before,after,condition.instructions,left,right,label⟩
    have assembled : assemble 0 LabelExec.emptyLink p.items = some out := by
      rw [← p.items_eq]; exact assembly
    change ∃ steps, Safe (encode out.code) steps
      ⟨size (LabelExec.emitPrefix (p.before ++ ((Block.ite p.condition p.yes p.no).expand p.label).1 ++ p.after) p.before),input⟩
      ⟨size (LabelExec.emitPrefix (p.before ++ ((Block.ite p.condition p.yes p.no).expand p.label).1 ++ p.after)
        (p.before ++ ((Block.ite p.condition p.yes p.no).expand p.label).1)),output⟩
    rw [p.items_eq, p.block_prefix]
    change ∃ steps, Safe (encode out.code) steps
      ⟨p.pc p.before,input⟩ ⟨p.pc (p.endPre ++ [.tag (p.label + 1)]),output⟩
    have capacity : Scalar.stackBound p.condition (input.length : Int) = true := by
      rw [height]; exact condition.capacity
    cases execution with
    | @iteTrue c a b s middle t word run nonzero body =>
      have middle_length : middle.length = n := by
        have result : (word :: middle).length = n + 1 := code_length condition.shape _ _ run height
        simp only [List.length_cons] at result; omega
      have output_length : output.length = m := structured_length yes.shape body middle_length
      obtain ⟨count,bodySafe⟩ := p.yes_run out assembled yes middle output middle_length body
      have first : Safe (encode out.code) p.condition.length
          ⟨p.pc p.before,input⟩ ⟨p.pc p.checked,word :: middle⟩ :=
        p.condition_run out assembled input (word :: middle) run capacity
      have second : Safe (encode out.code) 3
          ⟨p.pc p.checked,word :: middle⟩ ⟨p.pc p.yesPre,middle⟩ :=
        p.test_nonzero out assembled word middle nonzero (by omega)
      have fourth : Safe (encode out.code) 2
          ⟨p.pc (p.yesPre ++ p.yesItems),output⟩ ⟨p.pc p.endPre,output⟩ :=
        p.join_run out assembled output (by omega)
      have final : Safe (encode out.code) 1
          ⟨p.pc p.endPre,output⟩ ⟨p.pc (p.endPre ++ [.tag (p.label + 1)]),output⟩ :=
        p.end_tag out assembled output (by omega)
      exact ⟨p.condition.length + 3 + count + 2 + 1,
        append (append (append (append first second) bodySafe) fourth) final⟩
    | @iteFalse c a b s middle t run body =>
      have middle_length : middle.length = n := by
        have result : ((0 : Scalar.Word) :: middle).length = n + 1 := code_length condition.shape _ _ run height
        simp only [List.length_cons] at result; omega
      have output_length : output.length = m := structured_length no.shape body middle_length
      obtain ⟨count,bodySafe⟩ := p.no_run out assembled no middle output middle_length body
      have first : Safe (encode out.code) p.condition.length
          ⟨p.pc p.before,input⟩ ⟨p.pc p.checked,0 :: middle⟩ :=
        p.condition_run out assembled input (0 :: middle) run capacity
      have second : Safe (encode out.code) 3
          ⟨p.pc p.checked,0 :: middle⟩ ⟨p.pc p.falsePre,middle⟩ :=
        p.test_zero out assembled middle (by omega)
      have third : Safe (encode out.code) 1
          ⟨p.pc p.falsePre,middle⟩ ⟨p.pc p.noPre,middle⟩ :=
        p.false_tag out assembled middle (by omega)
      have final : Safe (encode out.code) 1
          ⟨p.pc p.endPre,output⟩ ⟨p.pc (p.endPre ++ [.tag (p.label + 1)]),output⟩ :=
        p.end_tag out assembled output (by omega)
      exact ⟨p.condition.length + 3 + 1 + count + 1,
        append (append (append (append first second) third) bodySafe) final⟩

#print axioms iteCertificate

end Solidity.Backend.Selection.ExecutionTrace
