import Solidity.Backend.Selection.LoopPackets

/-! Whole finite loop execution, deriving body entry and actual backedges from
existing scalar/control certificates and the published block expansion. -/
namespace Solidity.Backend.Selection.ExecutionTrace
namespace LoopLayout.Placement

theorem iteration {n : Nat} (p : Placement) (condition : LabelExec.Code n (n + 1))
    (same : p.condition = condition.instructions) (body : ControlCertificate p.body n n)
    (testRoom : n + 2 ≤ 1024) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (input middle output : Scalar.Stack) (word : Scalar.Word) (height : input.length = n)
    (run : Scalar.run p.condition input = some (word :: middle)) (nonzero : word ≠ 0)
    (actualBody : StructuredExec p.body middle output) :
    ∃ count, Safe (encode out.code) count ⟨p.pc p.before,input⟩ ⟨p.pc p.before,output⟩ := by
  have shape : LabelExec.CodeShape p.condition n (n + 1) := by rw [same]; exact condition.shape
  have result : (word :: middle).length = n + 1 := code_length shape _ _ run height
  have middle_length : middle.length = n := by simp only [List.length_cons] at result; omega
  have output_length : output.length = n := structured_length body.shape actualBody middle_length
  have capacity : Scalar.stackBound p.condition (input.length : Int) = true := by
    rw [same, height]; exact condition.capacity
  have first : Safe (encode out.code) 1 ⟨p.pc p.before,input⟩ ⟨p.pc p.conditionPre,input⟩ :=
    p.head_tag out assembly input (by omega)
  have second : Safe (encode out.code) p.condition.length
      ⟨p.pc p.conditionPre,input⟩ ⟨p.pc p.checked,word :: middle⟩ :=
    p.condition_run out assembly input (word :: middle) run capacity
  have third : Safe (encode out.code) 3 ⟨p.pc p.checked,word :: middle⟩ ⟨p.pc p.bodyPre,middle⟩ :=
    p.test_nonzero out assembly word middle nonzero (by omega)
  obtain ⟨bodyCount,bodyTrace⟩ := p.body_run out assembly body middle output middle_length actualBody
  have last : Safe (encode out.code) 2 ⟨p.pc p.backPre,output⟩ ⟨p.pc p.before,output⟩ :=
    p.backedge out assembly output (by omega)
  exact ⟨1 + p.condition.length + 3 + bodyCount + 2,
    append (append (append (append first second) third) bodyTrace) last⟩

theorem exit {n : Nat} (p : Placement) (condition : LabelExec.Code n (n + 1))
    (same : p.condition = condition.instructions) (testRoom : n + 2 ≤ 1024)
    (out : Assembled Empty) (assembly : assemble 0 LabelExec.emptyLink p.items = some out)
    (input output : Scalar.Stack) (height : input.length = n)
    (run : Scalar.run p.condition input = some (0 :: output)) :
    ∃ count, Safe (encode out.code) count ⟨p.pc p.before,input⟩
      ⟨p.pc (p.endPre ++ [.tag (p.label + 1)]),output⟩ := by
  have shape : LabelExec.CodeShape p.condition n (n + 1) := by rw [same]; exact condition.shape
  have result : ((0 : Scalar.Word) :: output).length = n + 1 := code_length shape _ _ run height
  have output_length : output.length = n := by simp only [List.length_cons] at result; omega
  have capacity : Scalar.stackBound p.condition (input.length : Int) = true := by
    rw [same, height]; exact condition.capacity
  have first : Safe (encode out.code) 1 ⟨p.pc p.before,input⟩ ⟨p.pc p.conditionPre,input⟩ :=
    p.head_tag out assembly input (by omega)
  have second : Safe (encode out.code) p.condition.length
      ⟨p.pc p.conditionPre,input⟩ ⟨p.pc p.checked,0 :: output⟩ :=
    p.condition_run out assembly input (0 :: output) run capacity
  have third : Safe (encode out.code) 3 ⟨p.pc p.checked,0 :: output⟩ ⟨p.pc p.endPre,output⟩ :=
    p.test_zero out assembly output (by omega)
  have last : Safe (encode out.code) 1 ⟨p.pc p.endPre,output⟩
      ⟨p.pc (p.endPre ++ [.tag (p.label + 1)]),output⟩ := p.end_tag out assembly output (by omega)
  exact ⟨1 + p.condition.length + 3 + 1,append (append (append first second) third) last⟩

#print axioms iteration
#print axioms exit

end LoopLayout.Placement

/-- Induction is over the existing finite execution, not an external fuel or
favorable body/backedge premise. The actual condition tail may change values. -/
theorem finite_loop {block : Block} {input output : Scalar.Stack}
    (actual : StructuredExec block input output) :
    ∀ (p : LoopLayout.Placement), block = .loop p.condition p.body →
    ∀ (n : Nat) (condition : LabelExec.Code n (n + 1)), p.condition = condition.instructions →
    ∀ (_body : ControlCertificate p.body n n), n + 2 ≤ 1024 →
    ∀ (out : Assembled Empty), assemble 0 LabelExec.emptyLink p.items = some out → input.length = n →
    ∃ count, Safe (encode out.code) count ⟨p.pc p.before,input⟩
      ⟨p.pc (p.endPre ++ [.tag (p.label + 1)]),output⟩ := by
  induction actual with
  | code run => intro p equal; cases equal
  | seq left right ihLeft ihRight => intro p equal; cases equal
  | iteTrue run nonzero body ih => intro p equal; cases equal
  | iteFalse run body ih => intro p equal; cases equal
  | @loopDone c b input output run =>
    intro p equal n condition same body room out assembly height
    cases equal
    exact p.exit condition same room out assembly input output height run
  | @loopMore c b input middle next output word run nonzero bodyRun rest ihBody ihRest =>
    intro p equal n condition same body room out assembly height
    cases equal
    have shape : LabelExec.CodeShape p.condition n (n + 1) := by rw [same]; exact condition.shape
    have result : (word :: middle).length = n + 1 := code_length shape _ _ run height
    have middle_length : middle.length = n := by simp only [List.length_cons] at result; omega
    have next_length : next.length = n := structured_length body.shape bodyRun middle_length
    obtain ⟨iterationCount,iterationTrace⟩ := p.iteration condition same body room out assembly
      input middle next word height run nonzero bodyRun
    obtain ⟨restCount,restTrace⟩ := ihRest p rfl n condition same body room out assembly next_length
    exact ⟨iterationCount + restCount,append iterationTrace restTrace⟩

/-- General loop control realization with arbitrary certified structured bodies. -/
def loopCertificate {n : Nat} (condition : LabelExec.Code n (n + 1))
    {block : Block} (body : ControlCertificate block n n) (testRoom : n + 2 ≤ 1024) :
    ControlCertificate (.loop condition.instructions block) n n where
  shape := .loop body.shape testRoom
  room := body.room
  realize := by
    intro before after label out assembly input output height execution
    let p : LoopLayout.Placement := ⟨before,after,condition.instructions,block,label⟩
    have assembled : assemble 0 LabelExec.emptyLink p.items = some out := by
      rw [← p.items_eq]; exact assembly
    obtain ⟨count,trace⟩ := finite_loop execution p rfl n condition rfl body testRoom out assembled height
    change ∃ steps, Safe (encode out.code) steps
      ⟨size (LabelExec.emitPrefix (p.before ++ ((Block.loop p.condition p.body).expand p.label).1 ++ p.after) p.before),input⟩
      ⟨size (LabelExec.emitPrefix (p.before ++ ((Block.loop p.condition p.body).expand p.label).1 ++ p.after)
        (p.before ++ ((Block.loop p.condition p.body).expand p.label).1)),output⟩
    rw [p.items_eq, p.block_prefix]
    exact ⟨count,trace⟩

#print axioms finite_loop
#print axioms loopCertificate

end Solidity.Backend.Selection.ExecutionTrace
