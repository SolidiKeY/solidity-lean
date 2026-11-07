import Solidity.Backend.Selection.StructuredExecution
import Solidity.Backend.Selection.BranchControls

/-! Nonempty conditional loop bodies, repeated actual backedges, zero exit and
changed-condition controls at a nonzero whole-runtime byte placement. -/
namespace Solidity.Backend.Selection.ExecutionTrace.LoopControls

open LabelExec

abbrev condition : Code 2 3 := BranchControls.condition

def decrement : Code 2 2 where
  instructions := [Scalar.pushByte 1, .op (.SWAP 0), .op .SUB]
  shape := .cons (.mk 0 1 2 rfl rfl rfl)
    (.cons (.mk 2 2 1 rfl rfl rfl) (.cons (.mk 2 1 1 rfl rfl rfl) (.nil 2)))
  capacity := by decide

def identity : Code 2 2 where
  instructions := []
  shape := .nil 2
  capacity := by decide

def body : Block := .ite condition.instructions (.code decrement.instructions) (.code identity.instructions)
def bodyCertificate : ControlCertificate body 2 2 :=
  iteCertificate condition (codeCertificate decrement) (codeCertificate identity) (by decide) (by decide)
def block : Block := .loop condition.instructions body
def loopControl : ControlCertificate block 2 2 := loopCertificate condition bodyCertificate (by decide)
/-- Exercise the general constructor, not only a hand-selected loop instance. -/
def certificate : ControlCertificate block 2 2 :=
  structuredCertificate block loopControl.shape loopControl.room

def before : List (Item Nat Empty) := [.instr (Scalar.pushWord 99)]
def after : List (Item Nat Empty) := [.instr (.op .POP)]
def placement : LoopLayout.Placement := ⟨before,after,condition.instructions,body,0⟩
def items : List (Item Nat Empty) := placement.items

theorem assembly_exists : ∃ out : Assembled Empty, assemble 0 emptyLink items = some out := by
  have onlyRef : ∀ label ∈ refs items, label = 1 ∨ label = 2 ∨ label = 3 ∨ label = 0 := by
    intro label member
    simpa only [show refs items = [1,2,3,0] from rfl, List.mem_cons, List.not_mem_nil, or_false] using member
  have defined : ∀ label ∈ refs items, (tagIndex items label).isSome := by
    intro label member; rcases onlyRef label member with rfl | rfl | rfl | rfl <;> decide
  have fits : ∀ label ∈ refs items,
      0 + tagOffset (fun _ => (32 : Fin 33)) items label < 256 ^ 32 := by
    intro label member; rcases onlyRef label member with rfl | rfl | rfl | rfl <;> decide
  exact Option.isSome_iff_exists.mp (assemble_isSome emptyLink (by decide) defined fits)

theorem body_two_one : StructuredExec body [2,23] [1,23] :=
  .iteTrue (show Scalar.run condition.instructions [2,23] = some [2,2,23] from rfl)
    (by decide) (.code (by decide))

theorem body_one_zero : StructuredExec body [1,23] [0,23] :=
  .iteTrue (show Scalar.run condition.instructions [1,23] = some [1,1,23] from rfl)
    (by decide) (.code (by decide))

theorem zero_execution : StructuredExec block [0,23] [0,23] :=
  .loopDone (show Scalar.run condition.instructions [0,23] = some [0,0,23] from rfl)

theorem two_execution : StructuredExec block [2,23] [0,23] :=
  .loopMore (show Scalar.run condition.instructions [2,23] = some [2,2,23] from rfl)
    (by decide) body_two_one
    (.loopMore (show Scalar.run condition.instructions [1,23] = some [1,1,23] from rfl)
      (by decide) body_one_zero zero_execution)

/-- The arbitrary nonempty structured body is reached and its backedge returns
at byte33 after PUSH32, not item1 or byte0; no remaining-loop premise is used. -/
theorem actual_iteration : ∃ out : Assembled Empty, assemble 0 emptyLink items = some out ∧
    ∃ count, Safe (encode out.code) count ⟨33,[2,23]⟩ ⟨33,[1,23]⟩ := by
  obtain ⟨out,assembly⟩ := assembly_exists
  obtain ⟨count,trace⟩ := placement.iteration condition rfl bodyCertificate (by decide) out assembly
    [2,23] [2,23] [1,23] 2 rfl rfl (by decide) body_two_one
  exact ⟨out,assembly,count,trace⟩

theorem wrong_head : ∃ out : Assembled Empty, assemble 0 emptyLink items = some out ∧
    ∃ count, advance count (encode out.code) ⟨33,[2,23]⟩ = some ⟨33,[1,23]⟩ ∧
      advance count (encode out.code) ⟨33,[2,23]⟩ ≠ some ⟨0,[1,23]⟩ := by
  obtain ⟨out,assembly,count,trace⟩ := actual_iteration
  refine ⟨out,assembly,count,trace.1,?_⟩
  rw [trace.1]
  intro equal
  have pc : (33 : Nat) = 0 := congrArg LabelExec.State.pc (Option.some.inj equal)
  omega

/-- Two real iterations/backedges and the zero exit execute in the same bytes. -/
theorem whole_loop : ∃ out : Assembled Empty, assemble 0 emptyLink items = some out ∧
    ∃ count, Safe (encode out.code) count ⟨33,[2,23]⟩
      ⟨placement.pc (placement.endPre ++ [.tag 1]),[0,23]⟩ := by
  obtain ⟨out,assembly⟩ := assembly_exists
  obtain ⟨count,trace⟩ := BranchLayout.realize_items certificate items before after 0 out
    assembly placement.items_eq [2,23] [0,23] rfl two_execution
  have endPrefix : before ++ (block.expand 0).1 = placement.endPre ++ [.tag 1] := placement.block_prefix
  rw [endPrefix] at trace
  exact ⟨out,assembly,count,trace⟩

theorem zero_loop : ∃ out : Assembled Empty, assemble 0 emptyLink items = some out ∧
    ∃ count, Safe (encode out.code) count ⟨33,[0,23]⟩
      ⟨placement.pc (placement.endPre ++ [.tag 1]),[0,23]⟩ := by
  obtain ⟨out,assembly⟩ := assembly_exists
  obtain ⟨count,trace⟩ := BranchLayout.realize_items certificate items before after 0 out
    assembly placement.items_eq [0,23] [0,23] rfl zero_execution
  have endPrefix : before ++ (block.expand 0).1 = placement.endPre ++ [.tag 1] := placement.block_prefix
  rw [endPrefix] at trace
  exact ⟨out,assembly,count,trace⟩

theorem wrong_result_or_tail : ∃ out : Assembled Empty, assemble 0 emptyLink items = some out ∧
    ∃ count, advance count (encode out.code) ⟨33,[2,23]⟩ =
        some ⟨placement.pc (placement.endPre ++ [.tag 1]),[0,23]⟩ ∧
      advance count (encode out.code) ⟨33,[2,23]⟩ ≠
        some ⟨placement.pc (placement.endPre ++ [.tag 1]),[1,23]⟩ ∧
      advance count (encode out.code) ⟨33,[2,23]⟩ ≠
        some ⟨placement.pc (placement.endPre ++ [.tag 1]),[0,24]⟩ := by
  obtain ⟨out,assembly,count,trace⟩ := whole_loop
  refine ⟨out,assembly,count,trace.1,?_,?_⟩
  · rw [trace.1]
    intro equal
    have stacks : ([0,23] : Scalar.Stack) = [1,23] := congrArg LabelExec.State.stack (Option.some.inj equal)
    exact (by decide : ([0,23] : Scalar.Stack) ≠ [1,23]) stacks
  · rw [trace.1]
    intro equal
    have stacks : ([0,23] : Scalar.Stack) = [0,24] := congrArg LabelExec.State.stack (Option.some.inj equal)
    exact (by decide : ([0,23] : Scalar.Stack) ≠ [0,24]) stacks

/-- A zero-exit condition may also change the returned lower stack. -/
theorem changed_exit : ∃ out : Assembled Empty,
    assemble 0 emptyLink ((Block.loop BranchControls.changing.instructions (.code [])).expand 0).1 = some out ∧
    ∃ count, Safe (encode out.code) count ⟨0,[42,23]⟩ ⟨size out.code,[99,23]⟩ := by
  let changed : Block := .loop BranchControls.changing.instructions (.code [])
  let control : ControlCertificate changed 2 2 :=
    loopCertificate BranchControls.changing (codeCertificate identity) (by decide)
  have execution : StructuredExec changed [42,23] [99,23] :=
    .loopDone (show Scalar.run BranchControls.changing.instructions [42,23] = some [0,99,23] from rfl)
  have fits : ∀ label ∈ refs (changed.expand 0).1,
      0 + tagOffset (fun _ => (32 : Fin 33)) (changed.expand 0).1 label < 256 ^ 32 := by
    intro label member
    have onlyRef : label = 1 ∨ label = 0 := by
      simpa only [show refs (changed.expand 0).1 = [1,0] from rfl,
        List.mem_cons, List.not_mem_nil, or_false] using member
    rcases onlyRef with rfl | rfl <;> decide
  obtain ⟨out,assembly⟩ := Option.isSome_iff_exists.mp (Block.expand_assemble_isSome changed 0 0 emptyLink fits)
  obtain ⟨count,actual,bounds⟩ := control.realize [] [] 0 out
    (by simpa only [List.nil_append, List.append_nil] using assembly) [42,23] [99,23] rfl execution
  have emitted : out.code = emitPrefix (changed.expand 0).1 (changed.expand 0).1 := (assemble_eq assembly).2.1
  have whole : Safe (encode out.code) count ⟨0,[42,23]⟩
      ⟨size (emitPrefix (changed.expand 0).1 (changed.expand 0).1),[99,23]⟩ := by
    simpa only [Safe, List.nil_append, List.append_nil] using And.intro actual bounds
  rw [← emitted] at whole
  exact ⟨out,assembly,count,whole⟩

/-- Static loop headers cannot exceed the physical bound with their target PUSH. -/
theorem header_overflow (condition : Code 1023 1024) (body : Block) :
    ¬ ControlCertificate (.loop condition.instructions body) 1023 1023 := by
  intro control
  have capacity : 1023 + 2 ≤ 1024 := control.shape.control_capacity
  omega

#print axioms bodyCertificate
#print axioms loopControl
#print axioms certificate
#print axioms assembly_exists
#print axioms body_two_one
#print axioms body_one_zero
#print axioms zero_execution
#print axioms two_execution
#print axioms actual_iteration
#print axioms wrong_head
#print axioms whole_loop
#print axioms zero_loop
#print axioms wrong_result_or_tail
#print axioms changed_exit
#print axioms header_overflow

end Solidity.Backend.Selection.ExecutionTrace.LoopControls
