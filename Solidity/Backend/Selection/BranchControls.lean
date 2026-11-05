import Solidity.Backend.Selection.BranchExecution

/-! Whole-branch controls with actual assembly, populated tails and conditions
that change the lower stack. No minimal assembler-width claim is needed. -/
namespace Solidity.Backend.Selection.ExecutionTrace.BranchControls

open LabelExec

def condition : Code 2 3 where
  instructions := [.op (.DUP 0)]
  shape := .cons (.mk 1 2 1 rfl rfl rfl) (.nil 3)
  capacity := by decide

def yes : Code 2 2 where
  instructions := [Scalar.pushByte 7, .op .ADD]
  shape := .cons (.mk 0 1 2 rfl rfl rfl) (.cons (.mk 2 1 1 rfl rfl rfl) (.nil 2))
  capacity := by decide

def no : Code 2 2 where
  instructions := [.op .POP, Scalar.pushByte 99]
  shape := .cons (.mk 1 0 1 rfl rfl rfl) (.cons (.mk 0 1 1 rfl rfl rfl) (.nil 2))
  capacity := by decide

def block : Block := .ite condition.instructions (.code yes.instructions) (.code no.instructions)
def certificate : ControlCertificate block 2 2 :=
  iteCertificate condition (codeCertificate yes) (codeCertificate no) (by decide) (by decide)

def before : List (Item Nat Empty) := [.instr (Scalar.pushWord 99)]
def after : List (Item Nat Empty) := [.instr (.op .POP)]
def items : List (Item Nat Empty) := before ++ (block.expand 0).1 ++ after

theorem assembly_exists : ∃ out : Assembled Empty, assemble 0 emptyLink items = some out := by
  have onlyRef : ∀ label ∈ refs items, label = 0 ∨ label = 1 := by
    intro label member
    simpa only [show refs items = [0,1] from rfl, List.mem_cons, List.not_mem_nil, or_false] using member
  have defined : ∀ label ∈ refs items, (tagIndex items label).isSome := by
    intro label member; rcases onlyRef label member with rfl | rfl <;> decide
  have fits : ∀ label ∈ refs items,
      0 + tagOffset (fun _ => (32 : Fin 33)) items label < 256 ^ 32 := by
    intro label member; rcases onlyRef label member with rfl | rfl <;> decide
  exact Option.isSome_iff_exists.mp (assemble_isSome emptyLink (by decide) defined fits)

theorem true_execution : StructuredExec block [5,23] [12,23] :=
  .iteTrue (show Scalar.run condition.instructions [5,23] = some [5,5,23] from rfl)
    (by decide) (.code (by decide))

theorem false_execution : StructuredExec block [0,23] [99,23] :=
  .iteFalse (show Scalar.run condition.instructions [0,23] = some [0,0,23] from rfl)
    (.code (by decide))

def exitPC : Nat := size (emitPrefix items (before ++ (block.expand 0).1))

/-- Both body entries, join behavior, final tag and every stack bound are derived. -/
theorem both_arms : ∃ out : Assembled Empty, assemble 0 emptyLink items = some out ∧
    ∃ trueCount falseCount : Nat,
      Safe (encode out.code) trueCount ⟨33,[5,23]⟩ ⟨exitPC,[12,23]⟩ ∧
      Safe (encode out.code) falseCount ⟨33,[0,23]⟩ ⟨exitPC,[99,23]⟩ := by
  obtain ⟨out,assembly⟩ := assembly_exists
  obtain ⟨yesCount,yesTrace⟩ := BranchLayout.realize_items certificate items before after 0 out
    assembly rfl [5,23] [12,23] rfl true_execution
  obtain ⟨noCount,noTrace⟩ := BranchLayout.realize_items certificate items before after 0 out
    assembly rfl [0,23] [99,23] rfl false_execution
  exact ⟨out,assembly,yesCount,noCount,yesTrace,noTrace⟩

/-- The same actual assembled true-arm run cannot return the false result or a damaged tail. -/
theorem wrong_arm_or_tail : ∃ out : Assembled Empty, assemble 0 emptyLink items = some out ∧
    ∃ count : Nat,
      advance count (encode out.code) ⟨33,[5,23]⟩ = some ⟨exitPC,[12,23]⟩ ∧
      advance count (encode out.code) ⟨33,[5,23]⟩ ≠ some ⟨exitPC,[99,23]⟩ ∧
      advance count (encode out.code) ⟨33,[5,23]⟩ ≠ some ⟨exitPC,[12,24]⟩ := by
  obtain ⟨out,assembly,yesCount,noCount,yesTrace,noTrace⟩ := both_arms
  refine ⟨out,assembly,yesCount,yesTrace.1,?_,?_⟩
  · rw [yesTrace.1]
    intro same
    have stacks : ([12,23] : Scalar.Stack) = [99,23] := congrArg LabelExec.State.stack (Option.some.inj same)
    exact (by decide : ([12,23] : Scalar.Stack) ≠ [99,23]) stacks
  · rw [yesTrace.1]
    intro same
    have stacks : ([12,23] : Scalar.Stack) = [12,24] := congrArg LabelExec.State.stack (Option.some.inj same)
    exact (by decide : ([12,23] : Scalar.Stack) ≠ [12,24]) stacks

/-- This valid condition overwrites its lower operand before choosing the false body. -/
def changing : Code 2 3 where
  instructions := [.op .POP, Scalar.pushByte 99, .push 0 #v[]]
  shape := .cons (.mk 1 0 1 rfl rfl rfl)
    (.cons (.mk 0 1 1 rfl rfl rfl) (.cons (.mk 0 1 2 rfl rfl rfl) (.nil 3)))
  capacity := by decide

def changedBlock : Block := .ite changing.instructions (.code yes.instructions) (.code yes.instructions)
def changedCertificate : ControlCertificate changedBlock 2 2 :=
  iteCertificate changing (codeCertificate yes) (codeCertificate yes) (by decide) (by decide)

theorem changed_execution : StructuredExec changedBlock [42,23] [106,23] :=
  .iteFalse (show Scalar.run changing.instructions [42,23] = some [0,99,23] from rfl)
    (.code (by decide))

def changedItems : List (Item Nat Empty) := before ++ (changedBlock.expand 0).1 ++ after

theorem changed_assembly_exists : ∃ out : Assembled Empty, assemble 0 emptyLink changedItems = some out := by
  have onlyRef : ∀ label ∈ refs changedItems, label = 0 ∨ label = 1 := by
    intro label member
    simpa only [show refs changedItems = [0,1] from rfl, List.mem_cons, List.not_mem_nil, or_false] using member
  have defined : ∀ label ∈ refs changedItems, (tagIndex changedItems label).isSome := by
    intro label member; rcases onlyRef label member with rfl | rfl <;> decide
  have fits : ∀ label ∈ refs changedItems,
      0 + tagOffset (fun _ => (32 : Fin 33)) changedItems label < 256 ^ 32 := by
    intro label member; rcases onlyRef label member with rfl | rfl <;> decide
  exact Option.isSome_iff_exists.mp (assemble_isSome emptyLink (by decide) defined fits)

/-- Whole byte execution observes the changed operand99, not the original42. -/
theorem changed_tail_observed : ∃ out : Assembled Empty, assemble 0 emptyLink changedItems = some out ∧
    ∃ count, Safe (encode out.code) count ⟨33,[42,23]⟩
      ⟨size (emitPrefix changedItems (before ++ (changedBlock.expand 0).1)),[106,23]⟩ := by
  obtain ⟨out,assembly⟩ := changed_assembly_exists
  obtain ⟨count,trace⟩ := BranchLayout.realize_items changedCertificate changedItems before after 0 out
    assembly rfl [42,23] [106,23] rfl changed_execution
  exact ⟨out,assembly,count,trace⟩

/-- The emitted join PUSH needs its own room beyond a full output stack. -/
theorem join_overflow (condition : Program) (left right : Block) (n : Nat) :
    ¬ ExpansionRoom (.ite condition left right) n 1024 := by
  intro room
  have capacity : 1024 + 1 ≤ 1024 := room.2.2
  omega

#print axioms certificate
#print axioms assembly_exists
#print axioms true_execution
#print axioms false_execution
#print axioms both_arms
#print axioms wrong_arm_or_tail
#print axioms changedCertificate
#print axioms changed_execution
#print axioms changed_tail_observed
#print axioms join_overflow

end Solidity.Backend.Selection.ExecutionTrace.BranchControls
