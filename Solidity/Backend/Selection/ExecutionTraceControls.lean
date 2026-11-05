import Solidity.Backend.Selection.ExecutionTrace
import Solidity.Backend.LabelExec.FragmentControls

/-! Kernel witnesses for placed code and sequential control realization. -/
namespace Solidity.Backend.Selection.ExecutionTrace.Controls

open LabelExec

def first : Code 1 2 where
  instructions := [Scalar.pushByte 7]
  shape := .cons (.mk 0 1 1 rfl rfl rfl) (.nil 2)
  capacity := by decide

def second : Code 2 2 where
  instructions := [Scalar.pushByte 5, .op .ADD]
  shape := .cons (.mk 0 1 2 rfl rfl rfl)
    (.cons (.mk 2 1 1 rfl rfl rfl) (.nil 2))
  capacity := by decide

def block : Block := .seq (.code first.instructions) (.code second.instructions)

def certificate : ControlCertificate block 1 2 :=
  seqCertificate (codeCertificate first) (codeCertificate second)

def before : List (Item Nat Empty) := [.instr (Scalar.pushWord 99)]
def after : List (Item Nat Empty) := [.instr (.op .POP)]
def items : List (Item Nat Empty) := before ++ (block.expand 0).1 ++ after

def assembled : Assembled Empty :=
  ⟨[Scalar.pushWord 99, Scalar.pushByte 7, Scalar.pushByte 5, .op .ADD, .op .POP], []⟩

theorem assembly : assemble 0 emptyLink items = some assembled := by rfl

theorem execution : StructuredExec block [23] [12,23] :=
  .seq (show StructuredExec (.code first.instructions) [23] [7,23] from .code (by decide))
    (.code (by decide))

/-- The entry PC is a byte offset after PUSH32, rather than an item index. -/
theorem offsets : size (emitPrefix items before) = 33 ∧
    size (emitPrefix items (before ++ (block.expand 0).1)) = 38 := by decide

/-- An inhabited frozen certificate derives both execution and every bound. -/
theorem certified : ∃ count : Nat,
    Safe (encode assembled.code) count ⟨33,[23]⟩ ⟨38,[12,23]⟩ := by
  obtain ⟨count,actual,bounds⟩ := certificate.realize before after 0 assembled
    assembly [23] [12,23] rfl execution
  exact ⟨count,actual,bounds⟩

/-- Exact reached stack and PC independently compute in the byte evaluator. -/
theorem actual_three : advance 3 (encode assembled.code) ⟨33,[23]⟩ =
    some ⟨38,[12,23]⟩ := by decide

theorem wrong_item_pc : advance 3 (encode assembled.code) ⟨1,[23]⟩ = none := by decide

theorem wrong_result : advance 3 (encode assembled.code) ⟨33,[23]⟩ ≠
    some ⟨38,[13,23]⟩ := by decide

theorem corrupted_tail : advance 3 (encode assembled.code) ⟨33,[23]⟩ ≠
    some ⟨38,[12,24]⟩ := by decide

/-- Missing input is a real byte-executor shortage at ADD, not a static refusal. -/
theorem actual_underflow : advance 1 (encode assembled.code) ⟨37,[7]⟩ = none := by decide

/-- Height equality does not imply preservation of the lower word by a condition. -/
theorem changed_condition_tail :
    StructuredExec (.code overwritingCondition.instructions) [42] [0,99] ∧
      [99] ≠ ([42] : Scalar.Stack) :=
  ⟨.code condition_changes_lower_word, by decide⟩

#print axioms certificate
#print axioms assembly
#print axioms execution
#print axioms certified
#print axioms actual_three
#print axioms wrong_item_pc
#print axioms wrong_result
#print axioms corrupted_tail
#print axioms actual_underflow
#print axioms changed_condition_tail

end Solidity.Backend.Selection.ExecutionTrace.Controls
