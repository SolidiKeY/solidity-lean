import Solidity.Backend.Selection.FramedLowering
import Solidity.Backend.StructuredFlow.BranchSelector

/-! Numeric-condition extensions of the existing relative-branch emitter laws.
The actual pending-skip continuation is retained, not turned into a return. -/
namespace Solidity.Backend.Selection.IRBranch

abbrev emit (condition left right : List Evm.Instr) : List Evm.Instr :=
  StructuredFlow.Branch.emit condition left right

theorem numeric_zero (word : Scalar.Word) :
    decide ((Evm.wmod word.toNat).val = 0) = (word == 0) := by
  rw [ir_word_nat, word_beq_nat]
  rfl

theorem test_run (distance : Nat) (word : Scalar.Word) (tail : Scalar.Stack) (initial : Evm.Machine) :
    Evm.run [.iszero, .jumpi distance] { initial with stack := irStack (word :: tail) } =
      .ok { initial with stack := irStack tail } (if word == 0 then distance else 0) := by
  simp only [Evm.run, Evm.exec_cons_zero, Evm.Instr.step, irStack, List.map_cons,
    Evm.Machine.next, Evm.Out.bind, Evm.exec_nil, numeric_zero]
  cases flag : word == 0 <;> rfl

theorem suffix_run (left right : List Evm.Instr) (word : Scalar.Word) (tail : Scalar.Stack)
    (initial : Evm.Machine) :
    Evm.run (emit [] left right) { initial with stack := irStack (word :: tail) } =
      if word == 0 then Evm.run right { initial with stack := irStack tail }
      else (Evm.run left { initial with stack := irStack tail }).bind
        (fun next pending => Evm.exec ([.jump right.length] ++ right) pending next) := by
  unfold emit StructuredFlow.Branch.emit
  simp only [List.nil_append]
  rw [Evm.run_append_skip (test_run (left.length + 1) word tail initial)]
  cases flag : word == 0 with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact Evm.exec_append left ([.jump right.length] ++ right) 0 _
  | true =>
    simp only [if_true]
    rw [Evm.exec_skip_append]
    rfl

theorem run {condition left right : List Evm.Instr} {initial : Evm.Machine}
    {word : Scalar.Word} {tail : Scalar.Stack}
    (actual : Evm.run condition initial = .ok { initial with stack := irStack (word :: tail) } 0) :
    Evm.run (emit condition left right) initial =
      if word == 0 then Evm.run right { initial with stack := irStack tail }
      else (Evm.run left { initial with stack := irStack tail }).bind
        (fun next pending => Evm.exec ([.jump right.length] ++ right) pending next) := by
  unfold emit StructuredFlow.Branch.emit
  rw [Evm.run_append_ok actual]
  exact suffix_run left right word tail initial

theorem split (condition left right : List Evm.Instr) (initial : Evm.Machine) :
    Evm.run (emit condition left right) initial =
      (Evm.run condition initial).bind (fun middle pending => Evm.exec (emit [] left right) pending middle) :=
  Evm.exec_append condition (emit [] left right) 0 initial

theorem empty_suffix (left right : List Evm.Instr) (initial : Evm.Machine) :
    Evm.run (emit [] left right) { initial with stack := irStack [] } = .fault := rfl

theorem join_normal (right : List Evm.Instr) (initial : Evm.Machine) :
    Evm.exec ([.jump right.length] ++ right) 0 initial = .ok initial 0 := by
  change Evm.exec right right.length initial = .ok initial 0
  exact Evm.exec_length right initial

/-- info: 'Solidity.Backend.Selection.IRBranch.numeric_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms numeric_zero
/-- info: 'Solidity.Backend.Selection.IRBranch.test_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms test_run
/-- info: 'Solidity.Backend.Selection.IRBranch.suffix_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms suffix_run
/-- info: 'Solidity.Backend.Selection.IRBranch.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run
/-- info: 'Solidity.Backend.Selection.IRBranch.split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms split
/-- info: 'Solidity.Backend.Selection.IRBranch.empty_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_suffix
/-- info: 'Solidity.Backend.Selection.IRBranch.join_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms join_normal

end Solidity.Backend.Selection.IRBranch
