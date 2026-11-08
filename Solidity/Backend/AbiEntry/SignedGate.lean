import Solidity.Backend.AbiEntry.SignedGateInterface

/-! Two unsigned comparisons preserve the signed cleanup predicate exactly.
No conversion of the input word or narrowing of accepted widths is introduced. -/
namespace Solidity.Backend.AbiEntry.SignedGate
open Solidity.Evm
open Interface (RouteCtx signedGateOutcome)

def low (bits : Nat) : Nat := 2^(bits-1)
def high (bits : Nat) : Nat := Solidity.AbiEntry.W-low bits
private theorem valid_ranges (bits : Nat) (word : Fin W) :
    (Solidity.AbiEntry.Kind.int bits).valid word.val=
      (decide (word.val<low bits) || decide (high bits≤word.val)) := rfl
private theorem high_lt (bits : Nat) (fits : low bits<W) : high bits<W := by
  unfold high
  rw [Solidity.AbiEntry.W_eq]
  exact Nat.sub_lt_of_pos_le (Nat.two_pow_pos (bits-1)) (Nat.le_of_lt fits)

def negative (C : Contract) (bound label : Fin W) : Prog C RouteCtx RouteCtx :=
  .cons (.require (.unop .not rfl rfl (UnsignedGate.condition C bound))) (SelectorRoutes.writeLabel C label)
def program (C : Contract) (bits : Nat) (label : Fin W) : Prog C RouteCtx RouteCtx :=
  if fits : low bits<W then
    .cons (.ite (UnsignedGate.condition C ⟨low bits,fits⟩) (SelectorRoutes.writeLabel C label)
      (negative C ⟨high bits,high_lt bits fits⟩ label)) .nil
  else SelectorRoutes.writeLabel C label

theorem admitted (C : Contract) (bits : Nat) (label : Fin W) :
    inFragP (Frag.init RouteCtx) (program C bits label)=some (Frag.init RouteCtx) := by
  unfold program
  split <;> rfl

def compiled (C : Contract) (base bits : Nat) (label : Fin W) :
    Compiler.Compilation base (Frag.init RouteCtx) (program C bits label) :=
  .core (Frag.init RouteCtx) (admitted C bits label)
theorem selected (C : Contract) (base bits : Nat) (label : Fin W) :
    Compiler.compile base (Frag.init RouteCtx) (program C bits label)=some (compiled C base bits label) :=
  ValueGateBody.body_selected base _ _ _ (admitted C bits label)

private theorem negative_code (C : Contract) (base : Nat) (bound label : Fin W) :
    compileProg base (negative C bound label)=
      [.mload base,.push (.val bound),.gt,.iszero,.jumpi 1,.revert,.push (.val label),.mstore (base+1)] := by
  simp only [negative,compileProg,compileStmt,compileVal]
  rw [UnsignedGate.condition_code,SelectorRoutes.write_code]
  rfl
private theorem finite_code (C : Contract) (base bits : Nat) (label : Fin W) (fits : low bits<W) :
    compileProg base (program C bits label)=
      [.mload base,.push (.val ⟨low bits,fits⟩),.gt,.iszero,.jumpi 3,.push (.val label),.mstore (base+1),.jump 8]++
      [.mload base,.push (.val ⟨high bits,high_lt bits fits⟩),.gt,.iszero,.jumpi 1,.revert,.push (.val label),.mstore (base+1)] := by
  simp only [program,dif_pos fits,compileProg,compileStmt,List.append_nil]
  rw [UnsignedGate.condition_code,SelectorRoutes.write_code,negative_code]
  rfl

private theorem front (base : Nat) (bound label word : Fin W) (rest : List Evm.Instr) (machine : Machine)
    (initial : machine.mem base=.val word) :
    run ([.mload base,.push (.val bound),.gt,.iszero,.jumpi 3,.push (.val label),.mstore (base+1),.jump rest.length]++rest) machine=
      if word.val<bound.val then .ok {machine with mem := upd machine.mem (base+1) (.val label)} 0 else run rest machine := by
  by_cases small : word.val<bound.val
  · simp only [run,List.cons_append,List.nil_append,exec_cons_zero,Instr.step,Machine.next,Out.bind,initial,
      small,decide_true,bword,if_true,if_false,Nat.one_ne_zero,decide_false,Bool.false_eq_true,exec_length]
  · simp only [run,List.cons_append,List.nil_append,exec_cons_zero,exec_cons_succ,Instr.step,Machine.next,
      Out.bind,initial,small,decide_false,decide_true,bword,if_true,if_false,Nat.one_ne_zero,Bool.false_eq_true]
private theorem negative_run (base : Nat) (bound label word : Fin W) (machine : Machine)
    (initial : machine.mem base=.val word) :
    run [.mload base,.push (.val bound),.gt,.iszero,.jumpi 1,.revert,.push (.val label),.mstore (base+1)] machine=
      if word.val<bound.val then .revert else .ok {machine with mem := upd machine.mem (base+1) (.val label)} 0 := by
  by_cases small : word.val<bound.val
  · simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.bind,initial,small,decide_true,bword,if_true,
      if_false,Nat.one_ne_zero,decide_false,Bool.false_eq_true]
  · simp only [run,exec_cons_zero,exec_cons_succ,Instr.step,Machine.next,Out.bind,initial,small,decide_false,
      decide_true,bword,if_true,if_false,Nat.one_ne_zero,Bool.false_eq_true]
    rfl

theorem run_program (C : Contract) (base bits : Nat) (label : Fin W) (machine : Machine)
    (word : Fin W) (initial : machine.mem base=.val word) :
    run (compileProg base (program C bits label)) machine=signedGateOutcome base bits label word machine := by
  rw [signedGateOutcome,valid_ranges]
  by_cases fits : low bits<W
  · rw [finite_code C base bits label fits]
    have tailLength : (8 : Nat)=([.mload base,.push (.val ⟨high bits,high_lt bits fits⟩),.gt,.iszero,
      .jumpi 1,.revert,.push (.val label),.mstore (base+1)] : List Evm.Instr).length := rfl
    rw [tailLength,front base _ label word _ machine initial]
    by_cases positive : word.val<low bits
    · simp only [if_pos positive,decide_eq_true positive,Bool.true_or,if_true]
    · rw [if_neg positive,negative_run base _ label word machine initial]
      by_cases lower : word.val<high bits
      · have invalid : ¬high bits≤word.val := Nat.not_le_of_gt lower
        simp only [if_pos lower,
          decide_eq_false positive,decide_eq_false invalid,Bool.false_or,Bool.false_eq_true,if_false]
      · have valid : high bits≤word.val := Nat.le_of_not_gt lower
        simp only [if_neg lower,
          decide_eq_false positive,decide_eq_true valid,Bool.false_or,if_true]
  · have positive : word.val<low bits := Nat.lt_of_lt_of_le word.isLt (Nat.le_of_not_gt fits)
    simp only [program,dif_neg fits,
      decide_eq_true positive,Bool.true_or,if_true]
    rw [SelectorRoutes.write_code]
    rfl

theorem executed (C : Contract) (base bits : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C bits label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C bits label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word) :
    run result.code machine=signedGateOutcome base bits label word machine := by
  have same : result=compiled C base bits label := Option.some.inj (found.symm.trans (selected C base bits label))
  rw [same]
  exact run_program C base bits label machine word initial

theorem rejected_iff (C : Contract) (base bits : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C bits label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C bits label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word) :
    (run result.code machine=.revert ↔ (Solidity.AbiEntry.Kind.int bits).valid word.val=false) := by
  rw [executed C base bits label result found machine word initial]
  cases valid : (Solidity.AbiEntry.Kind.int bits).valid word.val with
  | false => simp only [signedGateOutcome,valid,Bool.false_eq_true,if_false]
  | true =>
    simp only [signedGateOutcome,valid,if_true]
    constructor <;> intro impossible <;> cases impossible

theorem correspondence (C : Contract) (base bits : Nat) (label : Fin W)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (program C bits label))
    (found : Compiler.compile base (Frag.init RouteCtx) (program C bits label)=some result)
    (machine : Machine) (word : Fin W) (initial : machine.mem base=.val word)
    (input : Solidity.AbiEntry.Input) (offset fuel len : Nat)
    (loaded : word.val=Solidity.AbiEntry.load input.data offset) :
    (run result.code machine=.revert ↔
      Solidity.AbiEntry.cval input (fuel+1) (.word (.int bits)) offset len=.error .revert) := by
  rw [rejected_iff C base bits label result found machine word initial,loaded]
  cases valid : (Solidity.AbiEntry.Kind.int bits).valid (Solidity.AbiEntry.load input.data offset) with
  | false => simp only [Solidity.AbiEntry.cval,valid,Bool.false_eq_true,dite_false]
  | true =>
    simp only [Solidity.AbiEntry.cval,valid,dite_true]
    constructor <;> intro impossible <;> cases impossible

def certificate : Interface.SignedGateCertificate program where
  selected := fun C base bits label => ⟨compiled C base bits label,selected C base bits label⟩
  executed := executed
/-- info: 'Solidity.Backend.AbiEntry.SignedGate.admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.SignedGate.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.SignedGate.run_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_program
/-- info: 'Solidity.Backend.AbiEntry.SignedGate.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.SignedGate.rejected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_iff
/-- info: 'Solidity.Backend.AbiEntry.SignedGate.correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms correspondence
/-- info: 'Solidity.Backend.AbiEntry.SignedGate.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.SignedGate
