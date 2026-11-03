import Solidity.Backend.Scalar.WidthGuards
import Solidity.Backend.Scalar.Heights
import Solidity.Backend.Passes.ValueCertificate

/-! Consumer of published signed-width tests over the EXISTING intrinsic
comparison/Boolean/require constructors. This is not frontend cast expansion,
signed truncation, public ABI failure, or a new source/target evaluator. -/
namespace Solidity.Backend.Passes.SignedWidthGuard
open Backend.Scalar
variable {C : Contract} {Γ : Ctx}

def lower (w : Fin 32) (operand : Val C Γ .int) : Val C Γ .bool :=
  .binop .lt rfl rfl operand
    (.simple (.lit (signedMinimum w).val (signedMinimum w).property))

def upper (w : Fin 32) (operand : Val C Γ .int) : Val C Γ .bool :=
  .binop .lt rfl rfl
    (.simple (.lit (signedMaximum w).val (signedMaximum w).property)) operand

def outside (w : Fin 32) (operand : Val C Γ .int) : Val C Γ .bool :=
  .binop .or rfl rfl (lower w operand) (upper w operand)

def condition (w : Fin 32) (operand : Val C Γ .int) : Val C Γ .bool :=
  .unop .not rfl rfl (outside w operand)

private theorem comparison (left right : Val C Γ .int) (state : State C Γ)
    (a b : PrimTy.int.Denote) (hl : left.evalT state = .ok a) (hr : right.evalT state = .ok b) :
    (Val.binop .lt rfl rfl left right).evalT state = .ok (decide (a.val < b.val)) := by
  simp only [Val.evalT,hl,hr,BinOp.shortT,bind,Except.bind]
  rfl

theorem outside_source (w : Fin 32) (operand : Val C Γ .int) (state : State C Γ)
    (value : PrimTy.int.Denote) (evaluated : operand.evalT state = .ok value) :
    (outside w operand).evalT state =
      .ok (decide (value.val < (signedMinimum w).val) ||
        decide ((signedMaximum w).val < value.val)) := by
  have lo : (lower w operand).evalT state =
      .ok (decide (value.val < (signedMinimum w).val)) :=
    comparison _ _ state value (signedMinimum w) evaluated rfl
  have hi : (upper w operand).evalT state =
      .ok (decide ((signedMaximum w).val < value.val)) :=
    comparison _ _ state (signedMaximum w) value rfl evaluated
  simp only [outside,Val.evalT,lo,hi,bind,Except.bind]
  cases decide (value.val < (signedMinimum w).val) <;> rfl

theorem condition_source (w : Fin 32) (operand : Val C Γ .int) (state : State C Γ)
    (value : PrimTy.int.Denote) (evaluated : operand.evalT state = .ok value) :
    (condition w operand).evalT state = .ok (signedFits w value) := by
  have observed := outside_source w operand state value evaluated
  have bounds :
      (!(decide (value.val < (signedMinimum w).val) ||
        decide ((signedMaximum w).val < value.val))) = signedFits w value := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true',Bool.or_eq_false_iff,decide_eq_false_iff_not,
      signedFits,decide_eq_true_eq,signedMinimum,signedMaximum]
    have positive : 0 < 2 ^ (widthBits w - 1) := Nat.pow_pos (by decide)
    omega
  simp only [condition,Val.evalT,observed,bind,Except.bind]
  change (Except.ok (!(decide (value.val < (signedMinimum w).val) ||
    decide ((signedMaximum w).val < value.val))) : TRes Bool) = _
  rw [bounds]

def compiled {b : Nat} {F : Evm.Frag Γ} (w : Fin 32) (operand : Val C Γ .int)
    (given : Evm.Memory.CompiledVal b F operand) :
    Evm.Memory.CompiledVal b F (condition w operand) :=
  let lo : Evm.Memory.CompiledVal b F (lower w operand) :=
    ⟨_,.binary .lt rfl rfl _ _ _ _ given.cert (.core _ rfl)⟩
  let hi : Evm.Memory.CompiledVal b F (upper w operand) :=
    ⟨_,.binary .lt rfl rfl _ _ _ _ (.core _ rfl) given.cert⟩
  let either : Evm.Memory.CompiledVal b F (outside w operand) :=
    ⟨_,.binary .or rfl rfl _ _ _ _ lo.cert hi.cert⟩
  ⟨_,.unary .not rfl rfl _ _ either.cert⟩

/-- Caller-selected failure bytes and original numeric test capacity remain
explicit. Numeric component failure is not identified with public ABI bytes. -/
theorem application {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (operand : Val C Γ .int)
    (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (input : Evm.Memory.StateRepr L b frame F state base machine)
    (value : PrimTy.int.Denote) (evaluated : operand.evalT state = .ok value)
    (saved : List (Fin Evm.W)) (failure : List UInt8)
    (capacity : stackBound (signedWidthTest w) ((saved.length+1 : Nat) : Int) = true) :
    (condition w operand).evalT state = .ok (signedFits w value) ∧
    Evm.run (compiled w operand given).code {machine with stack := saved.map Evm.Word.val} =
      .ok ({machine with stack := saved.map Evm.Word.val}.push
        (.val (Evm.bword (signedFits w value)))) 0 ∧
    guarded (signedWidthTest w) [] failure
      (encodeValue .int value :: saved.map (fun a => BitVec.ofNat 256 a.val)) =
      some (if signedFits w value then
        .ok (encodeValue .int value :: saved.map (fun a => BitVec.ofNat 256 a.val))
        else .error failure) ∧
    stackBound (signedWidthTest w) ((saved.length+1 : Nat) : Int) = true := by
  have source := condition_source w operand state value evaluated
  obtain ⟨word,represented,target⟩ :=
    value_success_tail (compiled w operand given) input source (saved.map Evm.Word.val)
  have exactWord : word = .val (Evm.bword (signedFits w value)) := represented
  rw [exactWord] at target
  exact ⟨source,target,signedWidth_guarded w value _ failure,capacity⟩

theorem prefix_safe (w : Fin 32) (value : PrimTy.int.Denote) (saved : Stack)
    (capacity : stackBound (signedWidthTest w) ((saved.length+1 : Nat) : Int) = true)
    (before after : Backend.Program) (code : before ++ after = signedWidthTest w)
    {reached : Stack} (target : run before (encodeValue .int value :: saved) = some reached) :
    reached.length ≤ 1024 := by
  apply prefix_capacity before after target
  rw [code]
  exact capacity

end Solidity.Backend.Passes.SignedWidthGuard
/-- info: 'Solidity.Backend.Passes.SignedWidthGuard.outside_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthGuard.outside_source
/-- info: 'Solidity.Backend.Passes.SignedWidthGuard.condition_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthGuard.condition_source
/-- info: 'Solidity.Backend.Passes.SignedWidthGuard.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthGuard.application
/-- info: 'Solidity.Backend.Passes.SignedWidthGuard.prefix_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthGuard.prefix_safe

namespace Solidity.Backend.Passes.SignedWidthGuard
open Backend.Scalar
variable {C : Contract} {Γ : Ctx}

/-- Existing certificate/constructors only; not a generic compiler-recognizer
or frontend correspondence theorem. -/
def requireStage {b : Nat} {F : Evm.Frag Γ} (w : Fin 32) (operand : Val C Γ .int)
    (given : Evm.Memory.CompiledVal b F operand) :
    Evm.Compiler.Compilation b F (.cons (.require (condition w operand)) .nil) :=
  .memory ⟨F,((compiled w operand given).code ++ Evm.assertTop) ++ [],
    .cons (.require F _ _ (compiled w operand given).cert) (.nil F)⟩

theorem require_input {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (operand : Val C Γ .int) (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (input : Evm.Memory.StateRepr L b frame F state base machine)
    (capacity : b+Γ.length ≤ frame) :
    (requireStage w operand given).Input L frame base state machine := by
  refine ⟨input,?_,Or.inl rfl⟩
  change b + max (max Γ.length (max Γ.length 0)) Γ.length ≤ frame
  omega

theorem require_source (w : Fin 32) (operand : Val C Γ .int) (state : State C Γ)
    (value : PrimTy.int.Denote) (evaluated : operand.evalT state = .ok value) :
    (Prog.cons (.require (condition w operand)) .nil).run state =
      if signedFits w value then .ok ⟨state,List.prefix_refl _⟩ else .error .revert := by
  have source := condition_source w operand state value evaluated
  change TRun.seq (TRun.require (condition w operand)) _ state = _
  simp only [TRun.seq,TRun.require,Solidity.boolT,source,bind,Except.bind]
  cases signedFits w value <;> rfl

/-- The actual symbolic require run has no output machine on failure.
A successful check restores the entire initial machine and saved tail. -/
theorem require_target {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (operand : Val C Γ .int) (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (input : Evm.Memory.StateRepr L b frame F state base machine)
    (value : PrimTy.int.Denote) (evaluated : operand.evalT state = .ok value)
    (tail : List Evm.Word) :
    Evm.run (requireStage w operand given).code {machine with stack := tail} =
      if signedFits w value then .ok {machine with stack := tail} 0 else .revert := by
  have source := condition_source w operand state value evaluated
  obtain ⟨word,represented,target⟩ :=
    value_success_tail (compiled w operand given) input source tail
  have exactWord : word = .val (Evm.bword (signedFits w value)) := represented
  rw [exactWord] at target
  change Evm.run (((compiled w operand given).code ++ Evm.assertTop) ++ []) _ = _
  rw [List.append_nil,Evm.run_append_ok target]
  cases signedFits w value <;> rfl

theorem require_revert_iff {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (operand : Val C Γ .int) (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (input : Evm.Memory.StateRepr L b frame F state base machine)
    (value : PrimTy.int.Denote) (evaluated : operand.evalT state = .ok value)
    (tail : List Evm.Word) :
    (Evm.run (requireStage w operand given).code {machine with stack := tail} = .revert ↔
      signedFits w value = false) ∧
    (Evm.run (requireStage w operand given).code {machine with stack := tail} = .revert ↔
      (Prog.cons (.require (condition w operand)) .nil).run state = .error .revert) := by
  rw [require_target w operand given input value evaluated tail,
    require_source w operand state value evaluated]
  cases signedFits w value <;> simp only [Bool.false_eq_true,Bool.true_eq,ite_false,ite_true,
    reduceCtorEq,and_self]

end Solidity.Backend.Passes.SignedWidthGuard
/-- info: 'Solidity.Backend.Passes.SignedWidthGuard.require_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthGuard.require_input
/-- info: 'Solidity.Backend.Passes.SignedWidthGuard.require_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthGuard.require_source
/-- info: 'Solidity.Backend.Passes.SignedWidthGuard.require_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthGuard.require_target
/-- info: 'Solidity.Backend.Passes.SignedWidthGuard.require_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthGuard.require_revert_iff

namespace Solidity.Backend.Passes.SignedWidthGuard
open Backend.Scalar
variable {C : Contract} {Γ : Ctx}

theorem condition_operand_failure (w : Fin 32) (operand : Val C Γ .int)
    (state : State C Γ) (halt : THalt) (failed : operand.evalT state = .error halt) :
    (condition w operand).evalT state = .error halt := by
  simp only [condition,outside,lower,Val.evalT,failed,bind,Except.bind]

theorem require_operand_failure {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (operand : Val C Γ .int) (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (input : Evm.Memory.StateRepr L b frame F state base machine)
    (failed : operand.evalT state = .error .revert) (tail : List Evm.Word) :
    Evm.run (requireStage w operand given).code {machine with stack := tail} = .revert := by
  have conditionFailed := condition_operand_failure w operand state .revert failed
  have target := (value_revert_iff (compiled w operand given) input tail).mpr conditionFailed
  change Evm.run (((compiled w operand given).code ++ Evm.assertTop) ++ []) _ = _
  rw [List.append_nil]
  exact Evm.run_append_revert target

/-- Two DISTINCT reached failure alternatives: the operand never produces a
value, or an actually evaluated value fails the signed range check. -/
theorem require_failure_cases {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (operand : Val C Γ .int) (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (input : Evm.Memory.StateRepr L b frame F state base machine) (tail : List Evm.Word) :
    Evm.run (requireStage w operand given).code {machine with stack := tail} = .revert ↔
      operand.evalT state = .error .revert ∨
      ∃ value, operand.evalT state = .ok value ∧ signedFits w value = false := by
  constructor
  · intro failed
    rcases given.cert.correct (input.stack tail) with
      ⟨value,word,source,represented,target⟩ | ⟨source,target⟩
    · exact .inr ⟨value,source,(require_revert_iff w operand given input value source tail).1.mp failed⟩
    · exact .inl source
  · rintro (failed | ⟨value,source,outside⟩)
    · exact require_operand_failure w operand given input failed tail
    · exact (require_revert_iff w operand given input value source tail).1.mpr outside

end Solidity.Backend.Passes.SignedWidthGuard
/-- info: 'Solidity.Backend.Passes.SignedWidthGuard.condition_operand_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthGuard.condition_operand_failure
/-- info: 'Solidity.Backend.Passes.SignedWidthGuard.require_operand_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthGuard.require_operand_failure
/-- info: 'Solidity.Backend.Passes.SignedWidthGuard.require_failure_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.SignedWidthGuard.require_failure_cases
