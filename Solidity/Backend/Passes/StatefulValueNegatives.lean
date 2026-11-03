import Solidity.Backend.Passes.StatefulValueControls

namespace Solidity.Backend.Passes.StatefulValueNegatives
open Evm Evm.Memory
open Backend.Passes.Controls.Fixture
open ValueSequenceControls
open StatefulValueControls

def readNine : Val C Γ .uint :=
  .readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 1 rfl)))
def nine : PrimTy.uint.Denote := ⟨9,rfl⟩
def underflow : Val C Γ .uint := .binop .sub rfl rfl first readNine
def underflowCode : CompiledVal 0 (Frag.init Γ) underflow := (compileVal 0 _ underflow).get (by decide +kernel)
theorem nine_source : readNine.evalT σ = .ok nine := by with_unfolding_all rfl

def underflowInvocation : Backend.Scalar.CheckedInvocation Backend.Scalar.checkedUintSub seven nine
    (saved.map (fun w => BitVec.ofNat 256 w.val)) where
  testCapacity := by decide +kernel
  bodyCapacity := by decide +kernel

theorem underflow_application :
    underflow.evalT σ = .error .revert ∧
      run underflowCode.code {machine with stack := saved.map Word.val} = .revert ∧
      Backend.Scalar.guarded Backend.Scalar.checkedUintSub.test Backend.Scalar.checkedUintSub.body
        Backend.Scalar.overflowFailure
        (Backend.Scalar.encodeValue .uint seven :: Backend.Scalar.encodeValue .uint nine ::
          saved.map (fun w => BitVec.ofNat 256 w.val)) = some (.error Backend.Scalar.overflowFailure) ∧
      Backend.Scalar.stackBound Backend.Scalar.checkedUintSub.test ((saved.length+2 : Nat) : Int) = true ∧
      Backend.Scalar.stackBound Backend.Scalar.checkedUintSub.body ((saved.length+2 : Nat) : Int) = true :=
  StatefulChecked.binary_failure Backend.Scalar.checkedUintSub underflowCode fixture_repr
    first_source nine_source rfl (by decide +kernel) saved underflowInvocation

def minimumUnsigned : PrimTy.uint.Denote := lenU (2^255) (by decide)
def minimumSource : State C Γ := σ.setLocal .here minimumUnsigned
def minimumMachine : Machine := writeMachine machine 3 (.val ⟨2^255,by decide⟩)
theorem minimum_input : StateRepr 1 0 4 (Frag.init Γ) minimumSource base minimumMachine :=
  fixture_repr.setVal .here minimumUnsigned (.val ⟨2^255,by decide⟩) (ReprV.uint_of rfl)
def minimumOperand : Val C Γ .int := .unop .toInt rfl rfl (.simple (.local .here))
def minimumNegation : Val C Γ .int := .unop .neg rfl rfl minimumOperand
def minimumCode : CompiledVal 0 (Frag.init Γ) minimumNegation :=
  (compileVal 0 _ minimumNegation).get (by decide +kernel)

theorem minimum_operand_source : minimumOperand.evalT minimumSource = .ok Backend.Scalar.minimumInt := by
  with_unfolding_all rfl

theorem minimum_negation_application :
    minimumNegation.evalT minimumSource = .error .revert ∧
      run minimumCode.code {minimumMachine with stack := saved.map Word.val} = .revert ∧
      Backend.Scalar.guarded Backend.Scalar.checkedIntNeg.test Backend.Scalar.checkedIntNeg.body
        Backend.Scalar.overflowFailure
        (Backend.Scalar.encodeValue .int Backend.Scalar.minimumInt :: saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (.error Backend.Scalar.overflowFailure) ∧
      Backend.Scalar.stackBound Backend.Scalar.checkedIntNeg.test ((saved.length+1 : Nat) : Int) = true ∧
      Backend.Scalar.stackBound Backend.Scalar.checkedIntNeg.body ((saved.length+1 : Nat) : Int) = true :=
  StatefulChecked.unary_failure Backend.Scalar.checkedIntNeg minimumCode minimum_input
    minimum_operand_source (by decide +kernel) saved (by decide +kernel) (by decide +kernel)

/-- Ignoring the real guard wraps minimum negation back to minimum, instead
of the source failure and owner's actual checked component error. -/
theorem ignored_negation_guard :
    Backend.Scalar.run Backend.Scalar.checkedIntNeg.body
      [Backend.Scalar.encodeValue .int Backend.Scalar.minimumInt,99] =
      some [Backend.Scalar.encodeValue .int Backend.Scalar.minimumInt,99] := by decide +kernel

theorem negation_guard_bytes :
    Backend.encode Backend.Scalar.checkedIntNeg.test =
      [0x80,0x7f,0x80] ++ List.replicate 31 0 ++ [0x14] := by decide +kernel

theorem false_guard_taken : BinOp.and.shortT (p := .bool) false = some false := rfl
theorem eager_guard_refused : BinOp.and.shortT (p := .bool) false ≠ none := by decide

theorem skipped_rhs (tail : List Word) :
    (ExpressionControls.conjunction false).evalT σ = .ok false ∧
    ∃ w : Fin W, ReprV .bool false (.val w) ∧
      Backend.Scalar.encodeValue .bool false = BitVec.ofNat 256 w.val ∧
      run (ExpressionControls.checkedAnd false).code {machine with stack := tail} =
        .ok ({machine with stack := tail}.push (.val w)) 0 :=
  StatefulValues.short_taken (ExpressionControls.checkedAnd false) fixture_repr rfl rfl tail

theorem reached_rhs (tail : List Word) :
    (ExpressionControls.conjunction true).evalT σ = .error .revert ∧
      run (ExpressionControls.checkedAnd true).code {machine with stack := tail} = .revert :=
  StatefulValues.right_revert (ExpressionControls.checkedAnd true) fixture_repr rfl rfl
    (by with_unfolding_all rfl) tail

def failedLeft : Val C Γ .uint := .binop .subW rfl rfl ExpressionControls.badRead second
def failedLeftCode : CompiledVal 0 (Frag.init Γ) failedLeft :=
  (compileVal 0 _ failedLeft).get (by decide +kernel)
theorem failed_left (tail : List Word) :
    failedLeft.evalT σ = .error .revert ∧
      run failedLeftCode.code {machine with stack := tail} = .revert :=
  StatefulValues.left_revert failedLeftCode fixture_repr (by with_unfolding_all rfl) tail

/-- The wrong eager schedule reaches a real bounds revert; the actual whole
short-circuit compiler above succeeds. No failed RHS value is fabricated. -/
theorem eager_failure (tail : List Word) :
    run ExpressionControls.checkedBad.code {machine with stack := tail} = .revert :=
  (value_revert_iff ExpressionControls.checkedBad fixture_repr tail).mpr (by with_unfolding_all rfl)

theorem reversed_numeric :
    Backend.Scalar.run Backend.Scalar.wrappingSub.code
      [Backend.Scalar.encodeValue .uint four,Backend.Scalar.encodeValue .uint seven,99] =
      some [BitVec.ofNat 256 (2^256-3),99] := by decide +kernel

theorem capacity_refused : Backend.Scalar.stackBound Backend.Scalar.wrappingSub.code 1025 = false := by decide +kernel

theorem operand_corruption :
    run (d.code ++ [.pop] ++ a.code) machine ≠ run (d.code ++ a.code) machine := by
  obtain ⟨wa,_,ha⟩ := value_success_tail a fixture_repr first_source []
  obtain ⟨wd,_,hd⟩ := value_success_tail d fixture_repr second_source []
  change run a.code machine = .ok (machine.push wa) 0 at ha
  change run d.code machine = .ok (machine.push wd) 0 at hd
  have bad : run (d.code ++ [.pop] ++ a.code) machine = .ok (machine.push wa) 0 := by
    rw [List.append_assoc,run_append_ok hd,run_append_ok (m' := machine) (show run [.pop] (machine.push wd) = .ok machine 0 from rfl)]
    exact ha
  obtain ⟨x,y,_,_,good⟩ := value_pair_success_tail d a fixture_repr second_source first_source []
  change run (d.code ++ a.code) machine = .ok ((machine.push x).push y) 0 at good
  intro equal
  rw [bad,good] at equal
  have lengths := congrArg (fun out => match out with | .ok m _ => some m.stack.length | _ => none) equal
  change (some 1 : Option Nat) = some 2 at lengths
  cases lengths

def minimumProgram : Prog C Γ Γ :=
  .cons (.assignLocal .here (.simple (.lit minimumUnsigned.val minimumUnsigned.property))) .nil
def minimumProgramCode : Memory.CompiledProg 0 (Frag.init Γ) minimumProgram :=
  (Memory.compileProg 0 _ minimumProgram).get (by decide +kernel)

theorem minimum_reached (tail : List Word) :
    minimumProgram.run σ = .ok ⟨minimumSource,List.prefix_refl _⟩ ∧
    run minimumProgramCode.code {machine with stack := tail} =
      .ok {minimumMachine with stack := tail} 0 := by
  constructor <;> with_unfolding_all rfl

/-- The signed guard failure is reached after a genuine typed assignment. -/
theorem minimum_prefix_failure (tail : List Word) :
    run (minimumProgramCode.code ++ minimumCode.code) {machine with stack := tail} = .revert := by
  rw [run_append_ok (minimum_reached tail).2]
  exact (value_revert_iff minimumCode minimum_input tail).mpr minimum_negation_application.1

end Solidity.Backend.Passes.StatefulValueNegatives
