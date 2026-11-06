import Solidity.Backend.Passes.StatefulSpecialControls

namespace Solidity.Backend.Passes.StatefulModularControls
open Evm Evm.Memory
open Backend.Passes.Controls.Fixture
open ValueSequenceControls
open StatefulValueControls
open StatefulValueNegatives

def nineCode : CompiledVal 0 (Frag.init Γ) readNine := (compileVal 0 _ readNine).get (by decide +kernel)
def addition : Val C Γ .uint := .modular .addmod first second readNine
def multiplication : Val C Γ .uint := .modular .mulmod first second readNine
def zeroModulus : Val C Γ .uint := .modular .addmod first second StatefulSpecialControls.zeroRead

theorem source_results :
    addition.evalT σ = .ok (lenU 2 (by decide)) ∧
    multiplication.evalT σ = .ok (lenU 1 (by decide)) ∧
    zeroModulus.evalT σ = .error .revert := by
  refine ⟨?_,?_,?_⟩
  all_goals with_unfolding_all rfl

theorem operand_words (tail : List Word) :
    ∃ (wa wd wk : Fin W),
      ReprV .uint seven (.val wa) ∧ ReprV .uint four (.val wd) ∧ ReprV .uint nine (.val wk) ∧
      Backend.Scalar.encodeValue .uint seven = BitVec.ofNat 256 wa.val ∧
      Backend.Scalar.encodeValue .uint four = BitVec.ofNat 256 wd.val ∧
      Backend.Scalar.encodeValue .uint nine = BitVec.ofNat 256 wk.val ∧
      run (nineCode.code ++ (d.code ++ a.code)) {machine with stack := tail} =
        .ok ((({machine with stack := tail}.push (.val wk)).push (.val wd)).push (.val wa)) 0 :=
  StatefulModular.operands a d nineCode fixture_repr first_source second_source nine_source tail

theorem addition_application :
    addition.evalT σ = TRes.ofOpt (ModOp.addmod.evalT seven four nine) ∧
      Backend.Scalar.guarded (Backend.Scalar.selectModular .addmod).test (Backend.Scalar.selectModular .addmod).body
        Backend.Scalar.divisionFailure
        (Backend.Scalar.encodeValue .uint seven :: Backend.Scalar.encodeValue .uint four ::
          Backend.Scalar.encodeValue .uint nine :: saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (Backend.Scalar.modularOutcome .addmod seven four nine (saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
      Backend.Scalar.stackBound (Backend.Scalar.selectModular .addmod).test ((saved.length+3 : Nat) : Int) = true ∧
      Backend.Scalar.stackBound (Backend.Scalar.selectModular .addmod).body ((saved.length+3 : Nat) : Int) = true :=
  StatefulModular.component .addmod (Backend.Scalar.selectModular .addmod)
    first_source second_source nine_source saved (by decide +kernel) (by decide +kernel)

theorem multiplication_application :
    multiplication.evalT σ = TRes.ofOpt (ModOp.mulmod.evalT seven four nine) ∧
      Backend.Scalar.guarded (Backend.Scalar.selectModular .mulmod).test (Backend.Scalar.selectModular .mulmod).body
        Backend.Scalar.divisionFailure
        (Backend.Scalar.encodeValue .uint seven :: Backend.Scalar.encodeValue .uint four ::
          Backend.Scalar.encodeValue .uint nine :: saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (Backend.Scalar.modularOutcome .mulmod seven four nine (saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
      Backend.Scalar.stackBound (Backend.Scalar.selectModular .mulmod).test ((saved.length+3 : Nat) : Int) = true ∧
      Backend.Scalar.stackBound (Backend.Scalar.selectModular .mulmod).body ((saved.length+3 : Nat) : Int) = true :=
  StatefulModular.component .mulmod (Backend.Scalar.selectModular .mulmod)
    first_source second_source nine_source saved (by decide +kernel) (by decide +kernel)

/-- Real source/guarded failure reflection, without an unavailable whole
symbolic compiler certificate or an invented post-failure stack. -/
theorem zero_application :
    Backend.Scalar.guarded (Backend.Scalar.selectModular .addmod).test (Backend.Scalar.selectModular .addmod).body
      Backend.Scalar.divisionFailure
      (Backend.Scalar.encodeValue .uint seven :: Backend.Scalar.encodeValue .uint four ::
        Backend.Scalar.encodeValue .uint StatefulSpecialControls.zero :: saved.map (fun w => BitVec.ofNat 256 w.val)) =
      some (.error Backend.Scalar.divisionFailure) :=
  (StatefulModular.failure_iff .addmod (Backend.Scalar.selectModular .addmod)
    first_source second_source (show StatefulSpecialControls.zeroRead.evalT σ = .ok StatefulSpecialControls.zero by rfl)
    (saved.map (fun w => BitVec.ofNat 256 w.val))).mp source_results.2.2

/-- Exact remaining prerequisite: source and numeric component succeed, but
the actual current symbolic entry REFUSES both modular expressions. -/
theorem whole_compiler_refused :
    Memory.compileVal 0 (Frag.init Γ) addition = none ∧
    Memory.compileVal 0 (Frag.init Γ) multiplication = none := by
  constructor <;> rfl

theorem actual_bytes :
    Backend.encode (Backend.Scalar.selectModular .addmod).test = [0x82,0x15] ∧
    Backend.encode (Backend.Scalar.selectModular .addmod).body = [0x08] ∧
    Backend.encode (Backend.Scalar.selectModular .mulmod).body = [0x09] := by decide +kernel

theorem ignoring_zero_guard :
    Backend.Scalar.run (Backend.Scalar.selectModular .addmod).body [7,4,0,99] = some [0,99] := rfl

end Solidity.Backend.Passes.StatefulModularControls
