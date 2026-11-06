import Solidity.Backend.Passes.StatefulDivision
import Solidity.Backend.Passes.StatefulModular
import Solidity.Backend.Passes.StatefulValueNegatives

namespace Solidity.Backend.Passes.StatefulSpecialControls
open Evm Evm.Memory
open Backend.Passes.Controls.Fixture
open ValueSequenceControls
open StatefulValueControls

def signedSecond : Val C Γ .int := .unop .toInt rfl rfl second
def signedFour : PrimTy.int.Denote := ⟨4,rfl⟩
theorem signed_second_source : signedSecond.evalT σ = .ok signedFour := by with_unfolding_all rfl
def uDiv : Val C Γ .uint := .binop .div rfl rfl first second
def uDivCode : CompiledVal 0 (Frag.init Γ) uDiv := (compileVal 0 _ uDiv).get (by decide +kernel)
def uMod : Val C Γ .uint := .binop .mod rfl rfl first second
def uModCode : CompiledVal 0 (Frag.init Γ) uMod := (compileVal 0 _ uMod).get (by decide +kernel)
def iDiv : Val C Γ .int := .binop .div rfl rfl negated signedSecond
def iDivCode : CompiledVal 0 (Frag.init Γ) iDiv := (compileVal 0 _ iDiv).get (by decide +kernel)
def iMod : Val C Γ .int := .binop .mod rfl rfl negated signedSecond
def iModCode : CompiledVal 0 (Frag.init Γ) iMod := (compileVal 0 _ iMod).get (by decide +kernel)

theorem source_results :
    uDiv.evalT σ = .ok (lenU 1 (by decide)) ∧ uMod.evalT σ = .ok three ∧
    iDiv.evalT σ = .ok (⟨-1,rfl⟩ : PrimTy.int.Denote) ∧
    iMod.evalT σ = .ok (⟨-3,rfl⟩ : PrimTy.int.Denote) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals with_unfolding_all rfl

theorem uDiv_application :
    Evm.ValOutT .uint (TRes.ofOpt (BinOp.div.evalT rfl seven four))
      (run uDivCode.code {machine with stack := saved.map Word.val}) {machine with stack := saved.map Word.val} ∧
    Backend.Scalar.guarded (Backend.Scalar.zeroTest ⟨1,by decide⟩) [.op .DIV] Backend.Scalar.divisionFailure
      (Backend.Scalar.encodeValue .uint seven :: Backend.Scalar.encodeValue .uint four ::
        saved.map (fun w => BitVec.ofNat 256 w.val)) =
      some (Backend.Scalar.divisionOutcome .uint (BinOp.div.evalT rfl seven four)
        (saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
    Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2 : Nat) : Int) = true ∧
    Backend.Scalar.stackBound [.op .DIV] ((saved.length+2 : Nat) : Int) = true :=
  StatefulDivision.uint_division uDivCode fixture_repr first_source second_source saved (by decide +kernel) (by decide +kernel)

theorem uMod_application :
    Evm.ValOutT .uint (TRes.ofOpt (BinOp.mod.evalT rfl seven four))
      (run uModCode.code {machine with stack := saved.map Word.val}) {machine with stack := saved.map Word.val} ∧
    Backend.Scalar.guarded (Backend.Scalar.zeroTest ⟨1,by decide⟩) [.op .MOD] Backend.Scalar.divisionFailure
      (Backend.Scalar.encodeValue .uint seven :: Backend.Scalar.encodeValue .uint four ::
        saved.map (fun w => BitVec.ofNat 256 w.val)) =
      some (Backend.Scalar.divisionOutcome .uint (BinOp.mod.evalT rfl seven four)
        (saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
    Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2 : Nat) : Int) = true ∧
    Backend.Scalar.stackBound [.op .MOD] ((saved.length+2 : Nat) : Int) = true :=
  StatefulDivision.uint_remainder uModCode fixture_repr first_source second_source saved (by decide +kernel) (by decide +kernel)

theorem iMod_application :
    Evm.ValOutT .int (TRes.ofOpt (BinOp.mod.evalT rfl minusSeven signedFour))
      (run iModCode.code {machine with stack := saved.map Word.val}) {machine with stack := saved.map Word.val} ∧
    Backend.Scalar.guarded (Backend.Scalar.zeroTest ⟨1,by decide⟩) [.op .SMOD] Backend.Scalar.divisionFailure
      (Backend.Scalar.encodeValue .int minusSeven :: Backend.Scalar.encodeValue .int signedFour ::
        saved.map (fun w => BitVec.ofNat 256 w.val)) =
      some (Backend.Scalar.divisionOutcome .int (BinOp.mod.evalT rfl minusSeven signedFour)
        (saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
    Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2 : Nat) : Int) = true ∧
    Backend.Scalar.stackBound [.op .SMOD] ((saved.length+2 : Nat) : Int) = true :=
  StatefulDivision.int_remainder iModCode fixture_repr negated_source signed_second_source saved (by decide +kernel) (by decide +kernel)

theorem iDiv_application :
    Evm.ValOutT .int (TRes.ofOpt (BinOp.div.evalT rfl minusSeven signedFour))
      (run iDivCode.code {machine with stack := saved.map Word.val}) {machine with stack := saved.map Word.val} ∧
    Backend.Scalar.signedDivExecute
      (Backend.Scalar.encodeValue .int minusSeven :: Backend.Scalar.encodeValue .int signedFour ::
        saved.map (fun w => BitVec.ofNat 256 w.val)) =
      some (Backend.Scalar.signedDivOutcome minusSeven signedFour (saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
    Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2 : Nat) : Int) = true ∧
    Backend.Scalar.stackBound Backend.Scalar.signedDivOverflowTest ((saved.length+2 : Nat) : Int) = true ∧
    Backend.Scalar.stackBound [.op .SDIV] ((saved.length+2 : Nat) : Int) = true :=
  StatefulDivision.int_division iDivCode fixture_repr negated_source signed_second_source saved
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def zeroRead : Val C Γ .uint := .simple (.local .here)
def zero : PrimTy.uint.Denote := ⟨0,rfl⟩
def zeroDiv : Val C Γ .uint := .binop .div rfl rfl first zeroRead
def zeroDivCode : CompiledVal 0 (Frag.init Γ) zeroDiv := (compileVal 0 _ zeroDiv).get (by decide +kernel)

theorem zero_division :
    zeroDiv.evalT σ = .error .revert ∧
      run zeroDivCode.code {machine with stack := saved.map Word.val} = .revert ∧
      Backend.Scalar.guarded (Backend.Scalar.zeroTest ⟨1,by decide⟩) [.op .DIV] Backend.Scalar.divisionFailure
        (Backend.Scalar.encodeValue .uint seven :: Backend.Scalar.encodeValue .uint zero ::
          saved.map (fun w => BitVec.ofNat 256 w.val)) = some (.error Backend.Scalar.divisionFailure) := by
  have source : zeroDiv.evalT σ = .error .revert := by with_unfolding_all rfl
  have actual := StatefulDivision.uint_division zeroDivCode fixture_repr first_source
    (a := seven) (d := zero) (by with_unfolding_all rfl) saved (by decide +kernel) (by decide +kernel)
  refine ⟨source,(value_revert_iff zeroDivCode fixture_repr _).mpr source,?_⟩
  simpa only [Backend.Scalar.divisionOutcome,show BinOp.div.evalT (p := .uint) rfl seven zero = none by decide +kernel,
    Option.elim_none] using actual.2.1

def minusOne : PrimTy.int.Denote := ⟨-1,rfl⟩
def overflowDiv : Val C Γ .int :=
  .binop .div rfl rfl StatefulValueNegatives.minimumOperand (.simple (.lit (-1) rfl))
def overflowDivCode : CompiledVal 0 (Frag.init Γ) overflowDiv := (compileVal 0 _ overflowDiv).get (by decide +kernel)

theorem signed_overflow :
    overflowDiv.evalT StatefulValueNegatives.minimumSource = .error .revert ∧
      run overflowDivCode.code {StatefulValueNegatives.minimumMachine with stack := saved.map Word.val} = .revert ∧
      Backend.Scalar.signedDivExecute
        (Backend.Scalar.encodeValue .int Backend.Scalar.minimumInt :: Backend.Scalar.encodeValue .int minusOne ::
          saved.map (fun w => BitVec.ofNat 256 w.val)) = some (.error Backend.Scalar.overflowFailure) := by
  have source : overflowDiv.evalT StatefulValueNegatives.minimumSource = .error .revert := by with_unfolding_all rfl
  have actual := StatefulDivision.int_division overflowDivCode StatefulValueNegatives.minimum_input
    StatefulValueNegatives.minimum_operand_source (d := minusOne) rfl saved
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨source,(value_revert_iff overflowDivCode StatefulValueNegatives.minimum_input _).mpr source,?_⟩
  simpa only [Backend.Scalar.signedDivOutcome,show minusOne.val ≠ 0 by decide,if_false,
    Backend.Scalar.checkedOutcome,show BinOp.div.evalT (p := .int) rfl Backend.Scalar.minimumInt minusOne = none by decide +kernel,
    Option.elim_none] using actual.2.1

/-- Identical coarse reverts above do NOT determine component failure bytes. -/
theorem distinct_failure_bytes : Backend.Scalar.divisionFailure ≠ Backend.Scalar.overflowFailure := by decide +kernel

theorem body_bytes :
    Backend.encode [.op Backend.Op.DIV] = [0x04] ∧ Backend.encode [.op Backend.Op.MOD] = [0x06] ∧
    Backend.encode [.op Backend.Op.SDIV] = [0x05] ∧ Backend.encode [.op Backend.Op.SMOD] = [0x07] := by decide +kernel

end Solidity.Backend.Passes.StatefulSpecialControls
