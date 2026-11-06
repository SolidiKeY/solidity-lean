import Solidity.Yul.LocalOperations
import Solidity.Yul.Checks.LocalBlock
namespace Solidity.Yul.Checks.LocalOperations
open Solidity.Yul.LocalOperations
/-- Test-local decidable result equality; no Source implementation change. -/
local instance {α : Type} [DecidableEq α] : DecidableEq (Solidity.Source.R α) := by
  intro first second
  cases first with
  | error a =>
      cases second with
      | error b =>
          exact if h : a = b then isTrue (h ▸ rfl)
            else isFalse (fun same => h (Except.error.inj same))
      | ok b => exact isFalse (by intro same; cases same)
  | ok a =>
      cases second with
      | error b => exact isFalse (by intro same; cases same)
      | ok b =>
          exact if h : a = b then isTrue (h ▸ rfl)
            else isFalse (fun same => h (Except.ok.inj same))

example : Pipeline = Solidity.Roadmap.Pipeline := rfl

def env : Solidity.Source.Env := ⟨[]⟩
def b (n : Nat) : LocalValue env .bool := .scalar (boolShape env) (word n)
def u (n : Nat) : LocalValue env (.int Solidity.Source.IntTy.u8) := .scalar (u8Shape env) (word n)
def boolOut (result : Solidity.Source.R (LocalValue env .bool)) :
    Solidity.Source.R Nat := result.map (fun value => (scalarWord value (boolShape env)).val)
def u8Out (result : Solidity.Source.R (LocalValue env (.int Solidity.Source.IntTy.u8))) :
    Solidity.Source.R Nat := result.map (fun value => (scalarWord value (u8Shape env)).val)

example : boolOut (boolNot (b 2)) = .ok 0 := by decide
example : boolOut (boolBinary .and (b 2) (b 4)) = .ok 1 := by decide
example : boolOut (boolBinary .or (b 0) (b 2)) = .ok 1 := by decide
example : boolCompare .eq (b 2) (b 1) = .ok true := by decide
example : boolCompare .eq (b 2) (b 4) = .ok true := by decide
example : boolOut (boolNot (b 0)) = .ok 1 := by decide
example : boolOut (boolBinary .add (b 2) (b 4)) =
    .error (.stuck "not a boolean operation") := by decide
example : u8Out (u8Binary true .add (u 257) (u 0)) = .ok 1 := by decide
example : u8Out (u8Binary true .add (u 511) (u 1)) =
    .error (.revert (Solidity.Source.panicData .arithmetic)) := by decide
example : u8Out (u8Binary false .add (u 511) (u 1)) = .ok 0 := by decide
example : u8Out (uncheckedU8Add .legacy (u 511) (u 1)) = .ok 512 := by decide
example : u8Out (uncheckedU8Add .viaIR (u 511) (u 1)) = .ok 0 := by decide
example : uncheckedU8Add .legacy (u 511) (u 1) ≠ uncheckedU8Add .viaIR (u 511) (u 1) := by
  intro same
  have observed := congrArg u8Out same
  have legacy : u8Out (uncheckedU8Add .legacy (u 511) (u 1)) = .ok 512 := by decide
  have viaIR : u8Out (uncheckedU8Add .viaIR (u 511) (u 1)) = .ok 0 := by decide
  rw [legacy,viaIR] at observed
  cases observed
example (checked : Bool) : u8Binary checked .div (u 257) (u 256) =
    .error (.revert (Solidity.Source.panicData .divZero)) := u8_div_zero checked _
example (checked : Bool) : u8Binary checked .mod (u 257) (u 256) =
    .error (.revert (Solidity.Source.panicData .divZero)) := u8_mod_zero checked _

def pair : LocalValues env [.int Solidity.Source.IntTy.u8,.int Solidity.Source.IntTy.u8] :=
  (u 257,(u 511,()))
example : (copy pair (.there .here) .here).get (.there .here) = u 257 := copy_read _ _ _
example : (copy pair (.there .here) .here).get .here = u 257 := rfl
example : ((copy pair (.there .here) .here).get (.there .here)).clean? = none := rfl
example : (assign pair (.there .here) (u8Binary true .add (u 257) (u 0))).map
    (fun after => (scalarWord (after.get (.there .here)) (u8Shape env)).val) = .ok 1 := by decide
example : (assign pair .here (u8Binary true .add (u 511) (u 1))).map
    (fun after => (scalarWord (after.get .here) (u8Shape env)).val) =
      .error (.revert (Solidity.Source.panicData .arithmetic)) := by decide

/-- Actual mixed Source context: write raw bool2, run the Source ! value
operation, assign its typed result and re-observe through the Yul cell view. -/
def mixed := LocalBlock.initial.1.writeScalar .here (boolShape LocalBlock.env) (word 2)
def negateMixed : Solidity.Source.R (LocalValues LocalBlock.env LocalBlock.ctx.tys) :=
  assign mixed .here (boolNot (mixed.get .here))
example : negateMixed.map (fun after => (localWordCells LocalBlock.ctx after LocalBlock.flag).val) =
    .ok 0 := by decide
example : negateMixed.map (fun after => after.get (.there .here)) =
    .ok (mixed.get (.there .here)) := assign_other mixed .here (.there .here) (by decide) _
def witness : LocalValue env (.int Solidity.Source.IntTy.u8) :=
  .scalar (u8Shape env) (word 512)
example : Nonempty (LocalValue env (.int Solidity.Source.IntTy.u8)) := ⟨witness⟩
#print axioms Solidity.Yul.LocalOperations.u8_div_zero
#print axioms Solidity.Yul.LocalOperations.assign_other
end Solidity.Yul.Checks.LocalOperations
