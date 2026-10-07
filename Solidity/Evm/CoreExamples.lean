import Solidity.Evm.Examples
import Solidity.Evm.CoreCompile

/-!
# The scoped compiler at work

`Evm/Examples.lean`'s programs, resolved into the scoped syntax
(`Prog.resolve`) and compiled by `Evm/CoreCompile.lean`: the same runs, and
the same code up to the memory cells (`sameCode`).  `resolve` does not
reduce in the elaborator's `whnf`, so the checks run in the kernel
(`decide +kernel`), which evaluates the resolution with the compiler.
-/

namespace Solidity.Evm.Core.Examples

open Solidity.Evm.Examples

local instance : InContract := ⟨StandardExample⟩

/-- `P` resolved from no locals, or the empty program if it does not resolve. -/
def scopedOf {C : Contract} (P : Solidity.Prog C) : (Γ' : Solidity.Core.Ctx) × Solidity.Core.Prog C [] Γ' :=
  match Solidity.Core.Prog.resolve [] P with
  | .ok ⟨Γ', P'⟩ => ⟨Γ'.ctx, P'⟩
  | .error _ => ⟨[], .nil⟩

/-- The code of `P`, scoped. -/
def codeOf {C : Contract} (P : Solidity.Prog C) : List Instr := compileProg 0 (scopedOf P).2

def code (P : Solidity.Prog StandardExample) : String := "; ".intercalate ((codeOf P).map toString)

abbrev slotAfter {C : Contract} (P : Solidity.Prog C) (s : Slot) (m : Machine := fresh) :
    Option Nat :=
  Examples.storeAt (run (codeOf P) m) s

abbrev reverts {C : Contract} (P : Solidity.Prog C) (m : Machine := fresh) : Bool :=
  reverted (run (codeOf P) m)

/-- `P` resolves and is in the compiled fragment, from no locals. -/
abbrev compiles {C : Contract} (P : Solidity.Prog C) : Bool :=
  (Solidity.Core.Prog.resolve [] P).toBool && (inFragP (Frag.init []) (scopedOf P).2).isSome

/-- Both compilers give the same code, up to the memory cells. -/
abbrev sameCode {C : Contract} (P : Solidity.Prog C) : Bool :=
  (codeOf P).map Instr.forgetCell == (Evm.compileProg P).map Instr.forgetCell

/-! ## Storage writes -/

/-- info: PUSH 10; PUSH @11; PUSH 2; ADD; SSTORE -/
#guard_msgs in #eval IO.println (code setAge)

theorem setAge_run : slotAfter setAge (.root 13) = some 10 := by decide +kernel

theorem mappings_run :
    slotAfter mappings (.hash 7 (.root 5) 0) = some 5 ∧ slotAfter mappings (.root 0) = some 5 ∧
    slotAfter mappings (.hash 7 (.root 7) 2) = some 3 := by
  decide +kernel

/-- A storage alias lives at level `0`. -/
theorem alias_run : slotAfter alias (.root 0) = some 9 := by decide +kernel

/-- info: PUSH 3; MSTORE %0; MLOAD %0; PUSH 4; DUP2; ADD; DUP1; DUP3; GT; ISZERO; JUMPI +1; REVERT; SWAP1; POP; MSTORE %0 -/
#guard_msgs in #eval IO.println (code (sol{ uint x = 3; x += 4; } : Solidity.Prog StandardExample))

theorem locals_run : slotAfter locals (.root 1) = some 7 := by decide +kernel

/-! ## Checked arithmetic -/

theorem overflow_run : reverts overflow = true := by decide +kernel

theorem checks_run :
    reverts sol{ total = 340282366920938463463374607431768211456; total *= total; } = true ∧
    slotAfter sol{ total = 3; total *= 4; } (.root 0) = some 12 ∧
    reverts sol{ total = 3; total -= 4; } = true ∧
    reverts sol{ total = 1 / age; } = true := by
  decide +kernel

theorem incDec_run :
    let o := run (codeOf sol{ total = 3; total++; uint x = 1; x++; age = x; }) (fresh)
    Examples.storeAt o (.root 0) = some 4 ∧ Examples.storeAt o (.root 1) = some 2 ∧
    reverts sol{
      total = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
      total++; } = true := by
  decide +kernel

theorem shortCircuit_run :
    reverts sol{ require(total == 0 || total / total == 1); } = false := by
  decide +kernel

/-! ## Control flow, `delete`, arrays, `transfer` -/

theorem ite_run :
    slotAfter sol{ total = 5; if (total > 3) { age = 1; } else { age = 2; }; } (.root 1)
      = some 1 := by
  decide +kernel

/-- A branch's local ends with it: `x` and `y` share level `0`, and the
`uint z` declared after the `if` lives there too. -/
theorem scopedBranch_run :
    slotAfter sol{
      if (total == 0) { uint x = 4; age = x; } else { uint y = 5; age = y; }
      uint z = 2; total = z + age; } (.root 0) = some 6 := by
  decide +kernel

theorem delete_run :
    let o := run (codeOf sol{
      alice.age = 10; alice.account.balance = 4; delete alice; }) (fresh)
    Examples.storeAt o (.root 11) = some 0 ∧ Examples.storeAt o (.root 13) = some 0 := by
  decide +kernel

theorem deleteMapping_run :
    let o := run (codeOf sol{ wallet.stash[3] = 7; wallet.owner = 1; delete wallet; }) (fresh)
    Examples.storeAt o (.root 17) = some 0 ∧ Examples.storeAt o (.hash 3 (.root 18) 0) = some 7 := by
  decide +kernel

theorem arrays_revert :
    reverts sol{ values[0] = 1; } = true ∧ reverts sol{ values.pop(); } = true := by
  decide +kernel

theorem arrays_run :
    let o := run (codeOf sol{ values[1] = 7; values.pop(); })
      { fresh with store := upd (fun _ => 0) (.root 4) 2 }
    Examples.storeAt o (.data (.root 4) 1) = some 7 ∧ Examples.storeAt o (.root 4) = some 1 := by
  decide +kernel

theorem payOwner_wt : compiles payOwner := by decide +kernel

theorem payOwner_run :
    (match run (codeOf payOwner) (fresh 100) with
      | .ok m 0 => some (m.bal 0, m.bal 5, m.bal₀ 0, m.bal₀ 5, m.self)
      | _ => none) = some (70, 30, 100, 0, 0) := by
  decide +kernel

theorem transfer_refused :
    reverts sol{ owner.transfer(200); } (fresh 100) = true ∧
    reverts payOwner { fresh 100 with accepts := fun a _ => a != 5 } = true := by
  decide +kernel

theorem transfer_self :
    (match run (codeOf sol{ owner = 0; owner.transfer(30); }) (fresh 100) with
      | .ok m 0 => some (m.bal 0)
      | _ => none) = some 100 := by
  decide +kernel

theorem envReads_wt : compiles envReads := by decide +kernel

theorem envReads_run :
    let o := run (codeOf envReads) { fresh with caller := 7, callvalue := 100 }
    Examples.storeAt o (rootSlot StandardExample "owner") = some 7 ∧ Examples.storeAt o (.root 0) = some 100 := by
  decide +kernel

theorem selfBalance_out :
    compiles (sol{ total = address(this).balance; } : Solidity.Prog StandardExample) = false := by
  decide +kernel

/-! ## Lengths, `v = x++`, copies, `push` -/

theorem length_run :
    slotAfter sol{ total = values.length; } (.root 0)
      { fresh with store := upd (fun _ => 0) (.root 4) 3 } = some 3 := by
  decide +kernel

theorem bumps_wt : compiles bumps := by decide +kernel

theorem bumps_run :
    slotAfter bumps (.root 0) = some 5 ∧ slotAfter bumps (.root 1) = some 7 := by
  decide +kernel

theorem bumpStore_run :
    let o := run (codeOf sol{ total = 5; uint y = total++; age = y; }) fresh
    Examples.storeAt o (.root 0) = some 6 ∧ Examples.storeAt o (.root 1) = some 5 := by
  decide +kernel

theorem copyPerson_wt : compiles copyPerson := by decide +kernel

theorem copyPerson_run :
    slotAfter copyPerson (.root 16) = some 7 ∧ slotAfter copyPerson (.root 14) = some 3 := by
  decide +kernel

theorem pushes2_wt : compiles pushes2 := by decide +kernel

theorem pushes2_run :
    slotAfter pushes2 (.root 0) = some 2 ∧ slotAfter pushes2 (.data (.root 4) 0) = some 7 := by
  decide +kernel

theorem pushPerson_run :
    slotAfter sol{ alice.age = 9; persons.push(alice); } (.data (.root 9) 2) = some 9 := by
  decide +kernel

theorem pushLimit_run :
    reverts sol{ values.push(1); } { fresh with store := upd (fun _ => 0) (.root 4) Lmax }
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pow_run :
    slotAfter sol{ total = 3 ** 5; } (.root 0) = some 243 ∧
    slotAfter sol{ total = 0 ** 0; } (.root 0) = some 1 ∧
    slotAfter sol{ total = 2 ** 255; } (.root 0) = some (2 ^ 255) ∧
    reverts sol{ total = 2 ** 256; } = true := by
  decide +kernel

theorem pow_wt : compiles (sol{ total = 3 ** 5; } : Solidity.Prog StandardExample) := by
  decide +kernel

/-! ## What the fragment leaves out -/

theorem elemAlias_wt : compiles elemAlias := by decide +kernel

theorem elemAlias_run :
    let o := run (codeOf elemAlias) { fresh with store := upd (fun _ => 0) (.root 9) 1 }
    Examples.storeAt o (.data (.root 9) 2) = some 7 ∧ Examples.storeAt o (.root 0) = some 7 := by
  decide +kernel

/-- `inFrag` rejects what `wtProg` rejects: a `push()` of a struct, a memory
local, a copy of a struct holding a dynamic array, a fragile alias read after
a `pop`; and, through a branch, an alias forgotten by a `pop` in it. -/
theorem rejected :
    compiles (sol{ persons.push(); } : Solidity.Prog StandardExample) = false ∧
    compiles (sol{ Person memory m; } : Solidity.Prog StandardExample) = false ∧
    compiles (sol[TestSuite]{ basketA = basketB; } : Solidity.Prog TestSuite) = false ∧
    compiles (sol{ Person storage p = persons[0]; persons.pop(); p.age = 1; } :
      Solidity.Prog StandardExample) = false ∧
    compiles (sol{ Person storage p = persons[0];
        if (total == 0) { persons.pop(); } else { }; p.age = 1; } :
      Solidity.Prog StandardExample) = false := by
  decide +kernel

/-! ## Calls -/

/-- `y` lives at level `0`, `addTwo`'s parameter and return variable at `1`
and `2`, above it, and each call of `addOne` in `addTwo`'s body at `3` and
`4`: the second call's frame reuses the first one's cells. -/
theorem callTwice_wt : compiles callTwice := by decide +kernel

/--
info: PUSH 0; MSTORE %0; PUSH 3; MSTORE %1; PUSH 0; MSTORE %2;
MLOAD %1; MSTORE %3; PUSH 0; MSTORE %4; MLOAD %3; PUSH 1;
DUP2; ADD; DUP1; DUP3; GT; ISZERO; JUMPI +1; REVERT; SWAP1; POP;
MSTORE %4; MLOAD %4; MSTORE %2;
MLOAD %2; MSTORE %3; PUSH 0; MSTORE %4; MLOAD %3; PUSH 1;
DUP2; ADD; DUP1; DUP3; GT; ISZERO; JUMPI +1; REVERT; SWAP1; POP;
MSTORE %4; MLOAD %4; MSTORE %2;
MLOAD %2; MSTORE %0; MLOAD %0; PUSH @0; SSTORE
-/
#guard_msgs in #eval do
  let c := (codeOf callTwice).map toString
  for (i, n) in [(0, 6), (6, 6), (12, 10), (22, 3), (25, 6), (31, 10), (41, 3), (44, 5)] do
    IO.println ("; ".intercalate ((c.drop i).take n) ++ (if i + n < c.length then ";" else ""))

theorem callTwice_run :
    slotAfter callTwice (rootSlot CallsExample "total") = some 5 := by
  decide +kernel

/-! ## Signed arithmetic, fixed-size arrays -/

section Signed

local instance : InContract := ⟨TestSuite⟩

theorem signed_wt : compiles signed := by decide +kernel

theorem signed_run :
    slotAfter signed (rootSlot TestSuite "signedTotal") = some (toWord (-13)) := by
  decide +kernel

theorem sdivmod_run :
    slotAfter sol{ int x = -7; signedTotal = x / 2; } (rootSlot TestSuite "signedTotal")
      = some (toWord (-3)) ∧
    slotAfter sol{ int x = -7; signedTotal = x % 2; } (rootSlot TestSuite "signedTotal")
      = some (toWord (-1)) ∧
    slotAfter sol{ signedTotal = -7; signedTotal = -signedTotal; }
      (rootSlot TestSuite "signedTotal") = some 7 := by
  decide +kernel

theorem signedChecks_run :
    reverts sol{
      signedTotal = 57896044618658097711785492504343953926634992332820282019728792003956564819967;
      signedTotal += 1; } = true ∧
    reverts sol{
      signedTotal = -57896044618658097711785492504343953926634992332820282019728792003956564819968;
      signedTotal -= 1; } = true ∧
    reverts sol{
      signedTotal = -57896044618658097711785492504343953926634992332820282019728792003956564819968;
      signedTotal /= -1; } = true ∧
    reverts sol{
      signedTotal = -57896044618658097711785492504343953926634992332820282019728792003956564819968;
      signedTotal = -signedTotal; } = true ∧
    reverts sol{
      signedTotal = -57896044618658097711785492504343953926634992332820282019728792003956564819968;
      signedTotal *= -1; } = true ∧
    slotAfter sol{ int x = -1; if (x < 0) { total = 1; } else { total = 2; }; }
      (rootSlot TestSuite "total") = some 1 := by
  decide +kernel

theorem copyFixed_run :
    slotAfter sol{ triple.items[1] = 4; triple.tag = 9; triple2 = triple; }
      ((rootSlot TestSuite "triple2").add 1) = some 4 ∧
    slotAfter sol{ triple.items[1] = 4; triple.tag = 9; triple2 = triple; }
      ((rootSlot TestSuite "triple2").add 3) = some 9 := by
  decide +kernel

theorem fixedWrite_wt : compiles fixedWrite := by decide +kernel

theorem fixedWrite_run :
    slotAfter fixedWrite ((rootSlot TestSuite "fixedValues").add 2) = some 7 := by
  decide +kernel

theorem fixedOutOfBounds_run :
    reverts (sol{ uint k = 3; fixedValues[k] = 1; } : Solidity.Prog TestSuite) = true := by
  decide +kernel

end Signed

/-! ## The same code as the untyped compiler -/

theorem sameCode_run :
    sameCode setAge ∧ sameCode mappings ∧ sameCode alias ∧ sameCode locals ∧
    sameCode overflow ∧ sameCode payOwner ∧ sameCode envReads ∧ sameCode bumps ∧
    sameCode copyPerson ∧ sameCode pushes2 ∧ sameCode elemAlias ∧ sameCode callTwice ∧
    sameCode signed ∧ sameCode fixedWrite := by
  decide +kernel

end Solidity.Evm.Core.Examples
