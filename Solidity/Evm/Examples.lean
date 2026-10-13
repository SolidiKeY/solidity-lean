import Solidity.Evm.Compile

/-!
# The scoped compiler at work

Programs of `StandardExample`, `CallsExample` and `TestSuite`, elaborated
into the scoped syntax (`sol{ … }` at `Prog C [] _`), compiled by
`Evm/Compile.lean` and run on the machine.  The checks run in the kernel
(`decide +kernel`), which evaluates the compiler and the machine.
-/

namespace Solidity.Evm.Examples

open Semantics

local instance : InContract := ⟨StandardExample⟩

/-- The word at slot `s` after a run that succeeded. -/
def storeAt : Out → Slot → Option Nat
  | .ok m _, s => some (m.store s)
  | _, _ => none

/-- Whether a run reverted. -/
def reverted : Out → Bool
  | .revert => true
  | _ => false

/-- A run the checker saw revert reverted: `total += 1;` at `2^256 - 1`. -/
theorem reverted_eq {o : Out} (h : reverted o = true) : o = .revert := by
  cases o <;> simp_all [reverted]

/-- A fresh `StandardExample` at address `0`, its account holding `balance`,
every other account empty. -/
abbrev fresh (balance : Nat := 0) : Machine :=
  Machine.init (fun a => if a = 0 then balance else 0) 0

/-! ## Layout -/

/-- `alice` is the twelfth slot: after four `uint`s and seven one-slot
arrays and mappings. -/
theorem alice_slot : rootSlot StandardExample "alice" = .root 11 := rfl

/-- `Person` is an `Account` (`balance`, and a `Token` of one `value`) and an
`age`: three slots, `age` the third. -/
theorem person_layout : size (.ref (.struct "Person")) = 3 ∧ offset "Person" "age" = 2 := by
  decide

/-! ## The programs

The layout of `StandardExample`: `total`, `age`, `owner`, `balance` are slots
`0`–`3`, `values` is `4`, `balances` `5`, `flags` `6`, `folks` `7`, `matrix`
`8`, `persons` `9`, `people` `10`, `alice` `[11, 14)`, `bob` `[14, 17)`,
`wallet` `[17, 19)`. -/

/-- `alice.age = 10;` -/
def setAge := (sol{ alice.age = 10; } : Prog StandardExample [] _)

/-- `balances[7] = 5; total = balances[7] + balances[8]; folks[7].age = 3;` -/
def mappings :=
  (sol{ balances[7] = 5; total = balances[7] + balances[8]; folks[7].age = 3; } :
    Prog StandardExample [] _)

/-- `Person storage p = folks[7]; p.age = 9; total = folks[7].age;` -/
def alias := (sol{
  Person storage p = folks[7]; p.age = 9; total = folks[7].age;
} : Prog StandardExample [] _)

/-- `uint x = 3; x += 4; age = x > 5 ? x : 0;` -/
def locals := (sol{ uint x = 3; x += 4; age = x > 5 ? x : 0; } : Prog StandardExample [] _)

/-- `total = 2^256 - 1; total += 1;` -/
def overflow := (sol{
  total = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
  total += 1;
} : Prog StandardExample [] _)

/-- `owner = 5; owner.transfer(30);` -/
def payOwner := (sol{ owner = 5; owner.transfer(30); } : Prog StandardExample [] _)

/-- `owner = msg.sender; total = msg.value;`, called by `7` with `100`:
`CALLER` and `CALLVALUE` push them. -/
def envReads := (sol{ owner = msg.sender; total = msg.value; } : Prog StandardExample [] _)

/-- `uint x = 5; uint y = x++; total = y; age = ++x;`: `x++` is the old value,
`++x` the new one. -/
def bumps :=
  (sol{ uint x = 5; uint y = x++; total = y; y = ++x; age = y; } : Prog StandardExample [] _)

/-- `alice.age = 7; alice.account.balance = 3; bob = alice;` copies `alice`'s
three slots onto `bob`'s: `bob.age` is slot `16`, `bob.account.balance` `14`. -/
def copyPerson :=
  (sol{ alice.age = 7; alice.account.balance = 3; bob = alice; } : Prog StandardExample [] _)

/-- `values.push(7); values.push(); total = values.length;`: two elements, the
first `7` at `keccak(4)`, the length `2`. -/
def pushes2 :=
  (sol{ values.push(7); values.push(); total = values.length; } : Prog StandardExample [] _)

/-- An alias bound through an array index: `persons[0]`'s slot, its index
checked once, when it is bound.  With one person on the machine, writing
`p.age` writes `keccak(9) + 2`, which `persons[0].age` reads back. -/
def elemAlias :=
  (sol{ Person storage p = persons[0]; p.age = 7; total = persons[0].age; } :
    Prog StandardExample [] _)

/-- `uint y = addTwo(3); total = y;` over `CallsExample`: `addTwo` calls
`addOne` twice. -/
def callTwice := (sol[CallsExample]{ uint y = addTwo(3); total = y; } : Prog CallsExample [] _)

section Signed

local instance : InContract := ⟨TestSuite⟩

/-- `int x = -5; int y = 3; signedTotal = x * y + 2;` -/
def signed := (sol{ int x = -5; int y = 3; signedTotal = x * y + 2; } : Prog TestSuite [] _)

/-- `uint[3]` takes three slots; `Token[2]` two; a `FixedTriple`
(`uint[3] items; uint tag;`) four, `tag` the fourth.  solc lays a
fixed-size array out inline, from its own slot, with no length slot. -/
theorem fixed_layout :
    size (.ref (.fixed .uint 3)) = 3 ∧ size (.ref (.fixed (.ref (.struct "Token")) 2)) = 2 ∧
      size (.ref (.struct "FixedTriple")) = 4 ∧ offset "FixedTriple" "tag" = 3 := by
  decide

/-- `fixedValues[2] = 7;` -/
def fixedWrite := (sol{ fixedValues[2] = 7; } : Prog TestSuite [] _)

end Signed

end Solidity.Evm.Examples

namespace Solidity.Evm.Examples

open Solidity.Evm.Examples

local instance : InContract := ⟨StandardExample⟩

/-- The code of `P`. -/
def codeOf {C : Contract} {Γ' : Solidity.Ctx} (P : Solidity.Prog C [] Γ') : List Instr :=
  compileProg 0 P

def code {Γ' : Solidity.Ctx} (P : Solidity.Prog StandardExample [] Γ') : String :=
  "; ".intercalate ((codeOf P).map toString)

abbrev slotAfter {C : Contract} {Γ' : Solidity.Ctx} (P : Solidity.Prog C [] Γ') (s : Slot)
    (m : Machine := fresh) : Option Nat :=
  Examples.storeAt (run (codeOf P) m) s

abbrev reverts {C : Contract} {Γ' : Solidity.Ctx} (P : Solidity.Prog C [] Γ')
    (m : Machine := fresh) : Bool :=
  reverted (run (codeOf P) m)

/-- `P` is in the compiled fragment, from no locals. -/
abbrev compiles {C : Contract} {Γ' : Solidity.Ctx} (P : Solidity.Prog C [] Γ') : Bool :=
  (inFragP (Frag.init []) P).isSome

/-- `inFrag` rejects `P`. -/
abbrev rejects {C : Contract} {Γ' : Solidity.Ctx} (P : Solidity.Prog C [] Γ') : Bool :=
  (inFragP (Frag.init []) P).isNone

/-! ## Storage writes -/

/-- info: PUSH 10; PUSH @11; PUSH 2; ADD; SSTORE -/
#guard_msgs in #eval IO.println (code setAge)

theorem setAge_run : slotAfter setAge (.root 13) = some 10 := by decide +kernel

-- `total = total + age;`: both reads, then `ADD` and solc's overflow check
-- (the sum wrapping below `total` reverts), then the write.
/--
info: PUSH @0; SLOAD; PUSH @1; SLOAD;
DUP2; ADD; DUP1; DUP3; GT; ISZERO; JUMPI +1; REVERT; SWAP1; POP;
PUSH @0; SSTORE
-/
#guard_msgs in #eval
  let c := (codeOf sol{ total = total + age; }).map toString
  do
  IO.println ("; ".intercalate (c.take 4) ++ ";")
  IO.println ("; ".intercalate ((c.drop 4).take 10) ++ ";")
  IO.println ("; ".intercalate (c.drop 14))

/-- info: PUSH 3; PUSH @7; PUSH 7; KECCAK256; PUSH 2; ADD; SSTORE -/
#guard_msgs in #eval IO.println (code sol{ folks[7].age = 3; })

theorem mappings_run :
    slotAfter mappings (.hash 7 (.root 5) 0) = some 5 ∧ slotAfter mappings (.root 0) = some 5 ∧
    slotAfter mappings (.hash 7 (.root 7) 2) = some 3 := by
  decide +kernel

/-- A storage alias lives at level `0`. -/
theorem alias_run : slotAfter alias (.root 0) = some 9 := by decide +kernel

/-- info: PUSH 3; MSTORE %0; MLOAD %0; PUSH 4; DUP2; ADD; DUP1; DUP3; GT; ISZERO; JUMPI +1; REVERT; SWAP1; POP; MSTORE %0 -/
#guard_msgs in #eval IO.println (code sol{ uint x = 3; x += 4; })

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
    compiles sol{ require(total == 0 || total / total == 1); } ∧
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
    compiles sol{ alice.age = 10; alice.account.balance = 4; delete alice; } ∧
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
      { fresh with store := WordStore.write WordStore.zero (.root 4) 2 }
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
    compiles sol{ owner = 0; owner.transfer(30); } ∧
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
    rejects (sol{ total = address(this).balance; } : Solidity.Prog StandardExample [] _) := by
  decide +kernel

/-! ## Lengths, `v = x++`, copies, `push` -/

theorem length_run :
    slotAfter sol{ total = values.length; } (.root 0)
      { fresh with store := WordStore.write WordStore.zero (.root 4) 3 } = some 3 := by
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
    reverts sol{ values.push(1); } { fresh with store := WordStore.write WordStore.zero (.root 4) Lmax }
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pow_run :
    slotAfter sol{ total = 3 ** 5; } (.root 0) = some 243 ∧
    slotAfter sol{ total = 0 ** 0; } (.root 0) = some 1 ∧
    slotAfter sol{ total = 2 ** 255; } (.root 0) = some (2 ^ 255) ∧
    reverts sol{ total = 2 ** 256; } = true := by
  decide +kernel

theorem pow_wt : compiles (sol{ total = 3 ** 5; } : Solidity.Prog StandardExample [] _) := by
  decide +kernel

/-! ## What the fragment leaves out -/

theorem elemAlias_wt : compiles elemAlias := by decide +kernel

theorem elemAlias_run :
    let o := run (codeOf elemAlias) { fresh with store := WordStore.write WordStore.zero (.root 9) 1 }
    Examples.storeAt o (.data (.root 9) 2) = some 7 ∧ Examples.storeAt o (.root 0) = some 7 := by
  decide +kernel

/-- `inFrag` rejects a `push()` of a struct, a memory
local, a copy of a struct holding a dynamic array, a fragile alias read after
a `pop`; and, through a branch, an alias forgotten by a `pop` in it. -/
theorem rejected :
    rejects (sol{ persons.push(); } : Solidity.Prog StandardExample [] _) ∧
    rejects (sol{ Person memory m; } : Solidity.Prog StandardExample [] _) ∧
    rejects (sol[TestSuite]{ basketA = basketB; } : Solidity.Prog TestSuite [] _) ∧
    rejects (sol{ Person storage p = persons[0]; persons.pop(); p.age = 1; } :
      Solidity.Prog StandardExample [] _) ∧
    rejects (sol{ Person storage p = persons[0];
        if (total == 0) { persons.pop(); } else { }; p.age = 1; } :
      Solidity.Prog StandardExample [] _) := by
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
    reverts (sol{ uint k = 3; fixedValues[k] = 1; } : Solidity.Prog TestSuite [] _) = true := by
  decide +kernel

end Signed

end Solidity.Evm.Examples
