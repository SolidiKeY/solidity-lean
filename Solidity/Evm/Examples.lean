import Solidity.Evm.Correctness

/-!
# The compiler at work

Programs of `StandardExample` compiled and run on the machine, each run
checked by `decide` (the kernel runs the machine); and the headline theorems
applied to them, which turns a machine run into a fact about the interpreter:
`alice.age = 10;` makes the interpreter's `alice.age` read `10`
(`setAge_interpreter`), and `total += 1;` at `2^256 - 1` makes it revert
(`overflow_interpreter`) — neither by running the interpreter, whose storage
defaults (`defaultForTy`) the kernel does not unfold.

The layout of `StandardExample`: `total`, `age`, `owner`, `balance` are slots
`0`–`3`, `values` is `4`, `balances` `5`, `flags` `6`, `folks` `7`, `matrix`
`8`, `persons` `9`, `people` `10`, `alice` `[11, 14)`, `bob` `[14, 17)`,
`wallet` `[17, 19)`.
-/

namespace Solidity
namespace Evm
namespace Examples

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

/-- A fresh `StandardExample` holding `balance` in funds. -/
abbrev fresh (balance : Nat := 0) : Machine := Machine.init balance

def code (P : Prog StandardExample) : String := "; ".intercalate ((compileProg P).map toString)

/-! ## Layout -/

/-- `alice` is the twelfth slot: after four `uint`s and seven one-slot
arrays and mappings. -/
theorem alice_slot : rootSlot StandardExample "alice" = .root 11 := rfl

/-- `Person` is an `Account` (`balance`, and a `Token` of one `value`) and an
`age`: three slots, `age` the third. -/
theorem person_layout : size (.ref (.struct "Person")) = 3 ∧ offset "Person" "age" = 2 := by
  decide

/-! ## Storage writes -/

/-- `alice.age = 10;` -/
def setAge : Prog StandardExample := sol{ alice.age = 10; }

/-- info: PUSH 10; PUSH @11; PUSH 2; ADD; SSTORE -/
#guard_msgs in #eval IO.println (code setAge)

/-- `alice.age = 10;` writes `10` to slot `13`. -/
theorem setAge_run : storeAt (run (compileProg setAge) (fresh)) (.root 13) = some 10 := by decide

/-- `balances[7] = 5; total = balances[7] + balances[8]; folks[7].age = 3;` -/
def mappings : Prog StandardExample :=
  sol{ balances[7] = 5; total = balances[7] + balances[8]; folks[7].age = 3; }

/-- `total = total + age;`: both reads, then `ADD` and solc's overflow check
(the sum wrapping below `total` reverts), then the write. -/
def checkedAdd : Prog StandardExample := sol{ total = total + age; }

/--
info: PUSH @0; SLOAD; PUSH @1; SLOAD;
DUP2; ADD; DUP1; DUP3; GT; ISZERO; JUMPI +1; REVERT; SWAP1; POP;
PUSH @0; SSTORE
-/
#guard_msgs in #eval do
  let c := (compileProg checkedAdd).map toString
  IO.println ("; ".intercalate (c.take 4) ++ ";")
  IO.println ("; ".intercalate ((c.drop 4).take 10) ++ ";")
  IO.println ("; ".intercalate (c.drop 14))

/-- info: PUSH 3; PUSH @7; PUSH 7; KECCAK256; PUSH 2; ADD; SSTORE -/
#guard_msgs in #eval IO.println (code sol{ folks[7].age = 3; })

/-- `balances[7]` is `keccak(7, 5)`, `folks[7].age` is `keccak(7, 7) + 2`, and
`total` reads the sum `5 + 0`. -/
theorem mappings_run :
    storeAt (run (compileProg mappings) (fresh)) (.hash 7 (.root 5) 0) = some 5 ∧
    storeAt (run (compileProg mappings) (fresh)) (.root 0) = some 5 ∧
    storeAt (run (compileProg mappings) (fresh)) (.hash 7 (.root 7) 2) = some 3 := by
  decide

/-- `Person storage p = folks[7]; p.age = 9; total = folks[7].age;` -/
def alias : Prog StandardExample := sol{
  Person storage p = folks[7]; p.age = 9; total = folks[7].age;
}

/-- Writing through the alias writes `folks[7].age`, which `total` then reads. -/
theorem alias_run : storeAt (run (compileProg alias) (fresh)) (.root 0) = some 9 := by decide

/-- `uint x = 3; x += 4; age = x > 5 ? x : 0;` -/
def locals : Prog StandardExample := sol{ uint x = 3; x += 4; age = x > 5 ? x : 0; }

/-- A local lives in a memory cell; `?:` runs only the branch it picks. -/
theorem locals_run : storeAt (run (compileProg locals) (fresh)) (.root 1) = some 7 := by decide

/-! ## Checked arithmetic -/

/-- `total = 2^256 - 1; total += 1;` -/
def overflow : Prog StandardExample := sol{
  total = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
  total += 1;
}

/-- The sum wraps to `0`, below `2^256 - 1`: the guard reverts. -/
theorem overflow_run : reverted (run (compileProg overflow) (fresh)) = true := by decide

/-- `total = 2^128; total *= total;` overflows; `total = 3; total *= 4;` does
not; `total = 3; total -= 4;` underflows; `total = 1 / age;` divides by zero. -/
theorem checks_run :
    reverted (run (compileProg sol{
      total = 340282366920938463463374607431768211456; total *= total; }) (fresh)) = true ∧
    storeAt (run (compileProg sol{ total = 3; total *= 4; }) (fresh)) (.root 0) = some 12 ∧
    reverted (run (compileProg sol{ total = 3; total -= 4; }) (fresh)) = true ∧
    reverted (run (compileProg sol{ total = 1 / age; }) (fresh)) = true := by
  decide

/-- `total = 3; total++; uint x = 1; x++; age = x;` counts up; `++` past
`2^256 - 1` reverts like `+= 1`. -/
theorem incDec_run :
    let o := run (compileProg sol{ total = 3; total++; uint x = 1; x++; age = x; }) (fresh)
    storeAt o (.root 0) = some 4 ∧ storeAt o (.root 1) = some 2 ∧
    reverted (run (compileProg sol{
      total = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
      total++; }) (fresh)) = true := by
  decide

/-- `require(total == 0 || total / total == 1);` passes on a fresh contract:
`||` does not evaluate its right operand, whose division would revert. -/
theorem shortCircuit_run :
    reverted (run (compileProg sol{ require(total == 0 || total / total == 1); }) (fresh))
      = false := by
  decide

/-! ## Control flow, `delete`, arrays, `transfer` -/

/-- `total = 5; if (total > 3) { age = 1; } else { age = 2; }` takes the first
branch and skips the second. -/
theorem ite_run :
    storeAt (run (compileProg sol{ total = 5; if (total > 3) { age = 1; } else { age = 2; }; })
      (fresh)) (.root 1) = some 1 := by
  decide

/-- `alice.age = 10; alice.account.balance = 4; delete alice;` zeroes all three
of `alice`'s slots. -/
theorem delete_run :
    let o := run (compileProg sol{
      alice.age = 10; alice.account.balance = 4; delete alice; }) (fresh)
    storeAt o (.root 11) = some 0 ∧ storeAt o (.root 13) = some 0 := by
  decide

/-- `wallet.stash[3] = 7; wallet.owner = 1; delete wallet;` zeroes `owner`
and leaves the mapping's entry: `delete` does not reach into a mapping. -/
theorem deleteMapping_run :
    let o := run (compileProg sol{ wallet.stash[3] = 7; wallet.owner = 1; delete wallet; }) (fresh)
    storeAt o (.root 17) = some 0 ∧ storeAt o (.hash 3 (.root 18) 0) = some 7 := by
  decide

/-- On a fresh contract `values` is empty: `values[0] = 1;` fails the bounds
check and `values.pop();` the emptiness check. -/
theorem arrays_revert :
    reverted (run (compileProg sol{ values[0] = 1; }) (fresh)) = true ∧
    reverted (run (compileProg sol{ values.pop(); }) (fresh)) = true := by
  decide

/-- With `values` of length `2` on the machine, `values[1] = 7; values.pop();`
writes `keccak(4) + 1` and leaves the length `1`. -/
theorem arrays_run :
    let o := run (compileProg sol{ values[1] = 7; values.pop(); })
      { fresh with store := upd (fun _ => 0) (.root 4) 2 }
    storeAt o (.data (.root 4) 1) = some 7 ∧ storeAt o (.root 4) = some 1 := by
  decide

/-- `owner = 5; owner.transfer(30);` with `100` in funds leaves `70` and records
`-30` for address `5`; `owner.transfer(200);` reverts. -/
theorem transfer_run :
    (match run (compileProg sol{ owner = 5; owner.transfer(30); }) (fresh 100) with
      | .ok m _ => some (m.balance, m.net 5)
      | _ => none) = some (70, -30) ∧
    reverted (run (compileProg sol{ owner.transfer(200); }) (fresh 100)) = true := by
  decide

/-! ## Lengths, `v = x++`, copies, `push` -/

/-- `total = values.length;` reads the length slot: with `3` elements on the
machine, `total` is `3`. -/
theorem length_run :
    storeAt (run (compileProg sol{ total = values.length; })
      { fresh with store := upd (fun _ => 0) (.root 4) 3 }) (.root 0) = some 3 := by
  decide

/-- `uint x = 5; uint y = x++; total = y; age = ++x;`: `x++` is the old value,
`++x` the new one. -/
def bumps : Prog StandardExample := sol{ uint x = 5; uint y = x++; total = y; y = ++x; age = y; }

theorem bumps_wt : (wtProg (fun _ => none) bumps).isSome := by decide

theorem bumps_run :
    storeAt (run (compileProg bumps) fresh) (.root 0) = some 5 ∧
    storeAt (run (compileProg bumps) fresh) (.root 1) = some 7 := by
  decide

/-- `total = 5; uint y = total++; age = y;` on a storage target. -/
theorem bumpStore_run :
    let o := run (compileProg sol{ total = 5; uint y = total++; age = y; }) fresh
    storeAt o (.root 0) = some 6 ∧ storeAt o (.root 1) = some 5 := by
  decide

/-- `alice.age = 7; alice.account.balance = 3; bob = alice;` copies `alice`'s
three slots onto `bob`'s: `bob.age` is slot `16`, `bob.account.balance` `14`. -/
def copyPerson : Prog StandardExample :=
  sol{ alice.age = 7; alice.account.balance = 3; bob = alice; }

theorem copyPerson_wt : (wtProg (fun _ => none) copyPerson).isSome := by decide

theorem copyPerson_run :
    storeAt (run (compileProg copyPerson) fresh) (.root 16) = some 7 ∧
    storeAt (run (compileProg copyPerson) fresh) (.root 14) = some 3 := by
  decide

/-- `values.push(7); values.push(); total = values.length;`: two elements, the
first `7` at `keccak(4)`, the length `2`. -/
def pushes2 : Prog StandardExample := sol{ values.push(7); values.push(); total = values.length; }

theorem pushes2_wt : (wtProg (fun _ => none) pushes2).isSome := by decide

theorem pushes2_run :
    storeAt (run (compileProg pushes2) fresh) (.root 0) = some 2 ∧
    storeAt (run (compileProg pushes2) fresh) (.data (.root 4) 0) = some 7 := by
  decide

/-- `alice.age = 9; persons.push(alice);` copies `alice` into the new element:
its `age` is at `keccak(9) + 2`. -/
theorem pushPerson_run :
    storeAt (run (compileProg sol{ alice.age = 9; persons.push(alice); }) fresh)
      (.data (.root 9) 2) = some 9 := by
  decide

/-- solc's length limit: with `2^64` elements on the machine, `values.push(1);`
reverts (`Panic(0x41)`).  `compile_correct` assumes the arrays stay below it
(`L + pushesP P ≤ 2^64`), which no run of a program with fewer pushes breaks. -/
theorem pushLimit_run :
    reverted (run (compileProg sol{ values.push(1); })
      { fresh with store := upd (fun _ => 0) (.root 4) Lmax }) = true := by
  decide

set_option maxRecDepth 100000 in
/-- `**` is solc's `checked_exp_unsigned`, its loop unrolled (`expLoop`):
`3 ** 5` is `243`, `0 ** 0` is `1`, `2 ** 255` fits and `2 ** 256` reverts.
(The unrolled code is long, and the kernel's evaluation recurses through it.) -/
theorem pow_run :
    storeAt (run (compileProg sol{ total = 3 ** 5; }) fresh) (.root 0) = some 243 ∧
    storeAt (run (compileProg sol{ total = 0 ** 0; }) fresh) (.root 0) = some 1 ∧
    storeAt (run (compileProg sol{ total = 2 ** 255; }) fresh) (.root 0) = some (2 ^ 255) ∧
    reverted (run (compileProg sol{ total = 2 ** 256; }) fresh) = true := by
  decide

theorem pow_wt : (wtProg (fun _ => none) (sol{ total = 3 ** 5; } : Prog StandardExample)).isSome := by
  decide

/-! ## What the fragment leaves out -/

/-- An alias bound through an array index: `persons[0]`'s slot, its index
checked once, when it is bound.  With one person on the machine, writing
`p.age` writes `keccak(9) + 2`, which `persons[0].age` reads back. -/
def elemAlias : Prog StandardExample :=
  sol{ Person storage p = persons[0]; p.age = 7; total = persons[0].age; }

theorem elemAlias_wt : (wtProg (fun _ => none) elemAlias).isSome := by decide

theorem elemAlias_run :
    let o := run (compileProg elemAlias) { fresh with store := upd (fun _ => 0) (.root 9) 1 }
    storeAt o (.data (.root 9) 2) = some 7 ∧ storeAt o (.root 0) = some 7 := by
  decide

/-- `wtProg` rejects a `push()` of a struct (the slot it revives is not
cleared), a memory local, a copy of a struct holding a dynamic array (solc's
copy loop), and a use of an alias bound through an array index after a
`pop` (which may have left its slot past the end; the fragment forgets it,
`TyCtx.dropFragile`). -/
theorem rejected :
    (wtProg (fun _ => none) (sol{ persons.push(); } : Prog StandardExample)).isNone ∧
    (wtProg (fun _ => none) (sol{ Person memory m; } : Prog StandardExample)).isNone ∧
    (wtProg (fun _ => none) (sol[TestSuite]{ basketA = basketB; } : Prog TestSuite)).isNone ∧
    (wtProg (fun _ => none)
      (sol{ Person storage p = persons[0]; persons.pop(); p.age = 1; } :
        Prog StandardExample)).isNone := by
  decide

/-! ## Calls

A call is compiled as symbolic execution runs it, inlined: its arguments
stored in its parameters' cells, its return variable zeroed, its body, the
returned value copied where the call lands (`argsCode`). -/

/-- `uint y = addTwo(3); total = y;` over `CallsExample`: `addTwo` calls
`addOne` twice. -/
def callTwice : Prog CallsExample := sol[CallsExample]{ uint y = addTwo(3); total = y; }

theorem callTwice_wt : (wtProg (fun _ => none) callTwice).isSome := by decide

/-- It writes `5` to `total`, slot `0`. -/
theorem callTwice_run :
    storeAt (run (compileProg callTwice) (Machine.init 0)) (rootSlot CallsExample "total") = some 5 := by
  decide

/-- **The call runs in the interpreter too**, and `total` reads `5` after it:
the machine run, through `compile_storage`. -/
theorem callTwice_interpreter :
    ∃ σ', Prog.run (State.fresh CallsExample 0) callTwice = .ok σ' ∧
      ∀ n, σ'.findLive "total" [] = .ok (.prim (.int n)) → n = 5 := by
  rcases compile_storage (P := callTwice) (Option.some_get callTwice_wt).symm (by decide) 0 with
    ⟨σ', m', h1, h2, h3⟩ | ⟨_, h2⟩
  · refine ⟨σ', h1, fun n hn => ?_⟩
    have hp : PathSlot CallsExample false "total" [] (.prim .uint) (.root 0) := PathSlot.root rfl
    have hs := h3 _ _ _ n hp hn
    have hm := callTwice_run
    rw [show run (compileProg callTwice) (Machine.init 0) = _ from h2] at hm
    simp only [storeAt, Option.some.injEq] at hm
    rw [show rootSlot CallsExample "total" = .root 0 from rfl] at hm
    omega
  · have := callTwice_run
    rw [show run (compileProg callTwice) (Machine.init 0) = _ from h2] at this
    cases this

/-! ## Signed arithmetic

An `int` is its two's complement word; solc's signed checks are compiled
(`sTail`, `negCode`), the comparisons are `SLT`/`SGT`, `/` and `%` are
`SDIV`/`SMOD`. -/

section Signed

local instance : InContract := ⟨TestSuite⟩

/-- `int x = -5; int y = 3; signedTotal = x * y + 2;` -/
def signed : Prog TestSuite := sol{ int x = -5; int y = 3; signedTotal = x * y + 2; }

theorem signed_wt : (wtProg (fun _ => none) signed).isSome := by decide

/-- `signedTotal` holds `-13`'s word, `2^256 - 13`. -/
theorem signed_run :
    storeAt (run (compileProg signed) (Machine.init 0)) (rootSlot TestSuite "signedTotal") =
      some (toWord (-13)) := by
  decide

/-- Truncating division and the dividend's sign for `%`: `-7 / 2` is `-3`,
`-7 % 2` is `-1`; `-x` negates. -/
theorem sdivmod_run :
    storeAt (run (compileProg sol{ int x = -7; signedTotal = x / 2; })
      (Machine.init 0)) (rootSlot TestSuite "signedTotal") = some (toWord (-3)) ∧
    storeAt (run (compileProg sol{ int x = -7; signedTotal = x % 2; })
      (Machine.init 0)) (rootSlot TestSuite "signedTotal") = some (toWord (-1)) ∧
    storeAt (run (compileProg sol{ signedTotal = -7; signedTotal = -signedTotal; })
      (Machine.init 0)) (rootSlot TestSuite "signedTotal") = some 7 := by
  decide

/-- The signed guards: `2^255 - 1 + 1` overflows, `-2^255 - 1` underflows,
`-2^255 / -1` and `-(-2^255)` overflow, `-2^255 * -1` overflows; `-1 < 0`. -/
theorem signedChecks_run :
    reverted (run (compileProg sol{
      signedTotal = 57896044618658097711785492504343953926634992332820282019728792003956564819967;
      signedTotal += 1; }) (Machine.init 0)) = true ∧
    reverted (run (compileProg sol{
      signedTotal = -57896044618658097711785492504343953926634992332820282019728792003956564819968;
      signedTotal -= 1; }) (Machine.init 0)) = true ∧
    reverted (run (compileProg sol{
      signedTotal = -57896044618658097711785492504343953926634992332820282019728792003956564819968;
      signedTotal /= -1; }) (Machine.init 0)) = true ∧
    reverted (run (compileProg sol{
      signedTotal = -57896044618658097711785492504343953926634992332820282019728792003956564819968;
      signedTotal = -signedTotal; }) (Machine.init 0)) = true ∧
    reverted (run (compileProg sol{
      signedTotal = -57896044618658097711785492504343953926634992332820282019728792003956564819968;
      signedTotal *= -1; }) (Machine.init 0)) = true ∧
    storeAt (run (compileProg sol{ int x = -1; if (x < 0) { total = 1; } else { total = 2; }; })
      (Machine.init 0)) (rootSlot TestSuite "total") = some 1 := by
  decide

/-- A copy of a struct holding a fixed-size array: `triple2 = triple;` copies
all four slots. -/
theorem copyFixed_run :
    storeAt (run (compileProg sol{ triple.items[1] = 4; triple.tag = 9; triple2 = triple; })
      (Machine.init 0)) ((rootSlot TestSuite "triple2").add 1) = some 4 ∧
    storeAt (run (compileProg sol{ triple.items[1] = 4; triple.tag = 9; triple2 = triple; })
      (Machine.init 0)) ((rootSlot TestSuite "triple2").add 3) = some 9 := by
  decide

end Signed

/-! ## Fixed-size arrays

solc lays a fixed-size array out inline, from its own slot, with no length
slot: `uint[3] fixedValues;` takes three slots, element `i` at its slot plus
`i`, and the bound is the constant `3` (`fixedCheck`, `fixedSlot`). -/

section Fixed

local instance : InContract := ⟨TestSuite⟩

/-- `uint[3]` takes three slots; `Token[2]` two; a `FixedTriple`
(`uint[3] items; uint tag;`) four, `tag` the fourth. -/
theorem fixed_layout :
    size (.ref (.fixed .uint 3)) = 3 ∧ size (.ref (.fixed (.ref (.struct "Token")) 2)) = 2 ∧
      size (.ref (.struct "FixedTriple")) = 4 ∧ offset "FixedTriple" "tag" = 3 := by
  decide

/-- `fixedValues[2] = 7;` -/
def fixedWrite : Prog TestSuite := sol{ fixedValues[2] = 7; }

/-- It is in the compiled fragment, so `compile_correct` covers it. -/
theorem fixedWrite_wt : (wtProg (fun _ => none) fixedWrite).isSome := by decide

/-- `fixedValues[2] = 7;` writes `7` to `fixedValues`'s slot plus `2`. -/
theorem fixedWrite_run :
    storeAt (run (compileProg fixedWrite) (Machine.init 0))
      ((rootSlot TestSuite "fixedValues").add 2) = some 7 := by
  decide

/-- `uint k = 3; fixedValues[k] = 1;` reverts at the bound: `k` is not below `3`. -/
theorem fixedOutOfBounds_run :
    reverted (run (compileProg (sol{ uint k = 3; fixedValues[k] = 1; } : Prog TestSuite))
      (Machine.init 0)) = true := by
  decide

end Fixed

/-! ## The interpreter, read off the machine -/

/-- **`alice.age = 10;` in the interpreter.**  From a fresh contract the
interpreter succeeds, and `alice.age` reads `10`: `compile_storage` ties the
interpreter's read to slot `13`, and the machine run holds `10` there. -/
theorem setAge_interpreter :
    ∃ σ', Prog.run (State.fresh StandardExample 0) setAge = .ok σ' ∧
      ∀ n, σ'.findLive "alice" [.field "age"] = .ok (.prim (.int n)) → n = 10 := by
  rcases compile_storage (P := setAge) (Γ' := fun _ => none) rfl (by decide) 0 with
    ⟨σ', m', h1, h2, h3⟩ | ⟨_, h2⟩
  · refine ⟨σ', h1, fun n hn => ?_⟩
    have hp : PathSlot StandardExample false "alice" [.field "age"] (.prim .uint) (.root 13) :=
      PathSlot.field (segs := []) (PathSlot.root (T := .ref (.struct "Person")) rfl) rfl
    have hs := h3 _ _ _ n hp hn
    have hm := setAge_run
    rw [show run (compileProg setAge) fresh = _ from h2] at hm
    simp only [storeAt, Option.some.injEq] at hm
    omega
  · have := setAge_run
    rw [show run (compileProg setAge) fresh = _ from h2] at this
    cases this

/-- **`total += 1;` at `2^256 - 1` reverts in the interpreter**, because it
reverts on the machine: `compile_correct` makes the two revert together. -/
theorem overflow_interpreter :
    Prog.run (State.fresh StandardExample 0) overflow = .error .revert := by
  rcases compile_correct (P := overflow) (Γ' := fun _ => none) rfl
      (Sim.init StandardExample 0) (by decide) with ⟨_, _, _, h, _⟩ | ⟨h, _⟩
  · have := reverted_eq overflow_run
    rw [show run (compileProg overflow) (Machine.init 0) = _ from h] at this
    cases this
  · exact h

end Examples
end Evm
end Solidity
