import Solidity.Tools.Run
import Solidity.Tools.Inspect
import Solidity.Tools.ProofTree
import Solidity.Calculus.Derive

/-!
# Loops

`while`, `for`, `do … while`, `break`, `continue` and a `return` inside a
loop (`docs/loops.md`).  The elaborator lowers them to `Stmt.loop`, solkey's
lowered `while`, by solkey's `LoopLowering` (`lowerLoops`): the flags `brk`,
`cnt`, `ret`, made only when used; the pins below are its shapes.  A loop
runs as the least fixed point of its unwinding (`Loop.run`), so `#run` runs
it and a concrete one is decided by `Prog.run_loop_of_iterN`.  The calculus
unwinds a loop to the bound its `/// @custom:key unwind k` clause gives
(`whileUnwind`, solkey's taclet with a bound) and leaves it there by
`loopExit`; a loop with an invariant is proved by it (`whileInvariantBox`,
`whileInvariantDiamond`, with a variant), past the anonymising update of the
locals its body writes (`{anon(…)}`).
-/

namespace Solidity.Examples.Loops

open Semantics Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## The lowering

A loop with no jump keeps its condition.  `continue` sets `cnt`, declared at
the head of each iteration; `break` sets `brk`, declared before the loop and
tested by its condition; the rest of a block after a statement that may set
a flag runs under `if (!flag…)`, and a `for`'s update under the flags that
end the loop, so that `continue` still runs it. -/

/-- info: uint i = 0;
while (i < 3) { i++; } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint i = 0; while (i < 3) { i++; } }))

/-- info: uint s = 0;
uint i = 0;
bool brk2 = false;
while (!brk2 && (i < 9)) { bool cnt1 = false; if (i == 1) { cnt1 = true; } else {  } if (!cnt1) { if (i == 5) { brk2 = true; } else {  } if (!brk2) { s += i; } else {  } } else {  } if (!brk2) { i++; } else {  } } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint s = 0;
  for (uint i = 0; i < 9; i++) { if (i == 1) { continue; } if (i == 5) { break; } s += i; } }))

/-! `do body while (c)` runs the body once before the condition, by a flag
`first`: the body is not copied. -/

/-- info: uint i = 5;
bool first1 = true;
while (first1 || (i < 3)) { first1 = false; i++; } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint i = 5; do { i++; } while (i < 3); }))

/-! A statement after a `break` in its block is dropped, as solkey drops it. -/

/-- info: uint i = 0;
bool brk1 = false;
while (!brk1 && (i < 3)) { i++; brk1 = true; } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint i = 0; while (i < 3) { i++; break; i++; } }))

/-! The specification above a loop is its annotation (`LoopAnn`): solkey's
`invariant` and `decreases` clauses, or Lean's bound on unwinding; a loop
with neither is unwound zero times. -/

/-- info: uint i = 0;
/// @custom:key invariant i <= 3 /// @custom:key decreases 3 - i while (i < 3) { i++; } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint i = 0;
  /// @custom:key invariant i <= 3
  /// @custom:key decreases 3 - i
  while (i < 3) { i++; } }))

/-- info: uint i = 0;
/// @custom:key unwind 4 while (i < 3) { i++; } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint i = 0;
  /// @custom:key unwind 4
  for (; i < 3; ) { i++; } }))

/-! ## `return` inside a loop

In a function's body, `return e;` inside a loop assigns the return variable
and sets `ret`, which nested loops share; the outermost loop is followed by
`if (ret) return;`, which `lowerReturns` lowers as any early `return`: the
statements after the loop move into its `else`. -/

def Loops : Contract := contract!{
  uint total; uint[] values;
  function sum(uint n) returns (uint s) {
    for (uint i = 1; i <= n; i++) { s += i; }
  }
  function firstOdd(uint n) returns (uint r) {
    uint i = 0;
    while (true) {
      i++;
      if (i % 2 == 0) { continue; }
      if (i > n) { break; }
      r = i;
    }
  }
  function atLeastOnce(uint n) returns (uint k) {
    do { k++; } while (k < n);
  }
  function fill(uint n) {
    uint i = 0;
    while (i < n) { values.push(i * i); i++; }
    total = values.length;
  }
  function find(uint x) returns (uint) {
    for (uint i = 0; i < values.length; i++) {
      if (values[i] == x) { return i; }
    }
    return 100;
  }
  function search(uint n, uint x) returns (uint) {
    fill(n);
    return find(x);
  }
  function pair(uint n, uint t) returns (uint) {
    for (uint i = 0; i < n; i++) {
      for (uint j = 0; j < n; j++) {
        if (i + j == t) { return 10 * i + j; }
      }
    }
    return 100;
  }
}

/-- info: uint y;
uint se1 = 3;
uint se2;
uint se3 = 0;
bool ret4 = false;
while (!ret4 && (se3 < values.length)) { if (values[se3] == se1) { se2 = se3; ret4 = true; } else {  } if (!ret4) { se3++; } else {  } }
if (ret4) {  } else { se2 = 100; }
y = se2; -/
#guard_msgs in
#eval IO.println (Prog.show (Prog.inlined (sol[Loops]{ uint y = find(3); })))

/-! Nested loops share `ret`: the inner loop's condition tests it, and so do
the outer loop's condition and the rest of its body. -/

/-- info: uint y;
uint se1 = 3;
uint se2 = 4;
uint se3;
uint se4 = 0;
bool ret6 = false;
while (!ret6 && (se4 < se1)) { uint se5 = 0; while (!ret6 && (se5 < se1)) { if ((se4 + se5) == se2) { se3 = (10 * se4) + se5; ret6 = true; } else {  } if (!ret6) { se5++; } else {  } } if (!ret6) { se4++; } else {  } }
if (ret6) {  } else { se3 = 100; }
y = se3; -/
#guard_msgs in
#eval IO.println (Prog.show (Prog.inlined (sol[Loops]{ uint y = pair(3, 4); })))

/-! ## Refused -/

/-- error: Solidity elaboration failed: `break` outside a loop -/
#guard_msgs in
example : Prog StandardExample := sol{ break; }

/-- error: Solidity elaboration failed: i++ < 3: a loop's condition needs a statement before it (an effect, a call, a cast, a narrow operation or a constructor), and is evaluated again each iteration -/
#guard_msgs in
example : Prog StandardExample := sol{ uint i = 0; while (i++ < 3) { } }

/-- error: Solidity elaboration failed: a loop has an `invariant` or an `unwind` clause, not both -/
#guard_msgs in
example : Prog StandardExample := sol{ uint i = 0;
  /// @custom:key invariant i <= 3
  /// @custom:key unwind 3
  while (i < 3) { i++; } }

/-- error: Solidity elaboration failed: `break`, `continue` or `return` inside `try` inside a loop -/
#guard_msgs in
example : Prog StandardExample := sol{ uint i = 0;
  while (i < 3) { try address(7).get() { break; } catch { } i++; } }

/-! A loop inside a `try` clause, outside every loop, is lowered: its
`break` sets its flag (solkey's `LoopLowering` leaves a `try` as it is,
`docs/solkey-feedback.md`). -/

/-- info: uint i = 0;
try address(7).get() { bool brk1 = false; while (!brk1 && (i < 3)) { if (i == 1) { brk1 = true; } else {  } if (!brk1) { i++; } else {  } } } catch Error(string memory) {  } catch Panic(uint) {  } catch {  } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint i = 0;
  try address(7).get() { while (i < 3) { if (i == 1) { break; } i++; } } catch { } }))

/-! ## Runs

`#run` runs a loop by iterating it (`Loop.runImpl`, which the kernel never
sees): `sum(4)` is `1 + 2 + 3 + 4`; `firstOdd(6)` the last odd number up to
`6`, skipping the even ones by `continue` and leaving by `break`; a
`do … while` runs its body once even when the condition is false at once;
`search` fills `values` with squares and finds `9` at index `3`, and
`pair(3, 4)` leaves both loops at `i = 2`, `j = 2`. -/

/--
info: ok
returns 10
total = 0
values = []
-/
#guard_msgs in #run Loops.sum(4)

/--
info: ok
returns 5
total = 0
values = []
-/
#guard_msgs in #run Loops.firstOdd(6)

/--
info: ok
returns 1
total = 0
values = []
-/
#guard_msgs in #run Loops.atLeastOnce(0)

/--
info: ok
returns 3
total = 4
values = [0, 1, 4, 9]
-/
#guard_msgs in #run Loops.search(4, 9)

/--
info: ok
returns 22
total = 0
values = []
-/
#guard_msgs in #run Loops.pair(3, 4)

/-! A modifier's `_;` in a loop runs the body once per iteration, and two
`_;` run it twice, in the same locals, its parameters and return variable
not reset, as solc's legacy pipeline runs it (via-IR resets them): `g()`
under `thrice` adds `2` three times, `f(0)` under `twice` returns `1`, the
second run reading the `a` the first bumped. -/

def ModifierRuns : Contract := contract!{ uint n;
  modifier twice() { _; _; }
  modifier thrice() { for (uint i = 0; i < 3; i++) { _; } }
  function f(uint a) twice returns (uint r) { r = a++; }
  function g() thrice { n += 2; } }

/--
info: ok
n = 6
-/
#guard_msgs in #run ModifierRuns.g()

/--
info: ok
returns 1
n = 0
-/
#guard_msgs in #run ModifierRuns.f(0)

/-- info: uint y; uint se1 = 0; uint se2; se2 = se1++; se2 = se1++; y = se2; -/
#guard_msgs in
#eval IO.println (Prog.toStr (Prog.inlined (sol[ModifierRuns]{ uint y = f(0); })))

/-! ## A loop decided

The kernel does not reduce `Loop.run` (it is classical), but a loop done at
its `n`-th iteration runs as that iteration, which it does compute:
`while (i < 3) { i++; }` from `i = 0` is done at the fourth (three bodies,
then the condition false). -/

def countTo3 : Prog StandardExample := sol{ uint i = 0; while (i < 3) { i++; } }

example : (Prog.run State.exampleStore countTo3 >>= fun σ => σ.getEnv (.user "i")) =
    .ok (.val (.int 3)) := by
  unfold countTo3
  rw [Prog.run_cons_ok rfl, Prog.run_loop_of_iterN (n := 4) rfl]
  rfl

/-! ## Unwinding

`whileUnwind` is solkey's taclet of that name with a bound: a loop that may
still be unwound `n + 1` times is one iteration, then the loop that may be
unwound `n` times.  At the bound `loopExit` leaves the loop, with KeY's two
goals of a check: the rest with the condition false assumed, and that it is
false, which fails where the loop runs longer than its bound.  A loop with no
clause is `unwind 0`. -/

/--
info: Solidity.LeanTaclet.whileUnwind : ∀ {C : Contract} {k : Nat} {m : Modality} {n : Nat} {body : List (Stmt C)}
  {cond : Val C PrimTy.bool},
  dl[LeanTaclet C k]{ ⟨[ /// @custom:key unwind n + 1 while (cond) body; ]⟩ ⇝
    ⟨[ if (cond) {body;/// @custom:key unwind n while (cond) body;}; ]⟩ }
solkey: whileUnwind (loop_expand), past the pin
printed: none (a solkey taclet not printed)
sound: Solidity.LeanTaclet.sound
-/
#guard_msgs in #taclet whileUnwind

/--
info: Solidity.LeanTaclet.loopExit : ∀ {C : Contract} {k : Nat} {m : Modality} {body : List (Stmt C)}
  {cond : Val C PrimTy.bool},
  dl[LeanTaclet C k]{ ⟨[ while (cond) body; ]⟩ ⇝
    "loop exited": cond = false ⟹ ⟨[ ]⟩ ; "unwound to the end": cond = false }
solkey: none (a rule solkey does not have)
printed: none (theory only Lean has)
sound: Solidity.LeanTaclet.sound
-/
#guard_msgs in #taclet loopExit

/-- `while (i < 3) { i++; }` from `i = 0`, unwound three times, ends at `3`,
under the diamond: the strategy fires `whileUnwind` three times, and
`loopExit` owes `i < 3` false. -/
theorem countTo3Diamond :
    ⊨ dl!{ ⟨ uint i = 0;
             /// @custom:key unwind 3
             while (i < 3) { i++; }; ⟩ i == 3 } := by
  sol_symex
  sol_close

/-- A loop with no clause is not unwound: it ends where its condition is
false on entry. -/
theorem notEntered : ⊨ dl!{ ⟨ uint i = 5; while (i < 3) { i++; }; ⟩ i == 5 } := by
  sol_symex
  sol_close

/-- The same proved by the walk `sol_derive?` writes: `whileUnwind` is
`unfoldLean`, `loopExit` is `checkLean` with its goals `thn` and `els`. -/
theorem countTo1Walk : ⊢ dl!{ ⟨ uint i = 0;
    /// @custom:key unwind 1
    while (i < 1) { i++; }; ⟩ i == 1 } := by
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfoldLean .whileUnwind
  apply unfold .ifElseUnfold
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply split .ifElseSplit
  case thn =>
    apply update .localIncrement
    apply checkLean .loopExit
    case thn =>
      apply emptyModality
      refine close ?_
      sol_symex
      sol_close
    case els =>
      refine close ?_
      sol_symex
      sol_close
  case els =>
    apply emptyModality
    refine close ?_
    sol_symex
    sol_close
  case cov =>
    refine close ?_
    sol_symex
    sol_close

/-! The proof tree labels `loopExit`'s goals. -/

/--
info: 0: localValueDeclInitDrop
1: localValueAssign
2: loopExit
  [loop exited]
    3: emptyModality
    4: Closed goal
  [unwound to the end]
    5: Closed goal
closed: 0 open goal(s), 6 node(s), 2 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ ⟨ uint i = 5; while (i < 3) { i++; }; ⟩ i == 5 }

/-! ## solkey's solc ports, as loops

solkey's `solc/SolcControlFlow.sol` unrolled its two loops by hand until it
had loop rules (`ed7849d5b6`, past the pinned checkout); the corpus
(`Corpus/SolcControlFlow.lean`) keeps the unrolled ports.  Here they are the
loops solkey now writes, each unwound as often as it runs. -/

section
local instance : InContract := ⟨SolcControlFlow⟩

/-- `doWhileFalseRunsBodyOnce` (solc `statements/do_while_loop_continue.sol`):
`do { … } while (false)` runs its body once, and the `continue` it skips
would have jumped to the false condition. -/
theorem doWhileFalseRunsBodyOnce :
    ⊨ dl!{ ⟨ uint i = 0; uint r = 0;
             /// @custom:key unwind 1
             do { if (i > 0) { continue; } i = i + 1; } while (false);
             r = 42; assert(i == 1); assert(r == 42); ⟩ true } := by
  sol_symex
  sol_close

/-- `forLoopOverArray` (solc `array/array_storage_index_zeroed_test.sol`),
solkey's `@custom:key box`: a loop over an array of length `3` writes
`i + 1` at each index. -/
theorem forLoopOverArray :
    ⊨ dl!{ [ require(values.length == 3); uint i;
             /// @custom:key unwind 3
             for (i = 0; i < values.length; i++) { values[i] = i + 1; };
             assert(i == 3); assert(values[0] == 1); assert(values[1] == 2);
             assert(values[2] == 3); ] true } := by
  sol_prove

end

/-! ## Invariants

solkey's `whileInvariantBox` and `whileInvariantDiamond` (`docs/loops.md`,
Decision 4): the invariant now, and, whatever the locals the body writes
hold (`{anon(body)}`, solkey's `#loopAnon`), from where it holds the
condition's value `b` picks the body, which keeps it, or the rest.  Under the
diamond the variant's value before the iteration is kept (`variant`) and
checked after it only where the condition holds again.  The fresh `b` and
`variant` print as `se` and `ie`, the fresh names they are. -/

/--
info: Solidity.LeanTaclet.whileInvariantBox : ∀ {C : Contract} {k : Nat} {body : Prog C} {dec : Option (Val C PrimTy.uint)}
  {cond inv : Val C PrimTy.bool},
  dl[LeanTaclet C k]{ [ /// @custom:key invariant inv while (cond) body; ] ⇝
    "invariant initially valid": inv = true ; "invariant preserved and used": { anon(body) } (inv = true →
      { se := cond } (se = true ⟹ ⟨[ body ]⟩ inv = true ; se = false ⟹ ⟨[ ]⟩)) }
solkey: whileInvariantBox (loop_inv), past the pin
printed: none (a solkey taclet not printed)
sound: Solidity.LeanTaclet.sound
-/
#guard_msgs in #taclet whileInvariantBox

/--
info: Solidity.LeanTaclet.whileInvariantDiamond : ∀ {C : Contract} {k : Nat} {body : Prog C} {cond inv : Val C PrimTy.bool}
  {dec : Val C PrimTy.uint},
  dl[LeanTaclet C k]{ ⟨ /// @custom:key invariant inv /// @custom:key decreases dec while (cond) body; ⟩ ⇝
    "invariant initially valid": inv = true ; "invariant preserved and used": { anon(body) } (inv = true →
      { ie := dec ‖ se := cond } (se = true ⟹ ⟨[ body ]⟩
      (inv = true ∧ { se := cond } (se = true → 0 <= dec ∧ dec < ie)) ; se = false ⟹ ⟨[ ]⟩)) }
solkey: whileInvariantDiamond (loop_inv), past the pin
printed: none (a solkey taclet not printed)
sound: Solidity.LeanTaclet.sound
-/
#guard_msgs in #taclet whileInvariantDiamond

/-- A counting loop: from `i = 0`, `i <= n` holds at every head, so the loop
ends at `n`.  The `require` keeps `n` a number: `⊨` reads every state, and a
local there may hold anything. -/
theorem countToN :
    ⊨ dl!{ [ require(n >= 0); uint i = 0;
             /// @custom:key invariant i <= n
             while (i < n) { i = i + 1; }; ] i == n } := by
  sol_symex
  sol_close

/-- The same under the diamond: `n - i` decreases while the loop goes on, so
it ends.  The invariant says `0 <= i`: the anonymised `i` is any number. -/
theorem countToNDiamond :
    ⊨ dl!{ n >= 0 && n <= 1000 → ⟨ uint i = 0;
             /// @custom:key invariant 0 <= i && i <= n
             /// @custom:key decreases n - i
             while (i < n) { i = i + 1; }; ⟩ i == n } := by
  sol_symex
  sol_close

/-- A sum with a closed form, solkey's `invariantClosedFormSum`: adding `2`
`n` times leaves `2 * n`. -/
theorem sumClosedForm :
    ⊨ dl!{ [ require(n >= 0); uint s = 0; uint i = 0;
             /// @custom:key invariant i <= n && s == 2 * i
             while (i < n) { s = s + 2; i = i + 1; }; ] s == n + n } := by
  sol_symex
  sol_close

/-! A loop with `break`: the invariant moves to the `while` the lowering
leaves, so it holds at the head of the iteration the `break` ends too.  Lean
adds that the flag the condition tests is a `bool` (`brk1 || !brk1`), which
KeY's types say: an anonymised local holds anything. -/

/-- info: uint i = 0;
bool brk1 = false;
/// @custom:key invariant (i <= 10) && (brk1 || !brk1) while (!brk1 && (i < 10)) { if (i == 5) { brk1 = true; } else {  } if (!brk1) { i++; } else {  } } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint i = 0;
  /// @custom:key invariant i <= 10
  while (i < 10) { if (i == 5) { break; } i++; } }))

/-- A loop left by `break` keeps its bound: `i <= 10` holds at every head,
the one after the `break` included. -/
theorem breakKeepsBound :
    ⊨ dl!{ [ uint i = 0;
             /// @custom:key invariant i <= 10
             while (i < 10) { if (i == n) { break; } i = i + 1; }; ] i <= 10 } := by
  sol_symex
  sol_close

/-- The counting loop by the walk `sol_derive?` writes
(`Examples/ProofTree.lean`): the invariant rule is `invBox`, `invLean` with
solkey's two goals under the box, `init` ("invariant initially valid") and,
past the anonymising update, `thn` and `els` ("invariant preserved and
used"); the third, `cov`, is `true`, which `closeTrue` proves. -/
theorem countToNWalk : ⊢ dl!{ [ require(n >= 0); uint i = 0;
    /// @custom:key invariant i <= n
    while (i < n) { i = i + 1; }; ] i == n } := by
  apply unfold .requireConditionCapture
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply splitBox .requireSimple
  case thn =>
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    apply invBox .whileInvariantBox
    case init =>
      refine close ?_
      sol_symex
      sol_close
    case thn =>
      apply update .binopAssignment
      apply emptyModality
      refine close ?_
      sol_symex
      sol_close
    case els =>
      apply emptyModality
      refine close ?_
      sol_symex
      sol_close
  case els =>
    apply done .revertBox
    refine close ?_
    sol_symex
    sol_close

/-! The proof tree labels the invariant rule's goals as solkey does. -/

/--
info: 0: requireConditionCapture
1: localValueDeclInitDrop
2: greaterEqualAssignment
3: requireSimple
  [Holds]
    4: localValueDeclInitDrop
    5: localValueAssign
    6: whileInvariantBox
      [invariant initially valid]
        7: Closed goal
      [invariant preserved and used]
        8: additionAssignment
        9: emptyModality
        10: Closed goal
      [invariant preserved and used]
        11: emptyModality
        12: Closed goal
  [Reverts]
    13: revertBox
    14: Closed goal
closed: 0 open goal(s), 15 node(s), 4 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ [ require(n >= 0); uint i = 0;
             /// @custom:key invariant i <= n
             while (i < n) { i = i + 1; }; ] i == n }

/-! A body with no frame has no invariant rule: one that writes memory, as in
solkey, and, Lean's own refusals (`Stmt.within`), one that pushes, pops,
rebinds an alias or calls out, which solkey frames as writing storage and
the ledger.  Such a loop closes to `false` (`whileClose`), as one under the
diamond with no variant does (`whileNoVariantDiamond`). -/

/--
info: Solidity.LeanTaclet.whileClose : ∀ {C : Contract} {k : Nat} {body : Prog C} {m : Modality} {inv : Val C PrimTy.bool}
  {dec : Option (Val C PrimTy.uint)} {cond : Val C PrimTy.bool},
  dl[LeanTaclet C k]{ ⟨[ /// @custom:key invariant inv while (cond) body; ]⟩ ⇝ false }
solkey: none (a rule solkey does not have)
printed: none (theory only Lean has)
sound: Solidity.LeanTaclet.sound
-/
#guard_msgs in #taclet whileClose

/--
info: Solidity.LeanTaclet.whileNoVariantDiamond : ∀ {C : Contract} {k : Nat} {body : Prog C} {inv cond : Val C PrimTy.bool}
  {dec : Option (Val C PrimTy.uint)}, dl[LeanTaclet C k]{ ⟨ /// @custom:key invariant inv while (cond) body; ⟩ ⇝ false }
solkey: none (a rule solkey does not have)
printed: none (theory only Lean has)
sound: Solidity.LeanTaclet.sound
-/
#guard_msgs in #taclet whileNoVariantDiamond

/-! `whileClose` fired: the body pushes, so the loop has no frame. -/

/--
info:   ~[whileClose]~>
    dl{ false }
-/
#guard_msgs in
#step dl!{ [ /// @custom:key invariant i <= 3
             while (i < 3) { values.push(i); i = i + 1; }; ] true }

/-! `whileNoVariantDiamond` fired: an invariant under the diamond, and no
`decreases`. -/

/--
info:   ~[whileNoVariantDiamond]~>
    dl{ false }
-/
#guard_msgs in
#step dl!{ ⟨ /// @custom:key invariant i <= 3
             while (i < 3) { i = i + 1; }; ⟩ true }

end Solidity.Examples.Loops
