import Solidity.Tools.Run
import Solidity.Tools.Inspect
import Solidity.Tools.ProofTree
import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Chains
import Solidity.Semantics.RunFuel
import Solidity.Syntax.Inlined

/-!
# Loops

`while`, `for`, `do … while`, `break`, `continue` and a `return` inside a
loop (`docs/loops.md`).  The elaborator lowers them to `Stmt.loop`, solkey's
lowered `while`, by solkey's `LoopLowering` (`lowerLoops`): the flags `brk`,
`cnt`, `ret`, made only when used; the pins below are its shapes.  A loop
runs as the least fixed point of its unwinding (`TLoop.run`), so `#run` runs
it and a concrete one is decided with fuel (`Prog.runF_approx`).  The calculus
unwinds an unannotated loop with `whileUnwind` within the proof search budget.
An explicit `/// @custom:key unwind k` clause limits unwinding and leaves it there by
`loopExit`; a loop with an invariant is proved by it (`whileInvariantBox`,
`whileInvariantDiamond`, with a variant), past the anonymising update of the
locals its body writes (`{anon(…)}`).
-/

namespace Solidity.Examples.Loops

open Semantics

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## The lowering

A loop with no jump keeps its condition.  `continue` sets `cnt`, declared at
the head of each iteration; `break` sets `brk`, declared before the loop and
tested by its condition; the rest of a block after a statement that may set
a flag runs under `if (!flag…)`, and a `for`'s update under the flags that
end the loop, so that `continue` still runs it. -/

/-- info: uint i = 0;
while (i < 3) { i++; } -/
#guard_msgs in
#eval IO.println (Prog.show [] (sol{ uint i = 0; while (i < 3) { i++; } }))

/-- info: uint s = 0;
uint i = 0;
bool brk2 = false;
while (!brk2 && (i < 9)) { bool cnt1 = false; if (i == 1) { cnt1 = true; } else { } if (!cnt1) { if (i == 5) { brk2 = true; } else { } if (!brk2) { s += i; } else { } } else { } if (!brk2) { i++; } else { } } -/
#guard_msgs in
#eval IO.println (Prog.show [] (sol{ uint s = 0;
  for (uint i = 0; i < 9; i++) { if (i == 1) { continue; } if (i == 5) { break; } s += i; } }))

/-! `do body while (c)` runs the body once before the condition, by a flag
`first`: the body is not copied. -/

/-- info: uint i = 5;
bool first1 = true;
while (first1 || (i < 3)) { first1 = false; i++; } -/
#guard_msgs in
#eval IO.println (Prog.show [] (sol{ uint i = 5; do { i++; } while (i < 3); }))

/-! A statement after a `break` in its block is dropped, as solkey drops it. -/

/-- info: uint i = 0;
bool brk1 = false;
while (!brk1 && (i < 3)) { i++; brk1 = true; } -/
#guard_msgs in
#eval IO.println (Prog.show [] (sol{ uint i = 0; while (i < 3) { i++; break; i++; } }))

/-! The specification above a loop is its annotation (`LoopAnn`): solkey's
`invariant` and `decreases` clauses, or Lean's bound on unwinding; a loop
with neither uses automatic unwinding within the proof search budget. -/

/-- info: uint i = 0;
/// @custom:key invariant i <= 3 /// @custom:key decreases 3 - i while (i < 3) { i++; } -/
#guard_msgs in
#eval IO.println (Prog.show [] (sol{ uint i = 0;
  /// @custom:key invariant i <= 3
  /// @custom:key decreases 3 - i
  while (i < 3) { i++; } }))

/-- info: uint i = 0;
/// @custom:key unwind 4 while (i < 3) { i++; } -/
#guard_msgs in
#eval IO.println (Prog.show [] (sol{ uint i = 0;
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
while (!ret4 && (se3 < values.length)) { if (values[se3] == se1) { se2 = se3; ret4 = true; } else { } if (!ret4) { se3++; } else { } }
if (ret4) { } else { se2 = 100; }
y = se2; -/
#guard_msgs in
#eval IO.println (Prog.inlinedShow [] (sol[Loops]{ uint y = find(3); }))

/-! Nested loops share `ret`: the inner loop's condition tests it, and so do
the outer loop's condition and the rest of its body. -/

/-- info: uint y;
uint se1 = 3;
uint se2 = 4;
uint se3;
uint se4 = 0;
bool ret6 = false;
while (!ret6 && (se4 < se1)) { uint se5 = 0; while (!ret6 && (se5 < se1)) { if ((se4 + se5) == se2) { se3 = (10 * se4) + se5; ret6 = true; } else { } if (!ret6) { se5++; } else { } } if (!ret6) { se4++; } else { } }
if (ret6) { } else { se3 = 100; }
y = se3; -/
#guard_msgs in
#eval IO.println (Prog.inlinedShow [] (sol[Loops]{ uint y = pair(3, 4); }))

/-! ## Refused -/

/-- error: Solidity elaboration failed: `break` outside a loop -/
#guard_msgs in
example : Prog StandardExample [] [] := sol{ break; }

/-- The final false condition still increments `i`. -/
def effectfulCondition := sol{ uint i = 0; while (i++ < 3) { } assert(i == 4); }
example : (Prog.run (State.ofStorage (Storage.init StandardExample))
    effectfulCondition).halt? = none := by
  rcases Prog.runF_approx 8 effectfulCondition (State.ofStorage (Storage.init StandardExample)) with h | h
  · exact absurd (congrArg TRes.halt? h) (by decide +kernel)
  · rw [Prog.run, ← h]
    decide +kernel

/-- error: Solidity elaboration failed: a loop has an `invariant` or an `unwind` clause, not both -/
#guard_msgs in
example : Prog StandardExample [] [.val .uint] := sol{ uint i = 0;
  /// @custom:key invariant i <= 3
  /// @custom:key unwind 3
  while (i < 3) { i++; } }

/-- error: Solidity elaboration failed: `break`, `continue` or `return` inside `try` inside a loop -/
#guard_msgs in
example : Prog StandardExample [] [.val .uint] := sol{ uint i = 0;
  while (i < 3) { try address(7).get() { break; } catch { } i++; } }

/-! A loop inside a `try` clause, outside every loop, is lowered: its
`break` sets its flag (solkey's `LoopLowering` leaves a `try` as it is,
`docs/solkey-feedback.md`). -/

/-- info: uint i = 0;
try address(7).get() { bool brk1 = false; while (!brk1 && (i < 3)) { if (i == 1) { brk1 = true; } else { } if (!brk1) { i++; } else { } } } catch Error(string memory) { } catch Panic(uint) { } catch { } -/
#guard_msgs in
#eval IO.println (Prog.show [] (sol{ uint i = 0;
  try address(7).get() { while (i < 3) { if (i == 1) { break; } i++; } } catch { } }))

/-! ## Runs

`#run` runs a loop by iterating it (`TLoop.runImpl`, which the kernel never
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
#eval IO.println (Prog.inlinedStr [] (sol[ModifierRuns]{ uint y = f(0); }))

/-! ## A loop decided

The kernel does not reduce `TLoop.run` (it is classical), but the run with
fuel (`Prog.runF`, each loop entered at most `n` iterations), which it
does compute, is the typed run wherever it does not run out
(`Prog.runF_approx`): `while (i < 3) { i++; }` from `i = 0` is done at
the fourth iteration (three bodies, then the condition false). -/

def countTo3Core : Prog StandardExample [] [.val .uint] := sol{ uint i = 0; while (i < 3) { i++; } }

/-- `i` is `3` where the loop ends, from the initial store. -/
theorem countTo3Run :
    ((Prog.run (State.ofStorage Storage.standardExample) countTo3Core).toOption.map
      fun o => (TEnv.get .here o.st.env : PrimTy.uint.Denote).1) = some 3 := by
  rcases Prog.runF_approx 4 countTo3Core (State.ofStorage Storage.standardExample)
    with h | h
  · exact absurd (congrArg TRes.halt? h) (by decide +kernel)
  · rw [Prog.run, ← h]
    decide +kernel

/-- A loop whose body declares a local, popped at the end of every iteration. -/
def countUpCore : Prog StandardExample [] [.val .uint] :=
  sol{ uint i = 0; while (i < 3) { uint j = i + 1; i = j; } assert(i == 3); }

/-- The body's `j` is gone at every head: `i` is `3` where the loop ends, and
the `assert` passes. -/
theorem countUpRun :
    ((Prog.run (State.ofStorage Storage.standardExample) countUpCore).toOption.map
      fun o => (TEnv.get .here o.st.env : PrimTy.uint.Denote).1) = some 3 := by
  rcases Prog.runF_approx 4 countUpCore (State.ofStorage Storage.standardExample)
    with h | h
  · exact absurd (congrArg TRes.halt? h) (by decide +kernel)
  · rw [Prog.run, ← h]
    decide +kernel

/-! ## Unwinding

`whileUnwind` follows solkey's literal one-iteration schema. An automatic
loop keeps its mode; an explicit bound decreases by one. At zero,
`loopExit` leaves the loop, with KeY's two
goals of a check: the rest with the condition false assumed, and that it is
false, which fails where the loop runs longer than its bound. -/

/--
info: Solidity.Taclet.whileUnwind : ∀ {C : Contract} {k : Nat} {Γ : Ctx} {m : Modality} {u : LoopUnwind} {x : Ctx}
  {body : Prog C Γ x} {cond : Val C Γ PrimTy.bool},
  dl{ ⟨[ while (cond) body; ]⟩ ⇝ ⟨[ if (cond) {body;while (cond) body;}; ]⟩ }
solkey: whileUnwind (loop_expand)
printed: none (a solkey taclet not printed)
sound: Solidity.Taclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet whileUnwind

/--
info: Solidity.LeanTaclet.loopExit : ∀ {C : Contract} {k : Nat} {Γ : Ctx} {m : Modality} {x : Ctx} {body : Prog C Γ x}
  {cond : Val C Γ PrimTy.bool},
  dl[LeanTaclet C k]{ ⟨[ /// @custom:key unwind 0 while (cond) body; ]⟩ ⇝
    "loop exited": { se := cond } se = false ⟹ ⟨[ ]⟩ ; "unwound to the end": { se := cond } se = false }
solkey: none (a rule solkey does not have)
printed: none (theory only Lean has)
sound: Solidity.LeanTaclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet loopExit

/-- A terminating automatic loop proves its result using upstream rules alone. -/
example : Proves StandardExample .solkey [] .nil
    dl!{ ⟨ uint i = 0; while (i < 3) { i++; }; ⟩ i == 3 } := by
  sol_prove (steps := 128)

-- An unfinished infinite loop cannot be mistaken for a completed walk.
#guard (Seq.residueWithin 32 .all .nil
  (dl!{ ⟨ while (true) { }; ⟩ true })).isNone

-- A completed loop with a false postcondition leaves an obligation.
#guard match Seq.residueWithin 128 .all .nil
    (dl!{ ⟨ uint i = 0; while (i < 3) { i++; }; ⟩ i == 4 }) with
  | some leaves => !leaves.isEmpty
  | none => false

/-- Automatic and explicit bounds must survive both source printers. -/
private def annotatedLoop (a : LoopAnn StandardExample []) : Prog StandardExample [] [] :=
  .cons (.loop a (.simple (.bool false)) .nil) .nil

private def automaticLoop := annotatedLoop .auto
private def zeroLoop := annotatedLoop (.unwind 0)
private def beforeBoundLoop := annotatedLoop (LoopUnwind.before (.bounded 0))
private def afterBoundLoop := annotatedLoop (LoopUnwind.after (.bounded 0))

/-- info: automatic and concrete loop bounds roundtrip through both source printers -/
#guard_msgs in
run_meta do
  for name in [``automaticLoop, ``zeroLoop, ``beforeBoundLoop, ``afterBoundLoop] do
    let info ← Lean.getConstInfo name
    let original := info.value!
    let some ss ← Delab.withPrinter original false (Delab.ppProgS [] original)
      | throwError "loop printer failed: {name}"
    let printed ← `(sol[StandardExample]{ $[$ss;]* })
    let parsed ← Lean.Elab.Term.TermElabM.run' do
      let p ← Lean.Elab.Term.elabTermEnsuringType printed info.type
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      pure p
    unless ← Lean.Meta.isDefEq original parsed do
      throwError "loop source roundtrip changed {name}: {printed}"
    let shownExpr ← Lean.Meta.mkAppM ``Prog.show #[Lean.toExpr ([] : List Var), original]
    let shown ← unsafe Lean.Meta.evalExpr String (Lean.mkConst ``String) shownExpr
    let .ok shownSyntax := Lean.Parser.runParserCategory (← Lean.getEnv) `term s!"sol[StandardExample]\{ {shown} }"
      | throwError "loop display does not parse: {shown}"
    let parsed ← Lean.Elab.Term.TermElabM.run' do
      let p ← Lean.Elab.Term.elabTermEnsuringType shownSyntax info.type
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      pure p
    unless ← Lean.Meta.isDefEq original parsed do
      throwError "loop display roundtrip changed {name}: {shown}"
  Lean.logInfo "automatic and concrete loop bounds roundtrip through both source printers"

/-- `while (i < 3) { i++; }` from `i = 0`, unwound three times, ends at `3`,
under the diamond: the strategy fires `whileUnwind` three times, and
`loopExit` owes `i < 3` false. -/
theorem countTo3Diamond :
    ⊨ᶠ dl!{ ⟨ uint i = 0;
             /// @custom:key unwind 3
             while (i < 3) { i++; }; ⟩ i == 3 } := by
  sol_symex
  sol_close

/-- A loop with an explicit zero bound is not unwound: it ends where its condition is
false on entry. -/
theorem notEntered : ⊨ᶠ dl!{ ⟨ uint i = 5;
    /// @custom:key unwind 0
    while (i < 3) { i++; }; ⟩ i == 5 } := by
  sol_symex
  sol_close


/-! ## Anonymous loop locals

An invariant anonymises the locals written by its body. Their dependent
function reads still have their intrinsic range; exposing witnesses also
makes repeated optional reads available to the arithmetic closer. -/

/-- A dependent anonymous unsigned read retains both of its bounds. -/
example (_σ : State StandardExample []) (f : (t : PrimTy) → t.Denote) :
    0 ≤ (f .uint).val ∧ (f .uint).val <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  sol_close_enrich
  all_goals first | trivial | omega

/-- A signed read retains its signed bounds, including negative values. -/
example (_σ : State StandardExample []) (f : (t : PrimTy) → t.Denote) :
    -57896044618658097711785492504343953926634992332820282019728792003956564819968 ≤
        (f .int).val ∧ (f .int).val <
      57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
  sol_close_enrich
  all_goals first | trivial | omega

/-- A nested invariant witness identifies a repeated optional length read. -/
example (_σ : State StandardExample []) (f : (t : PrimTy) → t.Denote)
    (len : Option PrimTy.uint.Denote)
    (h : ∃ v, len = some v ∧ (True ∧ v.val = (f .uint).val)) :
    ∃ v, len = some v ∧ 0 < v.val + 1 := by
  sol_close_enrich
  all_goals omega

/-- Enrichment closing the focused goal preserves the following goal. -/
example (_σ : State StandardExample []) (f : (t : PrimTy) → t.Denote) :
    (f .uint).val = (f .uint).val ∧ (False ∨ True) := by
  constructor
  sol_close_enrich
  exact Or.inr True.intro

/-- An ordinary KeY integer receives no unsigned range facts. -/
example (_σ : State StandardExample []) (x : Int) (h : x < 0) : x < 0 := by
  fail_if_success
    have : 0 ≤ x := by
      sol_close_enrich
      all_goals omega
  exact h

/-- Negative signed values are also left consistent with their type. -/
example (_σ : State StandardExample []) (x : PrimTy.int.Denote)
    (h : x.val < 0) : x.val < 0 := by
  fail_if_success
    have : 0 ≤ x.val := by
      sol_close_enrich
      all_goals omega
  exact h

/-! ## solkey's solc ports, as loops

solkey's `solc/SolcControlFlow.sol` unrolled its two loops by hand until it
had loop rules (`ed7849d5b6`, correspondence pending against the pinned checkout); the corpus
(`Corpus/SolcControlFlow.lean`) keeps the unrolled ports.  Here they are the
loops solkey now writes, each unwound as often as it runs. -/

section
local instance : InContract := ⟨SolcControlFlow⟩

open scoped Scoped

/-- `doWhileFalseRunsBodyOnce` (solc `statements/do_while_loop_continue.sol`):
`do { … } while (false)` runs its body once, and the `continue` it skips
would have jumped to the false condition. -/
theorem doWhileFalseRunsBodyOnce :
    ⊨ᶠ dl!{ ⟨ uint i = 0; uint r = 0;
             /// @custom:key unwind 1
             do { if (i > 0) { continue; } i = i + 1; } while (false);
             r = 42; assert(i == 1); assert(r == 42); ⟩ true } := by
  sol_symex
  sol_close

/-- `forLoopOverArray` (solc `array/array_storage_index_zeroed_test.sol`),
solkey's `@custom:key box`: a loop over an array of length `3` writes
`i + 1` at each index. -/
theorem forLoopOverArray :
    ⊨ᶠ dl!{ [ require(values.length == 3); uint i;
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
info: Solidity.Taclet.whileInvariantBox : ∀ {C : Contract} {k : Nat} {Γ x : Ctx} {body : Prog C Γ x}
  {xs : List ((t : LTy) × Idx Γ t)} {hv : Option (List Name)} {dec : Option (Val C Γ PrimTy.uint)} {brk : Bool}
  {qs : List (LoopQ C Γ)} {cond inv : Val C Γ PrimTy.bool},
  dl{ [ /// @custom:key invariant inv while (cond) body; ] ⇝
    "invariant initially valid": inv = true ∧ ¬broke ; "invariant preserved and used": { anon(body) } (inv = true ∧
      ¬broke → { se := cond } (se = true ⟹ ⟨[ body ]⟩ (¬broke → inv = true) ∧ (broke → ⟨[ ]⟩) ; se = false ⟹ ⟨[ ]⟩)) }
solkey: whileInvariantBox (loop_inv)
printed: none (a solkey taclet not printed)
sound: Solidity.Taclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet whileInvariantBox

/--
info: Solidity.Taclet.whileInvariantDiamond : ∀ {C : Contract} {k : Nat} {Γ x : Ctx} {body : Prog C Γ x}
  {xs : List ((t : LTy) × Idx Γ t)} {hv : Option (List Name)} {qs : List (LoopQ C Γ)} {brk : Bool}
  {cond inv : Val C Γ PrimTy.bool} {dec : Val C Γ PrimTy.uint},
  dl{ ⟨ /// @custom:key invariant inv /// @custom:key decreases dec while (cond) body; ⟩ ⇝
    "invariant initially valid": inv = true ; "invariant preserved and used": { anon(body) } (inv = true →
      { ie := dec ‖ se := cond } (se = true ⟹ ⟨[ body ]⟩
      (inv = true ∧ { se := cond } (se = true → 0 <= dec ∧ dec < ie)) ; se = false ⟹ ⟨[ ]⟩)) }
solkey: whileInvariantDiamond (loop_inv)
printed: none (a solkey taclet not printed)
sound: Solidity.Taclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet whileInvariantDiamond

/-- A counting loop: from `i = 0`, `i <= n` holds at every head, so the loop
ends at `n`.  The `require` states `n >= 0`, which the leaf's closer
reads as a fact. -/
theorem countToN :
    ⊨ᶠ dl!{ [ require(n >= 0); uint i = 0;
             /// @custom:key invariant i <= n
             while (i < n) { i = i + 1; }; ] i == n } := by
  sol_symex
  sol_close

/-- A sum with a closed form, solkey's `invariantClosedFormSum`: adding `2`
`n` times leaves `2 * n`. -/
theorem sumClosedForm :
    ⊨ᶠ dl!{ [ require(n >= 0); uint s = 0; uint i = 0;
             /// @custom:key invariant i <= n && s == 2 * i
             while (i < n) { s = s + 2; i = i + 1; }; ] s == n + n } := by
  sol_symex
  sol_close

/-- `countToN` under the diamond: `n - i` decreases while the loop goes on, so
it ends.  The invariant says `0 <= i`: the anonymised `i` is any number. -/
theorem countToNDiamond :
    ⊨ᶠ dl!{ n >= 0 && n <= 1000 → ⟨ uint i = 0;
             /// @custom:key invariant 0 <= i && i <= n
             /// @custom:key decreases n - i
             while (i < n) { i = i + 1; }; ⟩ i == n } := by
  sol_symex
  sol_close

/-- A loop left by `break` keeps its bound: `i <= 10` holds at every head,
the one after the `break` included. -/
theorem breakKeepsBound :
    ⊨ᶠ dl!{ [ uint i = 0;
             /// @custom:key invariant i <= 10
             while (i < 10) { if (i == n) { break; } i = i + 1; }; ] i <= 10 } := by
  sol_symex
  sol_close

/-! ### Modifies sets

A body that writes the storage anonymises only the roots it may write, its
modifies set (`Prog.storeAt`, KeY's `assignable`): the premise's storage is
`anon(storage, b, anonStorage)` (KeY's `anon(heap, locset, anonHeap)`),
every other root as it was before the loop (`Stmt.run_keeps`, the frame
theorem).  So the invariant need not restate what the body leaves: here it
says nothing of `a`, which the postcondition reads. -/

/-- Two counters, the loop below bumping one. -/
def TwoCounters : Contract := contract!{ uint a; uint b; }

section Frames

local instance : InContract := ⟨TwoCounters⟩

/-- The loop's modifies set is `b`, the root its body writes. -/
example : (sol{ uint i = 0; while (i < 3) { b = b + 1; i = i + 1; } } :
    Prog TwoCounters [] [.val .uint]).storeAt = some ["b"] := by decide

/-- **A root the body does not write keeps its value past the loop**: the
invariant says nothing of `a`, the frame does. -/
theorem untouchedRoot :
    ⊨ᶠ dl!{ [ uint a0 = a; uint i = 0;
             /// @custom:key invariant i <= n
             while (i < n) { b = b + 1; i = i + 1; }; ] a == a0 } := by
  sol_symex
  sol_close

end Frames

/-- A quantified clause, solkey's specification language above a loop
(`\forall uint q; a -> c`, `LoopQ`): every number below `i` is below `n` at
every head. -/
theorem countWithPrefix :
    ⊨ᶠ dl!{ [ require(n >= 0); uint i = 0;
             /// @custom:key invariant i <= n
             /// @custom:key invariant \forall uint q; q < i -> q < n
             while (i < n) { i = i + 1; }; ] i == n } := by
  sol_symex
  sol_close

/-- info: uint i = 0;
/// @custom:key invariant i <= 3 /// @custom:key invariant \forall uint q; q < i -> q < 3 while (i < 3) { i++; } -/
#guard_msgs in
#eval IO.println (Prog.show [] (sol{ uint i = 0;
  /// @custom:key invariant i <= 3
  /// @custom:key invariant \forall uint q; q < i -> q < 3
  while (i < 3) { i++; } }))

/-! Renaming a callee's locals stops at a quantifier's own binder
(`RawInv.rename`): the inlined parameter `q` becomes `se1` outside the
`∀`, the bound `q` stays below it. -/

/-- info: Solidity.RawInv.imp (Solidity.RawExpr.name "se1") (Solidity.RawExpr.name "i") -/
#guard_msgs in
#eval RawInv.rename [("q", "se1")] (.imp (.name "q") (.name "i"))

/--
info: Solidity.RawInv.all
  (Solidity.PrimTy.uint)
  "q"
  (Solidity.RawInv.imp (Solidity.RawExpr.name "q") (Solidity.RawExpr.name "i"))
-/
#guard_msgs in
#eval RawInv.rename [("q", "se1")] (.all .uint "q" (.imp (.name "q") (.name "i")))

/-! A loop with `break`: the invariant moves to the `while` the lowering
leaves, so it holds at the head of the iteration the `break` ends too.  Lean
adds that the flag the condition tests is a `bool` (`brk1 || !brk1`), which
KeY's types say: an anonymised local holds anything. -/

/-- info: uint i = 0;
bool brk1 = false;
/// @custom:key invariant (i <= 10) && (brk1 || !brk1) while (!brk1 && (i < 10)) { if (i == 5) { brk1 = true; } else { } if (!brk1) { i++; } else { } } -/
#guard_msgs in
#eval IO.println (Prog.show [] (sol{ uint i = 0;
  /// @custom:key invariant i <= 10
  while (i < 10) { if (i == 5) { break; } i++; } }))

/-- The counting loop by the walk `sol_derive?` writes
(`Examples/ProofTree.lean`): the invariant rule is `invBox`, `invLean` with
solkey's two goals under the box, `init` ("invariant initially valid") and,
past the anonymising update, `thn` and `els` ("invariant preserved and
used"). -/
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
      sol_leaf
      sol_close
    case thn =>
      apply update .binopAssignment
      apply emptyModality
      sol_leaf
      sol_close
    case els =>
      apply emptyModality
      sol_leaf
      sol_close
  case els =>
    apply done .revertBox
    sol_leaf
    sol_close

/-! The proof tree labels the invariant rule's goals as solkey does. -/

/--
info: 0: allRight
1: requireConditionCapture
2: localValueDeclInitDrop
3: greaterEqualAssignment
4: requireSimple
  [Holds]
    5: localValueDeclInitDrop
    6: localValueAssign
    7: whileInvariantBox
      [invariant initially valid]
        8: Closed goal
      [invariant preserved and used]
        9: additionAssignment
        10: Closed goal
      [invariant preserved and used]
        11: Closed goal
  [Reverts]
    12: revertBox
    13: Closed goal
closed: 0 open goal(s), 14 node(s), 4 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ [ require(n >= 0); uint i = 0;
             /// @custom:key invariant i <= n
             while (i < n) { i = i + 1; }; ] i == n }

/-- The same proved by the walk `sol_derive?` writes: `whileUnwind` is
`unfold`, `loopExit` is `checkLean` with its goals `thn` and `els`; the
branch the unwinding leaves is a block (`blockEmpty`). -/
theorem countTo1Walk : ⊢ dl!{ ⟨ uint i = 0;
    /// @custom:key unwind 1
    while (i < 1) { i++; }; ⟩ i == 1 } := by
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply unfold .whileUnwind
  apply unfold .ifElseUnfold
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply split .ifElseSplit
  case thn =>
    apply unfold .blockEmpty
    apply update .localIncrement
    apply checkLean .loopExit
    case thn =>
      sol_leaf
      sol_close
    case els =>
      sol_leaf
      sol_close
  case els =>
    sol_leaf
    sol_close

/-! The proof tree labels `loopExit`'s goals. -/

/--
info: 0: localValueDeclInitDrop
1: localValueAssign
2: loopExit
  [loop exited]
    3: Closed goal
  [unwound to the end]
    4: updIntro
    5: Closed goal
closed: 0 open goal(s), 6 node(s), 2 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ ⟨ uint i = 5;
    /// @custom:key unwind 0
    while (i < 3) { i++; }; ⟩ i == 5 }

/-! A body with no frame has no invariant rule: one that writes memory, as in
solkey, and, Lean's own refusals (`Stmt.within`), one that pushes, pops,
rebinds an alias or calls out, which solkey frames as writing storage and
the ledger.  Such a loop closes to `false` (`whileClose`), as one under the
diamond with no variant does (`whileNoVariantDiamond`). -/

/--
info: Solidity.LeanTaclet.whileClose : ∀ {C : Contract} {k : Nat} {Γ x : Ctx} {body : Prog C Γ x} {m : Modality}
  {inv : Val C Γ PrimTy.bool} {dec : Option (Val C Γ PrimTy.uint)} {brk : Bool} {qs : List (LoopQ C Γ)}
  {cond : Val C Γ PrimTy.bool}, dl[LeanTaclet C k]{ ⟨[ /// @custom:key invariant inv while (cond) body; ]⟩ ⇝ false }
solkey: none (a rule solkey does not have)
printed: none (theory only Lean has)
sound: Solidity.LeanTaclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet whileClose

/--
info: Solidity.LeanTaclet.whileNoVariantDiamond : ∀ {C : Contract} {k : Nat} {Γ x : Ctx} {body : Prog C Γ x}
  {inv : Val C Γ PrimTy.bool} {brk : Bool} {qs : List (LoopQ C Γ)} {cond : Val C Γ PrimTy.bool}
  {dec : Option (Val C Γ PrimTy.uint)},
  dl[LeanTaclet C k]{ ⟨ /// @custom:key invariant inv while (cond) body; ⟩ ⇝ false }
solkey: none (a rule solkey does not have)
printed: none (theory only Lean has)
sound: Solidity.LeanTaclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet whileNoVariantDiamond

/-! `whileClose` fired: the body pushes, so the loop has no frame. -/

/--
info:   ~[whileClose]~>
    dl{ ∀ uint i; false }
-/
#guard_msgs in
#step dl!{ [ /// @custom:key invariant i <= 3
             while (i < 3) { values.push(i); i = i + 1; }; ] true }

/-! `whileNoVariantDiamond` fired: an invariant under the diamond, and no
`decreases`. -/

/--
info:   ~[whileNoVariantDiamond]~>
    dl{ ∀ uint i; false }
-/
#guard_msgs in
#step dl!{ ⟨ /// @custom:key invariant i <= 3
             while (i < 3) { i = i + 1; }; ⟩ true }

end Solidity.Examples.Loops
