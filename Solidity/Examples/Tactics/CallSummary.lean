import Solidity.Tools.ProofTree
import Solidity.Tools.Taclet
import Solidity.Tools.Counterexample
import Solidity.Calculus.Closers

/-!
# A call by its callee's summary (`internalCallSummary`)

A call statement carries its callee's body, and inlining it at every call
(`internalCallExpand`) makes nested calls exponential: in the family
`f₀(x) = x + 1`, `fₖ(x) = fₖ₋₁(fₖ₋₁(x))`, the walk of `y = fₖ(a);` inlines
`2^k` bodies, `7·2^(k+1) − 3` nodes (`docs/automation.md`, M6).  A callee
whose body only computes values, and calls, has a *summary* instead: its
body run symbolically once, in its own frame, to the term its return
variable holds (`Prog.sym`, `Calculus/CallSummary.lean`), a call in it read
through its own callee's summary and literal offsets folded (`Tm.norm`).
The call is then one update, `{ y := a + 2^k }`, which fails exactly where
the call reverts (`Premise.sound_callSummary`, `Calculus/SoundSummary.lean`):
the walk has five nodes whatever `k`.  A callee that does not call is
inlined, which costs its body once either way, and so is one whose body
drops a value it may revert on (`g`: `uint t = x + 1;` never read).
-/

namespace Solidity.Examples.Tactics.CallSummary

/-- The family of the M6 table: `fₖ` adds `2^k`, by two calls of `fₖ₋₁`;
`g` computes a value it drops. -/
def Doubling : Contract := contract!{
  function f0(uint x) returns (uint r) { r = x + 1; }
  function f1(uint x) returns (uint r) { r = f0(f0(x)); }
  function f2(uint x) returns (uint r) { r = f1(f1(x)); }
  function f3(uint x) returns (uint r) { r = f2(f2(x)); }
  function f4(uint x) returns (uint r) { r = f3(f3(x)); }
  function f5(uint x) returns (uint r) { r = f4(f4(x)); }
  function f6(uint x) returns (uint r) { r = f5(f5(x)); }
  function g(uint x) returns (uint r) { uint t = x + 1; r = f0(x); }
}

local instance : InContract := ⟨Doubling⟩

open scoped Solidity.Scoped

/-! ## The rule -/

/--
info: Solidity.LeanTaclet.internalCallSummary : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {f : Name} {ps : Ctx}
  {args : Args C Γ ps} {rs Γ' : Ctx} {ret : CallRet Γ rs Γ'} {Γf : Ctx} {body : Prog C (rs ++ ps) Γf} {u : Upd C Γ Γ'},
  dl[LeanTaclet C k]{ ⟨[ ic; ]⟩ ⇝ { u } ⟨[ ]⟩ }
solkey: none (a rule solkey does not have)
printed: none (theory only Lean has)
sound: Solidity.LeanTaclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet internalCallSummary

/-! ## The walk: one node a call

The family's walk, for `k = 1` and `k = 6`: the call is one node, its update
`{ y := a + 2^k }` (the offsets folded), and the leaf closes. -/

/--
info: 0: allRight
1: impRight
2: valueDeclSkip
3: internalCallSummary
4: Closed goal
closed: 0 open goal(s), 5 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ a < 1000 → ⟨ uint y = f1(a); ⟩ y >= a }

/--
info: 0: allRight
1: impRight
2: valueDeclSkip
3: internalCallSummary
4: Closed goal
closed: 0 open goal(s), 5 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ a < 1000 → ⟨ uint y = f6(a); ⟩ y >= a }

/-! `g` drops `x + 1`, which may revert: it has no summary and is inlined,
and so is `f0`, which calls nobody. -/

/--
info: 0: allRight
1: impRight
2: valueDeclSkip
3: internalCallExpand
4: localValueDeclInitDrop
5: localValueAssign
6: valueDeclSkip
7: blockEmpty
8: localValueDeclInitDrop
9: additionAssignment
10: internalCallExpand
11: localValueDeclInitDrop
12: localValueAssign
13: valueDeclSkip
14: blockEmpty
15: additionAssignment
16: localValueAssign
17: localValueAssign
18: Closed goal
closed: 0 open goal(s), 19 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ a < 1000 → ⟨ uint y = g(a); ⟩ y >= a }

/-- The walk by hand: the call is `internalCallSummary`'s update. -/
theorem doublingTwoWalk : ⊨ᶠ dl!{ a < 1000 → [ uint y = f2(a); ] y == a + 4 } := by
  apply Proves.fmlValid
  apply impRight
  apply update .valueDeclSkip
  apply update .internalCallSummary
  sol_leaf
  sol_close

/-! ## The family, `k = 1 … 6`

`sol_prove` and the leaf replay `sol_prove?` writes; the walk is five nodes
for every `k`, the leaf `{ y := a + 2^k } y >= a`. -/

theorem doublingOne : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f1(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem doublingTwo : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f2(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem doublingThree : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f3(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem doublingFour : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f4(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem doublingFive : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f5(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem doublingSix : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f6(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

/-- The summary is exact: `f₆` adds `64`. -/
theorem doublingSixExact : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f6(a); ⟩ y == a + 64 } := by
  sol_prove

/-- Under the box an overflow reverts, so no precondition is needed: the
update fails where `a + 64` does not fit. -/
theorem doublingSixBox : ⊨ᶠ dl!{ [ uint y = f6(a); ] y == a + 64 } := by
  sol_prove

/-- Without the precondition the diamond is false: at `a = 2^256 − 1` the
summary `a + 64` does not return, so the call reverts (a counterexample). -/
theorem doublingSixUnbounded : ¬ (⊨ᶠ dl!{ ⟨ uint y = f6(a); ⟩ y >= a }) := by
  sol_refute

end Solidity.Examples.Tactics.CallSummary

/-! ## What a summary reads

A summary reads the value locals and the state's roots (`Tm.valOnly`
admits the storage, the environment and memory as terms): `k1` reads the
storage, `s1` the sender.  A body whose value may revert and is read only
lazily (`lazy1`: `t` under `&&`) still owes it at its end, so it has no
summary and is inlined (`internalCallExpand`). -/

namespace Solidity.Examples.Tactics.CallSummary.Reads

def Reads : Contract := contract!{
  uint total;
  function k0(uint x) returns (uint r) { r = x + 1; }
  function k1(uint x) returns (uint r) { r = k0(x) + total; }
  function s0() returns (address r) { r = msg.sender; }
  function s1() returns (address r) { r = s0(); }
  function lazy1(uint x) returns (bool r) { uint t = k0(x); r = x > 5 && t > 6; }
}

local instance : InContract := ⟨Reads⟩

open scoped Solidity.Scoped

/--
info: 0: allRight
1: valueDeclSkip
2: internalCallSummary
3: Closed goal
closed: 0 open goal(s), 4 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ [ uint y = k1(a); ] y == a + 1 + total }

/--
info: 0: valueDeclSkip
1: internalCallSummary
2: Closed goal
closed: 0 open goal(s), 3 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ [ address y = s1(); ] y == msg.sender }

theorem readsStorage : ⊨ᶠ dl!{ [ uint y = k1(a); ] y == a + 1 + total } := by
  sol_prove

theorem readsSender : ⊨ᶠ dl!{ [ address y = s1(); ] y == msg.sender } := by
  sol_prove

/--
info: 0: allRight
1: valueDeclSkip
2: internalCallExpand
3: localValueDeclInitDrop
4: localValueAssign
5: valueDeclSkip
6: blockEmpty
7: valueDeclSkip
8: internalCallExpand
9: localValueDeclInitDrop
10: localValueAssign
11: valueDeclSkip
12: blockEmpty
13: additionAssignment
14: localValueAssign
15: logicalAndCaptureLhs
16: localValueDeclInitDrop
17: greaterThanAssignment
18: logicalAndShortCircuitRhs
19: ifElseSplit
  [if se6 true]
    20: logicalAndAssignment
    21: logicalAndAssignment
    22: localValueAssign
    23: Closed goal
  [if se6 false]
    24: localValueAssign
    25: localValueAssign
    26: Closed goal
closed: 0 open goal(s), 27 node(s), 2 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ [ bool y = lazy1(a); ] y == y }

end Solidity.Examples.Tactics.CallSummary.Reads

namespace Solidity.Examples.Tactics.CallSummary.CheckedResult

/-- Multiplication summaries retain every checked intermediate result. -/
def Tripling : Contract := contract!{
  function f0(uint x) returns (uint r) { r = x * 3; }
  function f1(uint x) returns (uint r) { r = f0(f0(x)); }
  function f2(uint x) returns (uint r) { r = f1(f1(x)); }
  function f3(uint x) returns (uint r) { r = f2(f2(x)); }
  function s0(int x) returns (int r) { r = x * 3; }
  function s1(int x) returns (int r) { r = s0(s0(x)); }
}

local instance : InContract := ⟨Tripling⟩
open scoped Solidity.Scoped

/-- Eight checked products: `f3(a)` returns at least `a` below 1000. -/
theorem triplingThree : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f3(a); ⟩ y >= a } := by
  apply Proves.fmlValid
  apply allIntro
  apply impRight
  apply update .valueDeclSkip
  apply update .internalCallSummary
  sol_leaf
  sol_close

/--
info: 0: allRight
1: impRight
2: valueDeclSkip
3: internalCallSummary
4: Closed goal
closed: 0 open goal(s), 5 node(s), 1 branch(es)
-/
#guard_msgs in
#proof_tree dl!{ a < 1000 → ⟨ uint y = f3(a); ⟩ y >= a }

/-- Signed checked products grow a nonnegative symbolic input. -/
theorem signedTripling : ⊨ᶠ dl!{ ∀ int a; a >= 0 ∧ a < 1000 →
    ⟨ int y = s1(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

/-- An overflowing unsigned summary cannot return normally. -/
theorem unsignedOverflow : ⊨ᶠ dl!{
    a > 57896044618658097711785492504343953926634992332820282019728792003956564819968 →
    [ uint y = f1(a); ] false } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

/-- An overflowing signed summary cannot return normally. -/
theorem signedOverflow : ⊨ᶠ dl!{ ∀ int a;
    a > 28948022309329048855892746252171976963317496166410141009864396001978282409984 →
    [ int y = s1(a); ] false } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

/-- A constant summary still evaluates without symbolic range premises. -/
theorem constantTripling : ⊨ᶠ dl!{ ⟨ uint y = f1(2); ⟩ y == 18 } := by
  sol_prove (steps := 128)

/-- Signed summaries also return the expected negative result. -/
theorem signedNegative : ⊨ᶠ dl!{ ⟨ int y = s1(-2); ⟩ y + 18 == 0 } := by
  sol_prove (steps := 128)

/-- info: 'Solidity.Examples.Tactics.CallSummary.CheckedResult.triplingThree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms triplingThree

/-- info: 'Solidity.Examples.Tactics.CallSummary.CheckedResult.signedTripling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms signedTripling

end Solidity.Examples.Tactics.CallSummary.CheckedResult
