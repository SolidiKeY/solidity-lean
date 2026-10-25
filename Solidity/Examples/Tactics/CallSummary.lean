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
  function f7(uint x) returns (uint r) { r = f6(f6(x)); }
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

/-! ## The family, `k = 1 … 7`

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

theorem doublingSeven : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f7(a); ⟩ y >= a } := by
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

/-- The family of the M6 table with products: `fₖ` multiplies by `3^(2^k)`,
by two calls of `fₖ₋₁`.  Its summary folds the literal factors
(`Op2.mk2`, `(u * c₁) * c₂ ⇝ u * (c₁ * c₂)`, which overflows where the
other does): `fₖ`'s is `x * 3^(2^k)`, one checked product. -/
def Tripling : Contract := contract!{
  function f0(uint x) returns (uint r) { r = x * 3; }
  function f1(uint x) returns (uint r) { r = f0(f0(x)); }
  function f2(uint x) returns (uint r) { r = f1(f1(x)); }
  function f3(uint x) returns (uint r) { r = f2(f2(x)); }
  function f4(uint x) returns (uint r) { r = f3(f3(x)); }
  function f5(uint x) returns (uint r) { r = f4(f4(x)); }
  function f6(uint x) returns (uint r) { r = f5(f5(x)); }
  function f7(uint x) returns (uint r) { r = f6(f6(x)); }
  function s0(int x) returns (int r) { r = x * 3; }
  function s1(int x) returns (int r) { r = s0(s0(x)); }
}

local instance : InContract := ⟨Tripling⟩
open scoped Solidity.Scoped

/-- `f3(a) = a * 6561` returns at least `a` below 1000. -/
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

/-! ### The family, `k = 1 … 7`

The leaf is `{ y := a * 3^(2^k) } y >= a`, one product (`3^128` at `k =
7`, below `2^256 / 1000`); the walk is five nodes, and the program a term
the size of the source: every call of `fₖ₋₁` holds its one body
(`CallMemo`, `docs/automation.md`, M6). -/

theorem triplingOne : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f1(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem triplingTwo : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f2(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem triplingThreeAuto : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f3(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem triplingFour : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f4(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem triplingFive : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f5(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem triplingSix : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f6(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem triplingSeven : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f7(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

/-- The summary is exact: `f₇` multiplies by `3^128`. -/
theorem triplingSevenExact : ⊨ᶠ dl!{
    ⟨ uint y = f7(1); ⟩ y == 11790184577738583171520872861412518665678211592275841109096961 } := by
  sol_prove (steps := 128)

/-- Under the box an overflow reverts, so no precondition is needed. -/
theorem triplingFourBox : ⊨ᶠ dl!{ [ uint y = f4(a); ] y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

/-- A false leaf (at `a = 0` the product is `0`): the closer fails.  (The
hypothesis only closes the example once the closer has failed.) -/
example (h : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f4(a); ⟩ y >= a + 1 }) :
    ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f4(a); ⟩ y >= a + 1 } := by
  fail_if_success
    sol_prove (steps := 128)
    sol_leaf
    sol_close
  exact h

/-- The same formula, refuted (`a = 0`). -/
theorem triplingFourOff : ¬ (⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f4(a); ⟩ y >= a + 1 }) := by
  sol_refute

/-- `a * 3^32` overflows past `10^62`: the closer fails, within the
declaration's heartbeats. -/
example (h : ⊨ᶠ dl!{ a < 100000000000000000000000000000000000000000000000000000000000000 →
    ⟨ uint y = f5(a); ⟩ y >= a }) :
    ⊨ᶠ dl!{ a < 100000000000000000000000000000000000000000000000000000000000000 →
      ⟨ uint y = f5(a); ⟩ y >= a } := by
  fail_if_success
    sol_prove (steps := 128)
    sol_leaf
    sol_close
  exact h

/-- The leaf evaluated whole (`sol_close`'s last alternative), its
summary `a * 3^16` (sixteen products before the literal factors were
folded: it ran past 45 s inside `simp` before `Close.forall_const_type`,
`docs/automation.md`, M6; `Affine.affineThreeWhole` keeps that shape). -/
theorem triplingFourWhole : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f4(a); ⟩ y >= a } := by
  apply Proves.fmlValid
  apply allIntro
  apply impRight
  apply update .valueDeclSkip
  apply update .internalCallSummary
  sol_leaf
  sol_close_unwrap
  intro σ
  sol_close_eval
  all_goals sol_close_saturate
  all_goals (try sol_close_landed)
  all_goals try (intros; sol_close_reads_all)
  all_goals try (subst_vars; sol_close_reads_all)
  all_goals (try intros)
  all_goals (try simp only [Close.exists_unit, Close.forall_unit, Close.exists_const_type,
    Close.forall_const_type] at *)
  all_goals (try sol_close_witness)
  all_goals (repeat' (first | intro _ | apply And.intro))
  all_goals sol_close_finish

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

/-- info: 'Solidity.Examples.Tactics.CallSummary.CheckedResult.triplingFive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms triplingFive

end Solidity.Examples.Tactics.CallSummary.CheckedResult

/-! ## Summaries the literals do not fold: one call site at a time

`fₖ(x) = fₖ₋₁(fₖ₋₁(x))` over `f₀(x) = x * 3 + 1`: no literal factor or
summand meets another (`(u * 3 + 1) * 3`), so `fₖ`'s summary has `2^(k+1)`
operations.  From four on (`CloseJ.shareMin`), `sol_close` reads the leaf one
call site at a time (`holds_upd_share`, `Calculus/LeafShare.lean`):
`{ sh0 := a * 3 } { sh1 := sh0 + 1 } … { y := … ‖ pop }`, each update
evaluated with the rest held opaque and each check refuted in a context of
its own (`CloseJ.peel`). -/

namespace Solidity.Examples.Tactics.CallSummary.Affine

def Affine : Contract := contract!{
  function f0(uint x) returns (uint r) { r = x * 3 + 1; }
  function f1(uint x) returns (uint r) { r = f0(f0(x)); }
  function f2(uint x) returns (uint r) { r = f1(f1(x)); }
  function f3(uint x) returns (uint r) { r = f2(f2(x)); }
}

local instance : InContract := ⟨Affine⟩
open scoped Solidity.Scoped

theorem affineTwo : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f2(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

theorem affineThree : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f3(a); ⟩ y >= a } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close

/-- Sixteen operations evaluated whole (`sol_close`'s last alternative,
which `CloseJ.shareWholeMax` skips at this size): within the default
heartbeats (`docs/automation.md`, M6, "The runaway"). -/
theorem affineThreeWhole : ⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f3(a); ⟩ y >= a } := by
  apply Proves.fmlValid
  apply allIntro
  apply impRight
  apply update .valueDeclSkip
  apply update .internalCallSummary
  sol_leaf
  sol_close_unwrap
  intro σ
  sol_close_eval
  all_goals sol_close_saturate
  all_goals (try sol_close_landed)
  all_goals try (intros; sol_close_reads_all)
  all_goals try (subst_vars; sol_close_reads_all)
  all_goals (try intros)
  all_goals (try simp only [Close.exists_unit, Close.forall_unit, Close.exists_const_type,
    Close.forall_const_type] at *)
  all_goals (try sol_close_witness)
  all_goals (repeat' (first | intro _ | apply And.intro))
  all_goals sol_close_finish

end Solidity.Examples.Tactics.CallSummary.Affine

/-! A callee's locals numbered past a fresh name the formula writes: the retry
of `elabModalProg` (`Calculus/Notation.lean`) rolls back the callees' first
numbering (`CallMemo`) with the counter, so the shared callee's `a` and `r`
take `se3` and `se4`, not the formula's `se2`. -/
namespace Solidity.Examples.Tactics.CallSummary.Retry

def Incr : Contract := contract!{
  function h(uint a) returns (uint r) { r = a + 1; }
}
local instance : InContract := ⟨Incr⟩
open scoped Solidity.Scoped

/--
info: node: 5
sequent:
  dl{ { se2 := 5 }, { y := defVal(T) }, { se3 := 1 } ⟹ ⟨ uint se4; se4 = se3 + 1; y = se4; ⟩ y = 2 }
rule: valueDeclSkip
state: inner
branch: -
parent: 4
children: [6]
tactics: apply Proves.update (Taclet.toStep .valueDeclSkip)
-/
#guard_msgs in
#proof_node 5 dl!{ { se2 := 5 } ⟨ uint y = h(1); ⟩ y == 2 }

end Solidity.Examples.Tactics.CallSummary.Retry
