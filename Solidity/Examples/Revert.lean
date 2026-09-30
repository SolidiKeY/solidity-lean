import Solidity.Calculus.Close
import Solidity.Calculus.Chains

/-!
# The two modalities: `revert();`, `require`, `assert`

`⟨ P ⟩ φ` (the diamond) says that `P` runs to the end and `φ` holds after;
`[ P ] φ` (the box) says only that *if* `P` runs to the end, `φ` holds after.
Without reverts the two agree.  `revert();` aborts the transaction, and so
does a `require(c);` or an `assert(c);` whose condition is false, and a
`transfer` the contract cannot fund: a reverted run satisfies every box
formula and no diamond formula (`Modality.onHalt`).

Every other rule is written for both modalities at once,
`⟨[ s; ]⟩` (solkey's `#mod`).  The two rules for `revert();` are the only
ones that tell them apart.  solkey's taclets (`solidityProgramRules.key`):

```
revertDiamond {
     \schemaVar \formula post;
     \find(\modality{#diamond}{c# revert(); #c}\endmodality(post))
     \replacewith(false)
     \heuristics(simplify_prog)
};

revertBox {
     \schemaVar \formula post;
     \find(\modality{#box}{c# revert(); #c}\endmodality(post))
     \replacewith(true)
     \heuristics(simplify_prog)
};

requireSimple {
    \schemaVar \formula post;
    \schemaVar \program SimpleExpression[primitive] se;

    \find(\modality{#mod}{c# require(s#se); #c}\endmodality(post))
    "Holds":
        \replacewith(se = FALSE | \modality{#mod}{c# #c}\endmodality(post));
    "Reverts":
        \replacewith(se = TRUE | \modality{#mod}{c# revert(); #c}\endmodality(post))
    \heuristics(simplify_prog)
};
```

A revert drops the rest of the program (`#c`) and the postcondition: the box
closes to `true`, the diamond to `false`.  `require` splits as `ifElseSplit`
does (`Branch.lean`), a non-simple condition captured first
(`requireConditionCapture`): the first goal goes on with the rest of the
program, the second reverts.  Under `⊢` the revert rules are
`apply done .revertBox` and `apply done .revertDiamond` (`Proves.done`).
A `transfer` the contract cannot fund reverts too, through the guard of
`transferNoCallback`: `Payment.lean`.
-/

namespace Solidity.Examples.Revert

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## The taclets -/

/-- info: @Taclet.revertBox : ∀ {C : Contract} {k : Nat}, dl{ [ revert(); ] ⇝ true } -/
#guard_msgs in #check @Taclet.revertBox

/-- info: @Taclet.revertDiamond : ∀ {C : Contract} {k : Nat}, dl{ ⟨ revert(); ⟩ ⇝ false } -/
#guard_msgs in #check @Taclet.revertDiamond

/--
info: @Taclet.requireSimple : ∀ {C : Contract} {k : Nat} {m : Modality} {se : Simple C PrimTy.bool},
  dl{ ⟨[ require(se); ]⟩ ⇝ se ≐ true ⟹ ⟨[ ]⟩ ; se ≐ false ⟹ ⟨[ revert(); ]⟩ }
-/
#guard_msgs in #check @Taclet.requireSimple

/--
info: @Taclet.requireConditionCapture : ∀ {C : Contract} {k : Nat} {m : Modality} {nse : Val C PrimTy.bool},
  dl{ ⟨[ require(nse); ]⟩ ⇝ ⟨[ bool se = nse; require(se); ]⟩ }
-/
#guard_msgs in #check @Taclet.requireConditionCapture

/-! ## The box: a guard that fails proves anything

`require(a == b); x = a;` ends with `x == b` whenever it ends: if `a != b`
it reverts, and the box asks nothing of a reverted run. -/

/-- `[ require(a == b); x = a; ] x == b`. -/
theorem requireBox : ⊢ dl!{ [ require(a == b); x = a; ] x == b } := by
  apply unfold .requireConditionCapture
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  -- dl{ { se1 := a == b } ⟹ [ require(se1); x = a; ] x = b }
  apply split .requireSimple
  case thn =>
    -- dl{ { se1 := a == b }, se1 ≐ true ⟹ [ x = a; ] x = b }
    apply update .localValueAssign
    apply empty
    refine close ?_
    sol_symex
    sol_close
  case els =>
    -- dl{ { se1 := a == b }, se1 ≐ false ⟹ [ revert(); x = a; ] x = b }
    apply done .revertBox
    -- dl{ { se1 := a == b }, se1 ≐ false ⟹ true }
    refine close ?_
    sol_symex
    sol_close
  case cov =>
    refine close ?_
    sol_symex
    sol_close

/-! ## The diamond: a guard that fails proves nothing

The same program under the diamond needs `a == b`: where it does not hold
the program reverts, and `revertDiamond` leaves `false`.  With the
precondition, the second goal has both `a = b` and `se1 ≐ false` in its
context. -/

/-- `a == b → ⟨ require(a == b); x = a; ⟩ x == b`. -/
theorem requireDiamond : ⊢ dl!{ a == b → ⟨ require(a == b); x = a; ⟩ x == b } := by
  apply intro
  apply unfold .requireConditionCapture
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply split .requireSimple
  case thn =>
    apply update .localValueAssign
    apply empty
    refine close ?_
    sol_symex
    sol_close
  case els =>
    apply done .revertDiamond
    -- dl{ a = b, { se1 := a == b }, se1 ≐ false ⟹ false }: the context is contradictory
    refine close ?_
    sol_symex
    sol_close
  case cov =>
    -- dl{ a = b, { se1 := a == b } ⟹ ¬(¬se1 ≐ true ∧ ¬se1 ≐ false) }
    refine close ?_
    sol_symex
    sol_close

/-- Without the precondition the diamond is not valid: in `exampleStore`
nothing binds `a`, so the condition is stuck. -/
example : ¬ (⊨ dl!{ ⟨ require(a == b); x = a; ⟩ x == b }) :=
  fun h => h Semantics.State.exampleStore

/-! ## `assert`: the same split

solc compiles a failing `assert` to a revert (a `Panic`), and the table says
so: `assertSimple` has `requireSimple`'s premise.  (KeY's
second line is an obligation `⟹ se` instead, a violated assertion being a
proof failure rather than a revert.) -/

/--
info: @Taclet.assertSimple : ∀ {C : Contract} {k : Nat} {m : Modality} {se : Simple C PrimTy.bool},
  dl{ ⟨[ assert(se); ]⟩ ⇝ se ≐ true ⟹ ⟨[ ]⟩ ; se ≐ false ⟹ ⟨[ revert(); ]⟩ }
-/
#guard_msgs in #check @Taclet.assertSimple

/-- `[ assert(a == b); x = a; ] x == b`, by the strategy. -/
theorem assertBox : ⊨ dl!{ [ assert(a == b); x = a; ] x == b } := by
  sol_symex
  sol_close

/-- `a == b → ⟨ assert(a == b); x = a; ⟩ x == b`. -/
theorem assertDiamond : ⊨ dl!{ a == b → ⟨ assert(a == b); x = a; ⟩ x == b } := by
  sol_symex
  sol_close

/-! ## A revert drops the rest of the program

`revertBox` closes the box whatever follows: `total = 5;` never runs, and
the postcondition `total == 7` is not looked at. -/

/--
trace: ⊢ dl{ ⟹ true }
-/
#guard_msgs in
/-- `[ revert(); total = 5; ] total == 7`. -/
theorem revertDropsRest : ⊢ dl!{ [ revert(); total = 5; ] total == 7 } := by
  apply done .revertBox
  trace_state
  refine close ?_
  exact fun _ => trivial

/-- The diamond of a revert is never true, whatever the postcondition. -/
example : ¬ (⊨ dl!{ ⟨ revert(); ⟩ true }) := fun h => h Semantics.State.exampleStore

/-- Only the rule for the goal's modality fires. -/
example : ⊢ dl!{ [ revert(); ] true } := by
  fail_if_success apply done .revertDiamond
  apply done .revertBox
  refine close ?_
  exact fun _ => trivial

/-! ## Under `if`: a revert in one branch

`if (a == b) { x = 1; } else { revert(); }` ends only through its `then`
branch.  The box holds with no precondition; the diamond needs `a == b`. -/

/-- `[ if (a == b) { x = 1; } else { revert(); } ] x == 1`. -/
theorem branchBox : ⊢ dl!{ [ if (a == b) { x = 1; } else { revert(); }; ] x == 1 } := by
  apply unfold .ifElseUnfold
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply split .ifElseSplit
  case thn =>
    apply update .localValueAssign
    apply empty
    refine close ?_
    sol_symex
    sol_close
  case els =>
    -- dl{ { se1 := a == b }, se1 ≐ false ⟹ [ revert(); ] x = 1 }
    apply done .revertBox
    refine close ?_
    sol_symex
    sol_close
  case cov =>
    refine close ?_
    sol_symex
    sol_close

/-- `a == b → ⟨ if (a == b) { x = 1; } else { revert(); } ⟩ x == 1`. -/
theorem branchDiamond :
    ⊢ dl!{ a == b → ⟨ if (a == b) { x = 1; } else { revert(); }; ⟩ x == 1 } := by
  apply intro
  apply unfold .ifElseUnfold
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply split .ifElseSplit
  case thn =>
    apply update .localValueAssign
    apply empty
    refine close ?_
    sol_symex
    sol_close
  case els =>
    -- dl{ a = b, { se1 := a == b }, se1 ≐ false ⟹ ⟨ revert(); ⟩ x = 1 }
    apply done .revertDiamond
    refine close ?_
    sol_symex
    sol_close
  case cov =>
    refine close ?_
    sol_symex
    sol_close

/-! ## The calculus's traces, for every modality

As chains (`Calculus/Chains.lean`), at a modality `m` and a postcondition
`φ`: every rule of a `require`, an `assert`
and an `if` is the same under either modality, the cover of the split
included (`⟨[ revert(); ]⟩ false ∨ c ∨ c'`, `Premise.coverFml`), so the
lines are written once, up to the `revert();` of a failing branch.  There
the modalities part: after it the chain is one per
modality, `revertBox` to `true` and `revertDiamond` to `false`.

The condition is a `bool` of the storage, `flags[a]`, which `se`
stands for once captured: `{ se1 := find(storage, flags[a]) }`. -/

section Trace
variable (m : Modality) (φ : Post StandardExample)

/-- `revert();` ends the calculus's traces: under the box it closes to `true`,
whatever follows… -/
example : dl![.box]{ ⟨[ revert(); y = 1; ]⟩ φ } ~[revertBox]~> dl![.box]{ true } := rfl

/-- …and under the diamond to `false`. -/
example : dl!{ ⟨ revert(); y = 1; ⟩ φ } ~[revertDiamond]~> dl!{ false } := rfl

/-- The `requireSimple` trace: the condition captured and read, the
split, the goal where it holds run to its end; the goal where it fails is
left at its revert. -/
def requireTrace : dl![m]{ ⟨[ require(flags[a]); y = 1; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → ⟨[ revert(); y = 1; ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } :=
  calc dl![m]{ ⟨[ require(flags[a]); y = 1; ]⟩ φ }
    _ ~[requireConditionCapture]~> dl![m]{ ⟨[ bool se1 = flags[a]; require(se1); y = 1; ]⟩ φ } := by
      sol_chain
    -- `localValueDeclInitDrop`, `storageIndexReadMappingFind`, `requireSimple`: the two
    -- lines between leave `se1` bound by an update in a statement, which `dl![m]{ … }`
    -- reads as a `uint` parameter (`Branch.lean`), so they are not written
    _ ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → ⟨[ y = 1; ]⟩ φ) ∧ (se1 ≐ false → ⟨[ revert(); y = 1; ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
      sol_chain
    _ ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → ⟨[ revert(); y = 1; ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
      sol_chain

/-- Under the box the failing goal closes: the trace, then `revertBox`. -/
example : dl![.box]{ ⟨[ require(flags[a]); y = 1; ]⟩ φ }
    ~*> dl![.box]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → true) ∧
            ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) } :=
  calc dl![.box]{ ⟨[ require(flags[a]); y = 1; ]⟩ φ }
    _ ~*> dl![.box]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → [ revert(); y = 1; ] φ) ∧
            ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) } := requireTrace .box φ
    _ ~[revertBox]~> dl![.box]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → true) ∧
            ([ revert(); ] false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
      sol_chain

/-- Under the diamond it leaves `false`: the condition must hold. -/
example : dl!{ ⟨ require(flags[a]); y = 1; ⟩ φ }
    ~*> dl!{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → false) ∧
            (⟨ revert(); ⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } :=
  (requireTrace .diamond φ).trans (by sol_chain)

/-- `assert` has `require`'s trace (the table's `assertSimple`). -/
def assertTrace : dl![m]{ ⟨[ assert(flags[a]); y = 1; ]⟩ φ }
    ~[assertConditionCapture]~> dl![m]{ ⟨[ bool se1 = flags[a]; assert(se1); y = 1; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → ⟨[ revert(); y = 1; ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
  sol_chain

/-- The `ifElseSplit` trace: both goals to their end, under `m`. -/
def ifTrace : dl![m]{ ⟨[ if (flags[a]) { y = 1; } else { y = 2; }; ]⟩ φ }
    ~[ifElseUnfold]~> dl![m]{ ⟨[ bool se1 = flags[a]; if (se1) { y = 1; } else { y = 2; }; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → ⟨[ y = 1; ]⟩ φ) ∧ (se1 ≐ false → ⟨[ y = 2; ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → { y := 2 } φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
  sol_chain

/-- A revert in the `else` branch: the lines stop at it, the `then` goal done. -/
def ifRevertTrace : dl![m]{ ⟨[ if (flags[a]) { y = 1; } else { revert(); }; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → { y := 1 } φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
  sol_chain

-- In the `then` branch it stops them before the `else` goal: go on after `cases m`.
/--
error: sol_chain: the derivation of
  dl{ ⟨[ if (flags[a]) {revert();} else {y = 1;}; ]⟩ φ }
does not reach
  dl{
    { se1 := find(storage, flags[a]) }
      ((se1 ≐ true → true) ∧ (se1 ≐ false → { y := 1 } φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
Its lines:
    dl{ ⟨[ if (flags[a]) {revert();} else {y = 1;}; ]⟩ φ }
  ~[ifElseUnfold]~>
    dl{ ⟨[ bool se1 = flags[a]; if (se1) {revert();} else {y = 1;}; ]⟩ φ }
  ~[localValueDeclInitDrop]~>
    dl{ ⟨[ se1 = flags[a]; if (se1) {revert();} else {y = 1;}; ]⟩ φ }
  ~[storageIndexReadMappingFind]~>
    dl{ { se1 := find(storage, flags[a]) } ⟨[ if (se1) {revert();} else {y = 1;}; ]⟩ φ }
  ~[ifElseSplit]~>
    dl{
  { se1 := find(storage, flags[a]) }
    ((se1 ≐ true → ⟨[ revert(); ]⟩ φ) ∧
        (se1 ≐ false → ⟨[ y = 1; ]⟩ φ) ∧ (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) }
  (the line after depends on the modality m, through a `revert();` (`revertBox`, `revertDiamond`): go on after `cases m`)
-/
#guard_msgs in
example : dl![m]{ ⟨[ if (flags[a]) { revert(); } else { y = 1; }; ]⟩ φ }
    ~*> dl![m]{ { se1 := find(storage, flags[a]) }
          ((se1 ≐ true → true) ∧ (se1 ≐ false → { y := 1 } φ) ∧
            (⟨[ revert(); ]⟩ false ∨ se1 ≐ true ∨ se1 ≐ false)) } := by
  sol_chain

/-- After `cases m`, each modality runs to the end. -/
example : ∃ ψ, Nonempty (dl![m]{ ⟨[ if (flags[a]) { revert(); } else { y = 1; }; ]⟩ φ } ~*> ψ) := by
  cases m <;> exact ⟨_, ⟨by sol_chain⟩⟩

end Trace

end Solidity.Examples.Revert
