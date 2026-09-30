import Solidity.Calculus.Close

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

end Solidity.Examples.Revert
