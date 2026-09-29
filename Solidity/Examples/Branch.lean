import Solidity.Calculus.Close

/-!
# A branch: `ifElseUnfold` and `ifElseSplit`

One case of control flow: `if (c) { … } else { … };`.  solkey's taclets
(`solidityProgramRules.key`) come in two steps.  A condition that is not a
simple expression — `a == b`, `alice.age == 4`, `!flag` — is captured into a
fresh boolean first (`ifElseUnfold`); on a simple condition `ifElseSplit`
branches:

```
ifElseSplit {
    \schemaVar \formula post;
    \schemaVar \program SimpleExpression se;
    \schemaVar \program Statement thenStm;
    \schemaVar \program Statement elseStm;

    \find( ==> \modality{#mod}{c# if (s#se) s#thenStm else s#elseStm #c}\endmodality(post))
    "if s#se true":
        \replacewith( ==> \modality{#mod}{c# s#thenStm #c}\endmodality(post))
        \add(se = TRUE ==>);
    "if s#se false":
        \replacewith( ==> \modality{#mod}{c# s#elseStm #c}\endmodality(post))
        \add(se = FALSE ==>)
    \heuristics(simplify_prog)
};
```

It is a rule with *two* premises: one goal per branch, the condition (or its
negation) added to the left of `⟹`, the rest of the program `#c` after the
branch in both.  Under `⊢` it is `apply split .ifElseSplit`, which leaves the
goals `thn` and `els`, and a third, `cov`: a condition can be stuck (a local
read before it is bound), so under the diamond the two conditions owe that
one of them holds (`Premise.cover`); under the box `cov` is `true`.

The old table's condition-directed rewrites (`ifElseTrue`, `ifElseFalse`,
`ifElseNegated`) are gone: a literal is simple, so `if (true)` splits like any
other condition, and `!c` is captured like `a == b`.  The goal whose
hypothesis is `true ≐ false` is then closed by the logic, not by a rule.
-/

namespace Solidity.Examples.Branch

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## The taclets

`thn` and `els` are schema variables for whole blocks (KeY's `#s0`). -/

/--
info: @Taclet.ifElseUnfold : ∀ {C : Contract} {k : Nat} {m : Modality} {nse : Val C PrimTy.bool} {thn els : List (Stmt C)},
  dl{ ⟨[ if (nse) thn else els; ]⟩ ⇝ ⟨[ bool se = nse; if (se) thn else els; ]⟩ }
-/
#guard_msgs in #check @Taclet.ifElseUnfold

/--
info: @Taclet.ifElseSplit : ∀ {C : Contract} {k : Nat} {m : Modality} {se : Simple C PrimTy.bool} {thn els : List (Stmt C)},
  dl{ ⟨[ if (se) thn else els; ]⟩ ⇝ se ≐ true ⟹ ⟨[ thn ]⟩ ; se ≐ false ⟹ ⟨[ els ]⟩ }
-/
#guard_msgs in #check @Taclet.ifElseSplit

/-! ## Example: a branch on two locals

`if (a == b) { x = 2; } else { x = 1; }` leaves `x` nonzero either way.  The
condition is captured into `se1`, the capture's declaration dropped, and its
value bound by `binopAssignment`; then the split. -/

/-- `if (a == b) { x = 2; } else { x = 1; }` ends with `x != 0`. -/
theorem branchLocals : ⊢ dl!{ [ if (a == b) { x = 2; } else { x = 1; }; ] x != 0 } := by
  apply unfold .ifElseUnfold
  -- dl{ ⟹ [ bool se1 = a == b; if (se1) { x = 2; } else { x = 1; }; ] ¬x = 0 }
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  -- dl{ { se1 := a == b } ⟹ [ if (se1) { x = 2; } else { x = 1; }; ] ¬x = 0 }
  apply split .ifElseSplit
  case thn =>
    -- dl{ { se1 := a == b }, se1 ≐ true ⟹ [ x = 2; ] ¬x = 0 }
    apply update .localValueAssign
    apply empty
    refine close ?_
    sol_symex
    sol_close
  case els =>
    -- dl{ { se1 := a == b }, se1 ≐ false ⟹ [ x = 1; ] ¬x = 0 }
    apply update .localValueAssign
    apply empty
    refine close ?_
    sol_symex
    sol_close
  case cov =>
    -- dl{ { se1 := a == b } ⟹ true }: the box owes nothing
    refine close ?_
    sol_symex
    sol_close

/-! ## The three goals, pinned

The condition is added *after* the updates of the context: it is read in the
state the `if` runs in. -/

/--
trace: case thn
⊢ dl{
    {
        se1 :=
          ‹Term.binop BinOp.eqB PrimTy.uint (Simple.local (Var.user "a")).lower (Simple.local (Var.user "b")).lower› },
    se1 ≐ true ⟹ [ x = 2; ] ¬x = 0 }

case els
⊢ dl{
    {
        se1 :=
          ‹Term.binop BinOp.eqB PrimTy.uint (Simple.local (Var.user "a")).lower (Simple.local (Var.user "b")).lower› },
    se1 ≐ false ⟹ [ x = 1; ] ¬x = 0 }

case cov
⊢ dl{
    {
        se1 :=
          ‹Term.binop BinOp.eqB PrimTy.uint (Simple.local (Var.user "a")).lower (Simple.local (Var.user "b")).lower› } ⟹
    true }
-/
#guard_msgs in
example : ⊢ dl!{ [ if (a == b) { x = 2; } else { x = 1; }; ] x != 0 } := by
  apply unfold .ifElseUnfold
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply split .ifElseSplit
  trace_state
  case thn | els =>
    apply update .localValueAssign
    apply empty
    refine close ?_
    sol_symex
    sol_close
  case cov =>
    refine close ?_
    sol_symex
    sol_close

/-! ## Under the diamond: the condition decides

With the precondition `a == b` the `else` goal has both `a = b` and
`se1 ≐ false` in its context, a contradiction; and the precondition binds
`a` and `b`, so the condition is not stuck and `cov` holds. -/

/-- `a == b → ⟨ if (a == b) { x = 2; } else { x = 1; } ⟩ x == 2`. -/
theorem branchDiamond :
    ⊢ dl!{ a == b → ⟨ if (a == b) { x = 2; } else { x = 1; }; ⟩ x == 2 } := by
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
    -- dl{ a = b, { se1 := a == b }, se1 ≐ false ⟹ ⟨ x = 1; ⟩ x = 2 }
    apply update .localValueAssign
    apply empty
    refine close ?_
    sol_symex
    sol_close
  case cov =>
    -- dl{ a = b, { se1 := a == b } ⟹ ¬(¬se1 ≐ true ∧ ¬se1 ≐ false) }
    refine close ?_
    sol_symex
    sol_close

/-- Without the precondition the diamond is not valid: in a state that does
not bind `a`, the condition is stuck and the program never ends. -/
example : ¬ (⊨ dl!{ ⟨ if (a == b) { x = 2; } else { x = 1; }; ⟩ x != 0 }) :=
  fun h => h Semantics.State.exampleStore

/-! ## A literal condition

`true` is simple: no capture, and the split's `else` goal carries
`true ≐ false`.  (The old `ifElseTrue` collapsed this in one rewrite.) -/

/--
trace: ⊢ ⊨
    dl{
      (true ≐ true → [ age = 1; ] select(storage, age) = 1) ∧
        (true ≐ false → [ age = 2; ] select(storage, age) = 1) ∧ true }
-/
#guard_msgs in
/-- `if (true) { age = 1; } else { age = 2; }` writes `1`. -/
theorem ifTrue : ⊨ dl!{ [ if (true) { age = 1; } else { age = 2; }; ] age == 1 } := by
  sol_step
  trace_state
  sol_symex
  sol_close

/-- `if (false) { x = 2; } else { x = 1; }`, under the diamond: the `then`
goal is the vacuous one. -/
theorem ifFalse : ⊨ dl!{ ⟨ if (false) { x = 2; } else { x = 1; }; ⟩ x == 1 } := by
  sol_symex
  sol_close

/-! ## A negated condition

`!true` is not simple: it is captured like `a == b` (`ifElseUnfold`), where
the old table swapped the branches (`ifElseNegated`). -/

/--
trace: ⊢ ⊨ dl{ [ bool se1 = !true; if (se1) {age = 2;} else {age = 1;}; ] ¬select(storage, age) = 0 }
-/
#guard_msgs in
/-- `if (!true) { age = 2; } else { age = 1; }` leaves `age != 0`. -/
theorem ifNegated : ⊨ dl!{ [ if (!true) { age = 2; } else { age = 1; }; ] age != 0 } := by
  sol_step
  trace_state
  sol_symex
  sol_close

/-! ## A condition that reads storage

`alice.age == 4` is captured like any other condition, and inside the
capture the read operand is captured again (`binopUnfoldLeft`) and read by
Step 3's `storageFieldReadFind`: `{ se2 := find(storage, alice.age) }`,
then `{ se1 := se2 == 4 }`.  The old rewrite chain stopped at the split, a
sequent rule it could not name; here the split is a rule like the others. -/

/-- `if (alice.age == 4) { total = 1; } else { total = 2; } uint y = total;`
ends with `y != 0`. -/
theorem branchOnStorage :
    ⊨ dl!{ [ if (alice.age == 4) { total = 1; } else { total = 2; }; uint y = total; ] y != 0 } := by
  sol_symex
  sol_close

/-! ## A conditional of references

A conditional whose branches are references (`c ? alice : bob`) has no value
to lower: the elaborator binds the reference it picks to a fresh alias (or
memory local) in a branch, and the statement uses that
(`sol{ … }`, `Syntax.lean`): `Person storage p = c ? alice : bob;` is
`if (c) { Person storage sp1 = alice; } else { Person storage sp1 = bob; }
Person storage p = sp1;`.  The branch is `ifElseSplit`'s, as `ternaryToIf`'s
is for a value. -/

/-- `Person storage p = c ? alice : bob; p.age = 7;` writes the person the
condition picks. -/
theorem ternaryOfReferences :
    ⊨ dl!{ [ bool c = true; Person storage p = c ? alice : bob; p.age = 7;
             uint r = alice.age; ] r == 7 } := by
  sol_symex
  sol_close

/-- `Person memory m = c ? mx : my;` — in memory the pick is by identity:
a write through `m` is a write to `my`. -/
theorem ternaryOfMemoryReferences :
    ⊨ dl!{ [ bool c = false; Person memory mx = alice; Person memory my = bob;
             Person memory m = c ? mx : my; m.age = 9; uint r = my.age; ] r == 9 } := by
  sol_symex
  sol_close

end Solidity.Examples.Branch
