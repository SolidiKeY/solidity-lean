import Solidity.Calculus.Close
import Solidity.Calculus.Core.Surface
import Solidity.Calculus.Core.Closers
import Solidity.Tools.CoreInspect

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
branch in both.  Under `⊢` it is `apply split .ifElseSplit`, which leaves
KeY's two goals `thn` and `els`: the locals are typed, so a `bool`
condition is never stuck and no third goal covers it.  Each branch is a
block, whose end prints as `}`.

The old table's condition-directed rewrites (`ifElseTrue`, `ifElseFalse`,
`ifElseNegated`) are gone: a literal is simple, so `if (true)` splits like any
other condition, and `!c` is captured like `a == b`.  The goal whose
hypothesis is `true ≐ false` is then closed by the logic, not by a rule.
-/

namespace Solidity.Examples.Tactics.Branch

open Proves

local instance : InContract := ⟨StandardExample⟩

open scoped Solidity.Core.Surface

/-! ## The taclets

`thn` and `els` are schema variables for whole blocks (KeY's `#s0`). -/

/--
info: @Taclet.ifElseUnfold : ∀ {C : Contract} {k : Nat} {m : Modality} {nse : Val C PrimTy.bool}
  {thenStm elseStm : List (Stmt C)},
  dl{ ⟨[ if (nse) thenStm else elseStm; ]⟩ ⇝ ⟨[ bool se = nse; if (se) thenStm else elseStm; ]⟩ }
-/
#guard_msgs in #check @Taclet.ifElseUnfold

/--
info: @Taclet.ifElseSplit : ∀ {C : Contract} {k : Nat} {m : Modality} {se : Simple C PrimTy.bool}
  {thenStm elseStm : List (Stmt C)},
  dl{ ⟨[ if (se) thenStm else elseStm; ]⟩ ⇝
    "if s#se true": se ≐ true ⟹ ⟨[ thenStm ]⟩ ; "if s#se false": se ≐ false ⟹ ⟨[ elseStm ]⟩ }
-/
#guard_msgs in #check @Taclet.ifElseSplit

/-! ## Example: a branch on two locals

`if (a == b) { x = 2; } else { x = 1; }` leaves `x` nonzero either way.  The
condition is captured into `se1`, the capture's declaration dropped, and its
value bound by `binopAssignment`; then the split.  The two goals are pinned
(the parameters `a`, `b`, `x` bound by `∀`, taken by `allRight` first):
the condition is added *after* the updates of the context, since it is read in
the state the `if` runs in. -/

/--
trace: case thn
⊢ dl{ ∀ uint x, ∀ uint b, ∀ uint a,
    { se1 := ‹Tm.app2 (Op2.binop BinOp.eqB PrimTy.uint) (Tm.pvV (Var.user "a")) (Tm.pvV (Var.user "b"))› }, se1 ≐ true ⟹
    [ x = 2; } ] ¬x = 0 }

case els
⊢ dl{ ∀ uint x, ∀ uint b, ∀ uint a,
    { se1 := ‹Tm.app2 (Op2.binop BinOp.eqB PrimTy.uint) (Tm.pvV (Var.user "a")) (Tm.pvV (Var.user "b"))› },
    se1 ≐ false ⟹ [ x = 1; } ] ¬x = 0 }
-/
#guard_msgs in
/-- `if (a == b) { x = 2; } else { x = 1; }` ends with `x != 0`. -/
theorem branchLocals : ⊢ dl!{ [ if (a == b) { x = 2; } else { x = 1; }; ] x != 0 } := by
  apply allIntro
  apply allIntro
  apply allIntro
  apply unfold .ifElseUnfold
  -- dl{ ⟹ [ bool se1 = a == b; if (se1) { x = 2; } else { x = 1; }; ] ¬x = 0 }
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  -- dl{ { se1 := a == b } ⟹ [ if (se1) { x = 2; } else { x = 1; }; ] ¬x = 0 }
  apply split .ifElseSplit
  trace_state
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

/-! ## A literal condition

`true` is simple: no capture, and the split's `else` goal carries
`true ≐ false`.  (The old `ifElseTrue` collapsed this in one rewrite.) -/

/--
trace: ⊢ ⊨ dl{ (true ≐ true → [ age = 1; } ] find(storage, age) = 1) ∧ (true ≐ false → [ age = 2; } ] find(storage, age) = 1) }
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
trace: ⊢ ⊨ dl{ [ bool se1 = !true; if (se1) {age = 2;} else {age = 1;}; ] ¬find(storage, age) = 0 }
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
memory local), and the statement uses that
(`sol{ … }`, `Syntax.lean`): `Person storage p = c ? alice : bob;` is
`Person storage sp1; if (c) { sp1 = alice; } else { sp1 = bob; }
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

/-! A local of a block, and a branch after it that declares the same name at
another type: Solidity scopes the first to its block.  The untyped program
has no blocks, so the elaborator writes the block flat and renames its local
apart (`x_1`, `freshenBlocks`): the locals check (`resolve`,
`Syntax/Resolve.lean`) reads a branch as a scope and refuses a binder of a
name in scope, so the program is `Fresh` and `Prog.run_erase` covers it.
The same holds for a `for` loop's init. -/

/-- info: bool c = true; bool x_1 = true; if (c) { uint x = 1; } else { } -/
#guard_msgs in
#eval IO.println (Prog.toStr
  (sol{ bool c = true; { bool x = true; } if (c) { uint x = 1; } } : Prog StandardExample))

/-- info: bool c = true; int i_1 = 0; while (i_1 < 1) { i_1++; } if (c) { uint i = 1; } else { } -/
#guard_msgs in
#eval IO.println (Prog.toStr
  (sol{ bool c = true; for (int i = 0; i < 1; i++) { } if (c) { uint i = 1; } } : Prog StandardExample))

/-! Two loops of one index: the first's is renamed apart, the second keeps
its name. -/

/--
info: uint n = 0; uint i_1 = 0; while (i_1 < 2) { n += i_1; i_1++; } uint i = 0; while (i < 3) { n += i; i++; }
-/
#guard_msgs in
#eval IO.println (Prog.toStr (sol{ uint n = 0; for (uint i = 0; i < 2; i++) { n += i; }
    for (uint i = 0; i < 3; i++) { n += i; } } : Prog StandardExample))

-- a local declared again in its own scope is still refused
/-- error: Solidity elaboration failed: x is already declared, or names a state variable -/
#guard_msgs in #check (sol{ uint x = 2; { uint x = 3; } } : Prog StandardExample)

-- a flat block's local declared twice in it: refused at the block's index
#guard match elabProgAt StandardExample
    sol_raw!{ uint a = 0; { uint x = 1; uint x = 2; } uint x = 3; } with
  | .error (i, _) => i == 1
  | .ok _ => false

/- Declared alike in both branches, then at another type in a later one. -/
#guard (Core.Prog.resolveCheck [] (sol{ bool c = true; if (c) { uint t = 1; } else { uint t = 2; }
    if (c) { bool t = true; } } : Prog StandardExample)).toBool

end Solidity.Examples.Tactics.Branch

/-! ## Read without the switch

Under the diamond a walk's leaves are not closed by their erasure yet
(`Core.Proves.close` takes box contexts), and the stuck condition of the
refutation is today's: scoped, `a` and `b` are bound by `∀` and the diamond
holds. -/

namespace Solidity.Examples.Tactics.Branch

open Proves

local instance : InContract := ⟨StandardExample⟩

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
  fun h => (h Semantics.State.exampleStore).1

end Solidity.Examples.Tactics.Branch
