import Solidity.Examples.Common
import Solidity.Semantics
import Solidity.JudgmentSplit

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 8000000

/-! ## Dynamic-logic derivations

The block-level rewriting of the other derivation files, lifted to full
dynamic-logic judgments `< program > post`: one taclet application
rewrites the program inside the modality and leaves the postcondition
untouched, e.g.

`< alice.account.balance = 10 > φ`
`⇝ᵈ[.storageFieldWriteUnfoldLeftFst]`
`< uint rv = 10; Account storage sp = alice.account; sp@Account.balance = rv > φ`

(the aliases the unfold rules introduce are the fixed names `rv` and
`sp`). The semantic counterparts of these judgments — with `.Holds`
verified by `native_decide` against the interpreter — live in
`Examples/Taclets/`. -/

/-! The step relations themselves (`JudgmentStep`, `NamedJudgmentStep`,
`JudgmentMultiStep`, the `⇝ᵈ` arrows and their `Trans` instances) live in
`MultiStep.lean`, beside their block-level twins: they depend on nothing but
the AST and the rules, and `sol_derivation` builds either layer from the same
source syntax.  The `dl_*` tactics live in `Examples/Common.lean`, beside the
block tactics they lift.  What stays here is the examples. -/


/-! ### The headline chain, at the judgment level

The calculus writes the deep storage write as

```
   ⟨[ alice.account.balance = 10; ]⟩ φ
⇝  ⟨[ Account storage acc = alice.account; acc.balance = 10; ]⟩ φ
⇝  {acc := alice·account} ⟨[ acc.balance = 10; ]⟩ φ
⇝  {acc := alice·account} {storage := save(storage, acc·balance, 10)} φ
⇝  {acc := alice·account ‖ storage := save(storage, alice·account·balance, 10)} φ
```

Three of the four pieces of that rendering are available here: the combined
modality `⟨[ … ]⟩` is `<[ … ]>`, the opaque postcondition `φ` is `‹φ›` over a
`variable`, and the rule sits on the arrow rather than in surrounding prose.
What is still missing is the update lines -- the rewrite layer ends at the
empty program, and the state update of each terminal rule lives in
`Wp/Terminal/Table.lean`.

The calculus's chain is also one line shorter than this one, for the reason
`Examples/Derivations/Paper.lean`'s header gives: the calculus freezes
the value operand into `rv` before it captures any part of the target
(`Counterexamples/ErrorOrder.lean` is why), which costs three administrative
steps.  They are elided into the `⇝*` line, as the calculus elides with
`⇝*`. -/

section
variable (φ : WrappedExpr)

sol_derivation deepFieldWriteJudgment :
    sol!{ <[ alice.account.balance = 10 ]> ‹φ› }
  ⇝[.storageFieldWriteUnfoldLeftFst]
    sol!{ <[ uint rv = 10;
             Account storage sp = alice.account;
             sp@Account.balance = rv ]> ‹φ› }
  ⇝* sol!{ <[ Account storage sp = alice.account;
              sp@Account.balance = rv ]> ‹φ› }
  ⇝[.storagePlaceAlias]
    sol!{ <[ sp@Account.balance = rv ]> ‹φ› }
  ⇝[.storageFieldWriteSave]
    sol!{ <[ ]> ‹φ› }

/-- The read twin.  It needs no value operand frozen, so its three rewrite
steps are exactly three rules.  Written with the ASCII arrows, which parse to
the same relations and still print as `⇝`. -/
sol_derivation deepFieldReadJudgment :
    sol!{ <[ result = alice.account.balance ]> ‹φ› }
  ~>[.storageFieldReadUnfoldRightFst]
    sol!{ <[ Account storage sp = alice.account;
             result = sp@Account.balance ]> ‹φ› }
  ~>[.storagePlaceAlias]
    sol!{ <[ result = sp@Account.balance ]> ‹φ› }
  ~>[.storageFieldReadFind]
    sol!{ <[ ]> ‹φ› }

/-- The calculus's "Let ω = …": a `let` prefix names the inactive suffix, and the
chain splices it back with `.. omega`.  `where` is the same thing written
after the chain. -/
sol_derivation deepFieldWriteInContext let omega := sblock!{ result = alice.account.balance } :
    sol!{ <[ alice.account.balance = 10; .. omega ]> ‹φ› }
  ⇝[.storageFieldWriteUnfoldLeftFst]
    sol!{ <[ uint rv = 10;
             Account storage sp = alice.account;
             sp@Account.balance = rv; .. omega ]> ‹φ› }
  ⇝* sol!{ <[ Account storage sp = alice.account;
              sp@Account.balance = rv; .. omega ]> ‹φ› }
  ⇝[.storagePlaceAlias]
    sol!{ <[ sp@Account.balance = rv; .. omega ]> ‹φ› }
  ⇝[.storageFieldWriteSave]
    sol!{ <[ result = alice.account.balance ]> ‹φ› }

end

/-! ### Deep storage write, one taclet application

The same rewriting against a *concrete* postcondition, which is what the
`native_decide` examples of `Examples/Taclets/` need: `‹φ›` is opaque, so
nothing evaluates it. -/

example :
    sol!{ < alice.account.balance = 10 > (alice.account.balance == 10) }
      ⇝ᵈ[.storageFieldWriteUnfoldLeftFst]
    sol!{ < uint rv = 10;
           Account storage sp = alice.account;
           sp@Account.balance = rv > (alice.account.balance == 10) } := by
  dl_rule_step

/-! ### The same judgment, reduced to the empty program

Written as a `calc` with explicit per-line tactics: the hand spelling that
`sol_derivation` writes for you, kept here as the regression test that the
`⇝ᵈ` relations and their `Trans` instances still compose. -/

example :
    sol!{ < alice.account.balance = 10 > (alice.account.balance == 10) }
      ⇝ᵈ* sol!{ < > (alice.account.balance == 10) } :=
  calc
    sol!{ < alice.account.balance = 10 > (alice.account.balance == 10) }
      ⇝ᵈ[.storageFieldWriteUnfoldLeftFst]
          sol!{ < uint rv = 10;
                 Account storage sp = alice.account;
                 sp@Account.balance = rv >
                 (alice.account.balance == 10) }        := by dl_rule_step
    _ ⇝ᵈ* sol!{ < Account storage sp = alice.account;
                 sp@Account.balance = rv >
                 (alice.account.balance == 10) }        := by
          dl_steps [.localValueDeclInitDrop, .valueDeclSkip, .localValueAssign]
    _ ⇝ᵈ[.storagePlaceAlias]
          sol!{ < sp@Account.balance = rv >
                 (alice.account.balance == 10) }        := by dl_rule_step
    _ ⇝ᵈ[.storageFieldWriteSave]
          sol!{ < > (alice.account.balance == 10) }     := by dl_rule_step

/-! ### `storage-root-postincrement.key` as a dynamic-logic derivation -/

example :
    sol!{ < age = 10; age++; result = age > (result == 11) }
      ⇝ᵈ* sol!{ < > (result == 11) } :=
  calc
    sol!{ < age = 10; age++; result = age > (result == 11) }
      ⇝ᵈ[.storageRootWriteStore]
          sol!{ < age++; result = age > (result == 11) } := by dl_rule_step
    _ ⇝ᵈ[.storageRootIncDec .postInc]
          sol!{ < result = age > (result == 11) }        := by dl_rule_step
    _ ⇝ᵈ[.storageRootReadSelect]
          sol!{ < > (result == 11) }                     := by dl_rule_step

/-- The same judgment, verified against the executable semantics. -/
example :
    (sol!{ < age = 10; age++; result = age > (result == 11) }).Holds := by
  native_decide

/-! ### If-then-else in a box judgment -/

example :
    sol!{ [ if (true) { age = amount } else { age = i } ] (age == amount) }
      ⇝ᵈ* sol!{ [ ] (age == amount) } :=
  calc
    sol!{ [ if (true) { age = amount } else { age = i } ] (age == amount) }
      ⇝ᵈ[.ifElseTrue] sol!{ [ age = amount ] (age == amount) } := by dl_rule_step
    _ ⇝ᵈ[.storageRootWriteStore]
          sol!{ [ ] (age == amount) }                       := by dl_rule_step

/-! ### Symbolic condition: capture, then the proof-level split

`ifElseUnfold` hoists a complex condition into the stack value
`pv`. The resulting `if (pv@bool) …` matches no rewrite rule *by design*
(mirroring KeY, where the program rules stop and the sequent rule
`ifthenelse_split` takes over): the derivation continues with the
proof-level `SolidityJudgment.ite_split`. -/

example :
    sol!{ < if ((alice.age == 4)) { total = 1 } else { total = 2 } >
          (total == 1) }
      ⇝ᵈ[.ifElseUnfold]
    sol!{ < bool pv = ((alice.age == 4));
           if (pv@bool) { total = 1 } else { total = 2 } > (total == 1) } := by
  dl_rule_step

/-- At the stuck point the derivation continues with
`SolidityJudgment.ite_split` — a *universally quantified* split over any
state binding `pv`, which `native_decide` cannot express. -/
example (s : Semantics.State) (b : Bool)
    (thn els rest : Block) (post : WrappedExpr)
    (h : Semantics.evalValue s sexpr!{ pv@bool } = .ok (s, .bool b)) :
    (SolidityJudgment.mk ⟨.diamond, Stmt.ite sexpr!{ pv@bool } thn els :: rest⟩
        post).Holds s ↔
      ((b = true ->
          (SolidityJudgment.mk ⟨.diamond, thn ++ rest⟩ post).Holds s) ∧
        (b = false ->
          (SolidityJudgment.mk ⟨.diamond, els ++ rest⟩ post).Holds s)) :=
  SolidityJudgment.ite_split h

end Solidity.Examples
