import Solidity.Update.Bridges
import Solidity.Semantics.DecEq

/-!
# The update algebra, on the headline example

The calculus ends the derivation of `alice.account.balance = 10;` with two
lines the rewrite layer cannot show:

```
⇝ {acc := alice·account} {storage := save(storage, acc·balance, 10)} φ
⇝ {acc := alice·account ‖ storage := save(storage, alice·account·balance, 10)} φ
```

The first is the *sequential* form the derivation accumulates, the second
the *parallel* form the merge law produces.  This file writes both down for
that program and checks that they agree — abstractly by
`Upd.Par.seq_single`, and concretely against the interpreter on
`State.exampleStore`.
-/

namespace Solidity.UpdExamples

open Semantics Wp Upd Examples StandardExample SoliditySyntax

/-! ## The two elementary updates of the headline derivation -/

/-- `acc := alice·account` — the calculus's alias update, Lean's
`storagePlaceAlias` on the fixed name `sp`. -/
def accAlias : Elem :=
  Elem.env "sp"
    (fun s => (placePath s sexpr!{ alice.account }).map fun p =>
      Binding.spath p.1 p.2)

/-- `storage := save(storage, sp·balance, rv)` — the terminal write. -/
def balanceSave : Elem :=
  Elem.storage (fun s =>
    (storageAssignUpd (splace!{ sp@Account.balance }) sexpr!{ rv@uint } s).map
      State.storage)

/-- Each of them really is the rule's update: the alias element is
`storagePlaceAliasUpd`, the storage element is `storageAssignUpd`.  These
are the two bridges of `Update/Bridges.lean` instantiated. -/
theorem accAlias_is_rule :
    Par.toUpd [accAlias] = storagePlaceAliasUpd "sp" sexpr!{ alice.account } :=
  storagePlaceAliasUpd_bridge "sp" _ (by decide)

theorem balanceSave_is_rule :
    Par.toUpd [balanceSave] =
      storageAssignUpd (splace!{ sp@Account.balance }) sexpr!{ rv@uint } :=
  storageAssignUpd_field _ _ _ _ _

/-! ## The merge

That last `⇝` is not a rule application: it is the update calculus
collapsing `{u}{v}` into `{u ‖ {u}v}`.  `Upd.Par.seq_single` is that step,
and here it is on the two elements above. -/

theorem headline_merge :
    Upd.seq (Par.toUpd [accAlias]) (Par.toUpd [balanceSave]) =
      Par.toUpd [accAlias, balanceSave.after [accAlias]] :=
  Par.seq_single [accAlias] balanceSave

/-! ## …and the same thing, run

`seq_single` is an equality of functions, so it says nothing about any
*particular* state unless a state is supplied.  Here is the calculus store:
both sides take it to the same state, and that state is the one the
interpreter reaches by executing the two statements. -/

/-- The sequential and the parallel form agree on the calculus store. -/
example :
    Upd.seq (Par.toUpd [accAlias]) (Par.toUpd [balanceSave]) State.exampleStore =
      Par.toUpd [accAlias, balanceSave.after [accAlias]] State.exampleStore := by
  rw [headline_merge]

/-- And the accumulated update is what the program does: running
`Account storage sp = alice.account; sp.balance = rv;` from a state that
binds `rv` reaches exactly `{sp := alice·account ‖ storage := save(…)}` of
it.  The `rv` binding is the freeze the calculus performs first
(`Counterexamples/ErrorOrder.lean`). -/
example :
    execBlock (State.exampleStore.setEnv "rv" (Binding.val (Value.int 10)))
        sblock!{ Account storage sp = alice.account; sp@Account.balance = rv }
      = Par.toUpd [accAlias, balanceSave.after [accAlias]]
          (State.exampleStore.setEnv "rv" (Binding.val (Value.int 10))) := by
  native_decide

end Solidity.UpdExamples
