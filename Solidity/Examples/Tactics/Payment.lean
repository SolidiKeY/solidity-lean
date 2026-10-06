import Solidity.Calculus.Sequents

/-!
# Payment: `transfer` and `send`, as `⊢` walks

`sadr.transfer(se);` has one rule, under the box, `transferNoCallbackBox`,
which books the payment on the ledger and nothing else: the update
`{ net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) }`,
`sadr`'s entry down by the amount unless `sadr` is the contract itself,
which books nothing (solkey's `\if(sadr = self)`).  Under the diamond a
payment has no rule (`LeanTaclet.transferDiamond` closes it to `false`).
Whether the world pays is not the rule's: on the EVM a refused payment
reverts, which the box does not see (`Evm.compile_box`).  The worked
examples' traces are `Examples/Chains/Payment.lean`'s; here the sequents
themselves, each with its whole context, are the goals of a walk, each a
checked line `show sequent!{ Γ ⟹ ψ }` (`Calculus/Sequents.lean`).

`pv = sadr.send(se);` has a rule under either modality (§4), with a goal per
outcome: `"send succeeded"`, the same booking with `pv` true, and `"send
failed"`, nothing booked and `pv` false.  A refused send returns `false`
rather than reverting, and the interpreter says which outcome a run takes
(`Semantics.sendAt`, the transaction's oracle), so the diamond has its rule
too (`sendNoCallbackDiamond`), with the amount's sign owed first
(`"non-negative amount"`).

The ledger's postconditions and the frame of a transfer are `Net.lean`'s;
the callback rules are `Callback.lean`'s.
-/

namespace Solidity.Examples.Tactics.Payment

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · The rule -/

/--
info: @Taclet.transferNoCallbackBox : ∀ {C : Contract} {k : Nat} {sadr se : Simple C PrimTy.uint},
  dl{ [ sadr .transfer(se); ] ⇝ { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.transferNoCallbackBox

/-! ## 2 · The walk -/

/-- `[ to.transfer(5); ] true` as a `⊢` walk: one rule, one goal, a checked
sequent (`Calculus/Sequents.lean`); the chain, from the receiver `3`, is
`Chains.Payment.Transfer5.chain`. -/
theorem transferBox : ⊢ dl!{ [ to.transfer(5); ] true } := by
  apply update .transferNoCallbackBox
  show sequent!{ { net := if(to = this) then net else store(net, at(to), select(net, at(to)) - 5) }
      ⟹ [ ] true }
  apply empty
  show sequent!{ { net := if(to = this) then net else store(net, at(to), select(net, at(to)) - 5) }
      ⟹ true }
  refine close ?_
  sol_symex
  sol_close

/-! ## 3 · Valid for every receiver and amount

The worked chains (`Chains/Payment.lean`) start from one concrete receiver
and amount; the strategy proves the boxes for all of them. -/

/-- `[ to.transfer(x + 2); ] true`, for every `to` and `x`. -/
theorem transferSumValid : ⊨ dl!{ [ to.transfer(x + 2); ] true } := by
  sol_symex
  sol_close

/-- `[ owner.transfer(5); ] true`, in every storage. -/
theorem transferOwnerValid : ⊨ dl!{ [ owner.transfer(5); ] true } := by
  sol_symex
  sol_close

/-! ## 4 · `send`: a goal per outcome -/

/--
info: @Taclet.sendNoCallbackBox : ∀ {C : Contract} {k : Nat} {pv : Var} {sadr se : Simple C PrimTy.uint},
  dl{ [ pv = sadr .send(se); ] ⇝
    "send succeeded": { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) ‖ pv := true } ⟨[ ]⟩ ;
      "send failed": { pv := false } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.sendNoCallbackBox

/--
info: @Taclet.sendNoCallbackDiamond : ∀ {C : Contract} {k : Nat} {pv : Var} {sadr se : Simple C PrimTy.uint},
  dl{ ⟨ pv = sadr .send(se); ⟩ ⇝
    "non-negative amount": 0 <= se ;
      "send succeeded": { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) ‖ pv := true } ⟨[
        ]⟩ ;
      "send failed": { pv := false } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.sendNoCallbackDiamond

/-- `[ ok = to.send(5); ] true` as a `⊢` walk: `sendNoCallbackBox`'s two
goals, `"send succeeded"` and `"send failed"`, each a checked sequent; it
has no formula goal. -/
theorem sendBox : ⊢ dl!{ [ ok = to.send(5); ] true } := by
  apply cases .sendNoCallbackBox
  · simp only [List.not_mem_nil, false_implies, implies_true]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  refine ⟨?_, ?_⟩
  · show sequent!{ { net := if(to = this) then net else store(net, at(to), net(to) - 5) ‖ ok := true }
        ⟹ [ ] true }
    apply empty
    refine close ?_
    sol_symex
    sol_close
  · show sequent!{ { ok := false } ⟹ [ ] true }
    apply empty
    refine close ?_
    sol_symex
    sol_close

/-- `⟨ uint to = 9; ok = to.send(5); ⟩ true`: under the diamond the amount's
sign first (`"non-negative amount"`), then the two outcomes.  The receiver is
bound: a booking at a local that holds nothing is stuck, and the diamond
fails on it. -/
theorem sendDiamond : ⊢ dl!{ ⟨ uint to = 9; ok = to.send(5); ⟩ true } := by
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply cases .sendNoCallbackDiamond
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    show sequent!{ { to := 9 } ⟹ 0 <= 5 }
    refine close ?_
    sol_symex
    sol_close
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  refine ⟨?_, ?_⟩
  · show sequent!{ { to := 9 },
        { net := if(to = this) then net else store(net, at(to), net(to) - 5) ‖ ok := true }
        ⟹ ⟨ ⟩ true }
    apply empty
    refine close ?_
    sol_symex
    sol_close
  · show sequent!{ { to := 9 }, { ok := false } ⟹ ⟨ ⟩ true }
    apply empty
    refine close ?_
    sol_symex
    sol_close

/-- `[ ok = owner.send(x + 2); ] true`: a storage receiver and an amount
that is not simple, both captured first (`send_unfold_leftFstReceiver`,
`send_unfold_rightSndArgument`). -/
theorem sendCapturedValid : ⊨ dl!{ [ ok = owner.send(x + 2); ] true } := by
  sol_symex
  sol_close

/--
info: @Taclet.send_unfold_leftFstReceiver : ∀ {C : Contract} {k : Nat} {m : Modality} {pv : Var} {nadr e : Val C PrimTy.uint},
  dl{ ⟨[ pv = nadr .send(e); ]⟩ ⇝ ⟨[ uint se = nadr; pv = se .send(e); ]⟩ }
-/
#guard_msgs in #check @Taclet.send_unfold_leftFstReceiver

/--
info: @Taclet.send_unfold_rightSndArgument : ∀ {C : Contract} {k : Nat} {m : Modality} {pv : Var}
  {sadr : Simple C PrimTy.uint} {nse : Val C PrimTy.uint},
  dl{ ⟨[ pv = sadr .send(nse); ]⟩ ⇝ ⟨[ uint se = nse; pv = sadr .send(se); ]⟩ }
-/
#guard_msgs in #check @Taclet.send_unfold_rightSndArgument

end Solidity.Examples.Tactics.Payment
