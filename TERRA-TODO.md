# C157 routine adapter

Module: `Solidity/Lowering/StorageOps/SourceWordCommutation.lean`.
Lemma: `Solidity.Lowering.StorageOps.SourceWordCommutation.complete`.
Why routine: combine checked `run` in both orders, `world_commute`, and
`journal_order` in both orders; no new soundness argument or premise.

The statement elaborated in the failed automation scratch. It is NOT a compiled
Lean declaration or a closed proof. Keep every premise and exact journal snapshot.
Do not claim full Source states/journals commute, fresh lvalue compilation,
whole compiler or implicit rollback. No admission is permitted.

```lean
namespace Solidity.Lowering.StorageOps.SourceWordCommutation
theorem complete {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
 (p : Source.SPath) (v : Source.Val E.layout (E.cellTy p))
 (q : Source.SPath) (w : Source.Val E.layout (E.cellTy q))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (writable : frame.static=false) (ordinaryP : E.transientRoot p=false) (ordinaryQ : E.transientRoot q=false)
 (different : p≠q) :
 let forward := (two frame p v q w).run (locals,state)
 let reverse := (two frame q w p v).run (locals,state)
 forward=(.ok (), (locals,SourceWordWrite.after frame q w (SourceWordWrite.after frame p v state))) ∧
 reverse=(.ok (), (locals,SourceWordWrite.after frame p v (SourceWordWrite.after frame q w state))) ∧
 forward.2.2.ex.world=reverse.2.2.ex.world ∧
 forward.2.2.ex.journal =
 .account frame.this ((SourceWordWrite.after frame p v state).ex.world.accounts frame.this) ::
 .account frame.this (state.ex.world.accounts frame.this) :: state.ex.journal ∧
 reverse.2.2.ex.journal =
 .account frame.this ((SourceWordWrite.after frame q w state).ex.world.accounts frame.this) ::
 .account frame.this (state.ex.world.accounts frame.this) :: state.ex.journal
end Solidity.Lowering.StorageOps.SourceWordCommutation
```

The historical twelve adapters remain in the preserved original checkout and prior handoffs; they are not resubmitted here. This adds one pending routine adapter.
