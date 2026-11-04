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

## C159 routine captured failure adapter

Module: `Solidity/Lowering/StorageOps/SourceWriteRollback.lean`.
Lemma: `Solidity.Lowering.StorageOps.SourceWriteRollback.run_refused`.
Why routine: unfold the existing pair, use checked `SourceWordWrite.source_write`
for the first operation and `static_write` for the second through `Hoare.run_bind`.
The producer arguments and actual complete controls are checked separately.
This statement is uncompiled; no stub, admission or implicit rollback claim.

```lean
namespace Solidity.Lowering.StorageOps.SourceWriteRollback
theorem run_refused {E : Source.Env} {Γ : Source.RCtx}
    (writer rejector : Source.Fr) (p : Source.SPath)
    (v : Source.Val E.layout (E.cellTy p)) (q : Source.SPath)
    (w : Source.Val E.layout (E.cellTy q))
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (writable : writer.static=false) (ordinary : E.transientRoot p=false)
    (static : rejector.static=true) :
    (refusedAfter writer rejector p v q w : Source.EM E Γ Unit).run (locals,state)=
      (.error (.revert []),(locals,SourceWordWrite.after writer p v state))
end Solidity.Lowering.StorageOps.SourceWriteRollback
```

Two routine adapters are specified here; the historical twelve remain preserved
separately, for fourteen pending adapters total. Neither statement is compiled.

## C166: complete primitive-copy fuel classification

Proposed owned module name: `Solidity.Lowering.StorageOps.SourceStorageCopyPhases`
(no file or root import registered).
Lemma: `Solidity.Lowering.StorageOps.SourceStorageCopyPhases.all_fuel`.
Why routine: case analysis on fuel versus count+2/count+3, then instantiate the
checked `SourceStorageCopyBarrier.copy_timeout`, `SourceStorageCopyPayload.copy_prefix`,
`SourceStorageCopyEmpty.copy_empty` or `SourceStorageCopyPrefix.prepared`; the
remaining work is natural-number substitution and zero-length log normalization.
This is an uncompiled statement, not a stub or an assumed future theorem.
The hard phase producers and nontrivial complete controls are checked separately.

```lean
namespace Solidity.Lowering.StorageOps.SourceStorageCopyPhases
theorem all_fuel :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (_writable : frame.static=false) (t : Solidity.Source.IntTy)
 (src dst : Solidity.Source.SPath) (_different : src≠dst) (fuel count oldLength : Nat)
 (payload : Nat → Solidity.Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_sourceHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok count,(locals,state)))
 (_reads : ∀ j<count,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.int t)).run (locals,state)=(.ok (payload j),(locals,state)))
 (_targetHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state))),
 let trace := Solidity.Backend.StorageOps.SourceStorageCopy.copyLog frame t dst count oldLength payload typed
 let written := Solidity.Backend.StorageOps.SourceStorageCopy.writes frame t dst payload
   (fun j => (Solidity.Backend.StorageOps.SourceStorageCopy.element_type t dst typed j).symm) 0 (count-1)
 (Solidity.Source.storeVal (E:=E) (Γ:=Γ) frame fuel (.array .storage (.int t) none) dst
   (Solidity.Source.Val.storRef (τ:=.array .storage (.int t) none) rfl src)).run (locals,state)=
 if fuel≤count+2 then (.error .timeout,(locals,state))
 else if fuel=count+3 then
   if count=0 then
     if oldLength=0 then (.ok (),(locals,{state with ex:=state.ex.run trace}))
     else (.error .timeout,(locals,state))
   else (.error .timeout,(locals,{state with ex:=state.ex.run written}))
 else if oldLength-count≤fuel-3 then (.ok (),(locals,{state with ex:=state.ex.run trace}))
 else (.error .timeout,(locals,{state with ex:=state.ex.run (trace.take (count+min (oldLength-count) (fuel-3)))}))
end Solidity.Lowering.StorageOps.SourceStorageCopyPhases
```

The prior subtotal was fourteen pending adapters; this statement makes fifteen.
No `all_fuel` theorem is registered or claimed proved.

## C169: byte capture-to-prepared-copy adapter

Module: `Solidity.Lowering.StorageOps.SourceByteStorageCapture` (not created).
Lemma: `prepared_copy`.
Why routine: unfold actual storRef capture once, use checked `load_bytes`
with OLD header/read premises, then `store_prepared`; rewrite list length.
The operation producers and their soundness proofs are already checked. No
new assumption about emitted target code or desired preservation is permitted.
This statement is type-validated only; no theorem/stub is registered.

```lean
theorem prepared_copy :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (_writable : frame.static=false)
 (src dst : Solidity.Source.SPath) (_different : src≠dst)
 (count oldLength padding : Nat) (payload : Nat → UInt8)
 (typed : ∀ j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy (dst.go (.index j)))
 (headerTyped : (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy dst)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_sourceHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok count,(locals,state)))
 (_reads : ∀ j<count,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.fixedBytes 1 (by decide))).run (locals,state)=
   (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload j] rfl),(locals,state)))
 (_targetHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state))),
 let bs := (List.range' 0 count).map payload
 (Solidity.Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+3) (.bytes .storage) dst
   (Solidity.Source.Val.storRef (τ:=.bytes .storage) rfl src)).run (locals,state)=
 (if oldLength-count≤count+padding then .ok () else .error .timeout,
  (locals,{state with ex:=state.ex.run (Solidity.Lowering.StorageOps.SourceByteStoragePrepared.phaseLog frame dst typed headerTyped bs oldLength padding)}))
```

This adds one routine adapter to the prior fifteen: sixteen remain pending.
The statement does not discharge generic storRef composition.

## C170: byte-capture barrier adapters

Module: `Solidity.Lowering.StorageOps.SourceByteStorageBarrier`.
Lemmas: `memory_timeout`, `copy_timeout`.
Why routine: unfold the existing loadMem/header bind once and apply the checked
`load_timeout`; unfold the distinct-path storRef bind once and apply that
memory adapter. No writable/destination/header/type hypothesis may be added.
The OLD valid-source read premises are material; malformed sources can fail
earlier. These proposition types are checked only, not proved or registered.

```lean
theorem memory_timeout :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath)
 (fuel count : Nat) (payload : Nat → UInt8)
 (initial : Solidity.Source.Locals E.layout Γ × Solidity.Source.St E)
 (_short : fuel≤count+1)
 (_header : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame path).run initial=(.ok count,initial))
 (_reads : ∀ j<count,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame (path.go (.index j)) (.fixedBytes 1 (by decide))).run initial=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload j] rfl),initial)),
 (Solidity.Source.loadMem (E:=E) (Γ:=Γ) frame fuel (.bytes .memory) path).run initial=(.error .timeout,initial)

theorem copy_timeout :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (src dst : Solidity.Source.SPath)
 (fuel count : Nat) (payload : Nat → UInt8)
 (initial : Solidity.Source.Locals E.layout Γ × Solidity.Source.St E)
 (_different : src≠dst) (_short : fuel≤count+2)
 (_header : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame src).run initial=(.ok count,initial))
 (_reads : ∀ j<count,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.fixedBytes 1 (by decide))).run initial=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload j] rfl),initial)),
 (Solidity.Source.storeVal (E:=E) (Γ:=Γ) frame fuel (.bytes .storage) dst
   (Solidity.Source.Val.storRef (τ:=.bytes .storage) rfl src)).run initial=(.error .timeout,initial)
```

Two adapters added to the prior sixteen: eighteen remain pending.

## C171: nested allocating-capture wrapper

Module: `Solidity.Lowering.StorageOps.SourceNestedByteCapture`.
Lemma: `copy_timeout_prefix`.
Why routine: unfold actual storRef/loadMem outer capture, use OLD outer header,
then apply checked `timeout_prefix` at start0. The existing producer proves the
allocation prefix; do not assume full-state preservation or erase its heap.
No destination or writable-frame premise is required. Proposition type only;
no theorem/stub registered.

```lean
theorem copy_timeout_prefix :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (src dst : Solidity.Source.SPath) (_different : src≠dst)
 (count : Nat) (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_outerHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok (count+1),(locals,state)))
 (_headers : ∀ j<count+1,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (src.go (.index j))).run (locals,state)=(.ok 0,(locals,state))),
 (Solidity.Source.storeVal (E:=E) (Γ:=Γ) frame (count+5) (.array .storage (.bytes .storage) none) dst
   (Solidity.Source.Val.storRef (τ:=.array .storage (.bytes .storage) none) rfl src)).run (locals,state)=
 (.error .timeout,(locals,Nat.repeatTR Solidity.Lowering.StorageOps.SourceNestedByteCapture.captureStep count state))
```

One adapter added to the prior eighteen: nineteen remain pending.
