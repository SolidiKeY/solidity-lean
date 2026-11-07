

<!-- Preserved V10 routine obligations; none is marked discharged by this merge. -->

# C157 captured-write adapter — completed

Module: `Solidity/Lowering/StorageOps/SourceWordCommutation.lean`.
Lemma: `Solidity.Lowering.StorageOps.SourceWordCommutation.complete`.
Why routine: combine checked `run` in both orders, `world_commute`, and
`journal_order` in both orders; no new soundness argument or premise.

The exact statement below is now compiled as `SourceWordCommutation.complete`
and used by the existing populated world-equality control. Every premise and
exact journal snapshot is retained.
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

The historical twelve adapters remain in the preserved original checkout and prior handoffs; they are not resubmitted here. C157 is closed; the other historical adapters remain open.

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

## C172: nonempty nested capture outer wrapper

Module: `Solidity.Lowering.StorageOps.SourceNestedByteValues`.
Lemma: `copy_timeout_prefix`.
Why routine: unfold the two existing outer storRef/loadMem binds and apply
checked `timeout_prefix` at start0. Keep the exact heap payloads and order;
add no writable/destination premise. Common inner length is a parameter of
this component theorem, not an admitted-source restriction. Proposition type
only; no compiled theorem, assumption or stub.

```lean
theorem copy_timeout_prefix :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (src dst : Solidity.Source.SPath) (_different : src≠dst)
 (count length : Nat) (payload : Nat → Nat → UInt8)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_outerHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok (count+1),(locals,state)))
 (_headers : ∀ j<count+1,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (src.go (.index j))).run (locals,state)=(.ok length,(locals,state)))
 (_reads : ∀ j<count+1,∀ k<length,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame ((src.go (.index j)).go (.index k)) (.fixedBytes 1 (by decide))).run (locals,state)=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload j k] rfl),(locals,state))),
 (Solidity.Source.storeVal (E:=E) (Γ:=Γ) frame (count+length+5) (.array .storage (.bytes .storage) none) dst
  (Solidity.Source.Val.storRef (τ:=.array .storage (.bytes .storage) none) rfl src)).run (locals,state)=
 (.error .timeout,(locals,(List.range' 0 count).foldl
  (Solidity.Lowering.StorageOps.SourceNestedByteValues.allocateAt length payload) state))
```

One adapter added to prior nineteen: twenty remain pending.

## C173: varying-length outer capture wrapper

Module: `Solidity.Lowering.StorageOps.SourceVaryingByteCapture`.
Lemma: `copy_timeout_prefix`.
Why routine: unfold the existing outer capture binds and apply the checked
runtime prefix theorem at start0. Preserve both fuel inequalities and the exact
heap payloads; add no destination/writable premise. This is a type-checked
proposition only, not a compiled theorem or assumption.

```lean
theorem copy_timeout_prefix :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (src dst : Solidity.Source.SPath) (_different : src≠dst)
 (count budget : Nat) (length : Nat → Nat) (payload : Nat → Nat → UInt8)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_enough : ∀ j<count,length j<count+budget-j) (_short : budget≤length count)
 (_outerHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok (count+1),(locals,state)))
 (_headers : ∀ j<count+1,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (src.go (.index j))).run (locals,state)=
  (.ok (length j),(locals,state)))
 (_reads : ∀ j<count+1,∀ k<length j,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame ((src.go (.index j)).go (.index k)) (.fixedBytes 1 (by decide))).run (locals,state)=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload j k] rfl),(locals,state))),
 (Solidity.Source.storeVal (E:=E) (Γ:=Γ) frame (count+budget+5) (.array .storage (.bytes .storage) none) dst
  (Solidity.Source.Val.storRef (τ:=.array .storage (.bytes .storage) none) rfl src)).run (locals,state)=
 (.error .timeout,(locals,(List.range' 0 count).foldl
  (fun state j=>Solidity.Lowering.StorageOps.SourceNestedByteValues.allocateAt (length j) payload state j) state))
```

One added to prior twenty: twenty-one adapters remain pending.

## C174: successful outer snapshot wrapper

Module: `Solidity.Lowering.StorageOps.SourceByteCaptureSuccess`.
Lemma: `snapshot_all`.
Why routine: unfold one actual array loadMem/header bind and apply checked
`capture_all` at start0, preserving both returned typed references and heap
payloads. Proposition type only; no theorem, assumption or stub registered.

```lean
theorem snapshot_all :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath) (count budget : Nat)
 (length : Nat → Nat) (payload : Nat → Nat → UInt8)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_enough : ∀ j<count,length j<count+budget-j)
 (_outerHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame path).run (locals,state)=(.ok count,(locals,state)))
 (_headers : ∀ j<count,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (path.go (.index j))).run (locals,state)=
  (.ok (length j),(locals,state)))
 (_reads : ∀ j<count,∀ k<length j,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame ((path.go (.index j)).go (.index k)) (.fixedBytes 1 (by decide))).run (locals,state)=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload j k] rfl),(locals,state))),
 (Solidity.Source.loadMem (E:=E) (Γ:=Γ) frame (count+budget+4) (.array .memory (.bytes .memory) none) path).run (locals,state)=
 (.ok (Solidity.Source.Data.array (l:=.memory) (τ:=.bytes .memory) (n:=none) count (fun _ h=>nomatch h)
  (fun j : Fin count=>Solidity.Source.Data.val (Solidity.Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (state.heap.next+j.val)))),
  (locals,(List.range' 0 count).foldl
  (fun state j=>Solidity.Lowering.StorageOps.SourceNestedByteValues.allocateAt (length j) payload state j) state))
```

One added to prior twenty-one: twenty-two adapters remain pending.

## C179: OLD-header commit wrapper

Module: `Solidity.Lowering.StorageOps.SourceByteCommitFrames`.
Lemma: `commit_from_old_headers`.
Why routine: apply the already checked `SourceCapturedByteCommit.commit_all`;
for each header premise apply `prefix_header`, then rewrite its OLD read with
`headersOld`. Keep all existing captured-object/type/fuel/cleanup premises.
Place the wrapper in this module to avoid an import cycle. The proposition below
is type-checked only; it is no compiled theorem, axiom, assumption or instance.

```lean
theorem commit_from_old_headers : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (_writable : frame.static=false) (dst : Solidity.Source.SPath)
 (typed : ∀ i j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy ((dst.go (.index i)).go (.index j)))
 (headerTyped : ∀ i, (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy (dst.go (.index i)))
 (payload : Nat → List UInt8) (oldLength : Nat → Nat) (start count budget first : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_captured : ∀ j<count,state.heap.get (first+j)=some ⟨.bytes .memory,Solidity.Source.Data.bytes (payload (start+j))⟩)
 (_enough : ∀ j<count,(payload (start+j)).length≤count+budget-j)
 (_cleanup : ∀ j<count,oldLength (start+j)-(payload (start+j)).length≤count+budget-j)
 (_headersOld : ∀ j<count,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (dst.go (.index (start+j)))).run
 (locals,state)=(.ok (oldLength (start+j)),(locals,state))),
 (Solidity.Source.storeElems (E:=E) (Γ:=Γ) frame (count+budget+5) (.bytes .storage) dst start count
  (fun j : Fin count=>Solidity.Source.Data.val (Solidity.Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (first+j.val)))).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.run (Solidity.Lowering.StorageOps.SourceCapturedByteCommit.plans frame dst typed headerTyped payload oldLength budget start count).flatten}))
```

One routine adapter added; twenty-three remain pending.

## C180: explicit rollback of the failed commit phase

Module: `Solidity.Lowering.StorageOps.SourceCapturedByteTimeout`.
Lemma: `rollback_cleanup_timeout`.
Why routine: rewrite the checked `cleanup_timeout` outcome, expand the existing
`rollbackTo` and apply `ExecState.journal_run`/`undoN_run`. Commit changes only
`ex`, so heap equality follows from unchanged heap, not from restoration of the
mark's heap field. This concerns the pre-COMMIT state with snapshots already
captured, not a pre-capture caller state or physical target rollback.
Type-checked proposition only; no compiled theorem, axiom or instance.

```lean
theorem rollback_cleanup_timeout : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (_writable : frame.static=false) (dst : Solidity.Source.SPath)
 (typed : ∀ i j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy ((dst.go (.index i)).go (.index j)))
 (headerTyped : ∀ i, (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy (dst.go (.index i)))
 (payload : Nat → List UInt8) (oldLength : Nat → Nat) (start count budget first : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_captured : ∀ j<count+1,state.heap.get (first+j)=some ⟨.bytes .memory,Solidity.Source.Data.bytes (payload (start+j))⟩)
 (_enough : ∀ j<count+1,(payload (start+j)).length≤count+1+budget-j)
 (_cleanup : ∀ j<count,oldLength (start+j)-(payload (start+j)).length≤count+1+budget-j)
 (_short : budget+1<oldLength (start+count)-(payload (start+count)).length)
 (_headers : ∀ j<count+1,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (dst.go (.index (start+j)))).run (locals,state)=
  (.ok (oldLength (start+j)),(locals,state))),
 let outcome :=  (Solidity.Source.storeElems (E:=E) (Γ:=Γ) frame (count+budget+6) (.bytes .storage) dst start (count+1)
  (fun j : Fin (count+1)=>Solidity.Source.Data.val (Solidity.Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (first+j.val)))).run (locals,state)
 (Solidity.Source.rollbackTo (state.ex.journal.length,state.logs.length,state.heap) : Solidity.Source.EM E Γ Unit).run outcome.2=
 (.ok (),(locals,state))
```

One routine adapter added; twenty-four remain pending.
<!-- Preserved lane snapshot below; pending/history only, not proof evidence. -->
<!-- Preserved V17 lane pending statements; not proof evidence. -->
# Routine G19 slot projection (draft statement only)
Module: Solidity.Lowering.G19.AssignmentReturnFlag. boolSlot is a projection
from the actual V07 ContextMap, never an independently chosen target index.
The Source semantic proof and concrete mixed controls stay with Sol.
theorem boolSlot_spec {srcΓ : Source.RCtx} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (i : Source.Idx srcΓ .bool)
    (h : (m.slot i).1 = .val .bool) :
    m.slot i = ⟨.val .bool, boolSlot m i h⟩
Why routine: dependent-pair projection/cast equality, no run/profile/world or
preservation claim. No placeholder proof exists. Standard automation attempts
are retained; retry after introducing binders, then pair/equality cases if
needed. Keep only the winning proof. After checking, a wrapper may discharge
correct's map_i/map_a; do not count this universal obligation closed beforehand.
Concrete controls close both by rfl. Do not edit V07 or reserved Source modules.
## Conditional statement scalar observation corollary
Module: Solidity/Lowering/G19/ConditionalStatementControls.lean
Lemma: scalar_observation_agrees. Why routine: rewrite the two already proved
source_observation/target_observation endpoints; no new soundness argument.
Use existing module opens and preserve both pipeline/choice parameters.
theorem scalar_observation_agrees (pipeline : Roadmap.Pipeline) (choice : Bool) :
    sourceObs pipeline choice = observeTarget (code tci tca ti ta tj tb) choice
Draft statement only, not a compiled declaration or completed coverage row.
Do not change either observation list, expected result or producer interface.
## Conditional sequence scalar observation corollary
Module: Solidity/Lowering/G19/ConditionalSequenceControls.lean
Lemma: scalar_observation_agrees. Routine: rewrite the existing
source_observation and target_observation endpoints, preserving every field.
theorem scalar_observation_agrees (pipeline : Roadmap.Pipeline) (choice : Bool) :
    sourceObs pipeline choice = observeTarget (code tci tca ti ta tj tb tb ti) choice
Draft only; no placeholder declaration or completed coverage claim.
Soundness, generic reached-context proof and negative controls stay with Sol.
## Return-tail scalar observation corollary
Module: Solidity/Lowering/G19/ReturnTailControls.lean
Lemma: scalar_observation_agrees. Routine: rewrite the two existing complete
scalar observation endpoints; preserve the outcome/selector and every caller field.
theorem scalar_observation_agrees (pipeline : Roadmap.Pipeline) (choice : Bool) :
    sourceObs pipeline choice = observeTarget (code tci tca ti ta) choice
Draft only; no placeholder declaration or completed coverage claim.
Soundness, captured-selector proof and alias negatives stay with Sol.
## Immediate-return while false selector
Module: Solidity/Lowering/G19/WhileReturnControls.lean
Lemma: captured_false. Routine: map the already proved no target endpoint,
then reduce the fresh Boolean head. Preserve the complete target outcome.
theorem captured_false :
    ((AssignmentReturnFlag.code P.mapping (.there .here) .here rfl rfl : Prog P.C _ _).run P.target).map
      (fun out => TEnv.get .here out.st.env) = .ok false
Draft only; no placeholder declaration or completed coverage claim.
The Source loop proof and mapped transport stay with Sol.
## Mapped condition false-branch adapter
Module: Solidity/Backend/StructuredFlow/MappedBranch.lean (new, not created).
Lemma: false_run. Routine: append the fresh-cell load to the checked emitter,
combine run_append_ok/run_exact/upd_same with entry.vals and the initial false
read, then apply the published Branch.false_run. The true arm's exact pending
skip and complete compiler integration remain with Sol.
namespace Solidity.Backend.StructuredFlow.MappedBranch
open Solidity.Evm Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag
def condition {srcΓ : Source.RCtx} {Γ : Ctx} (b : Nat) (m : ContextMap srcΓ Γ)
    (i a : Source.Idx srcΓ .bool) (hi : (m.slot i).1 = .val .bool)
    (ha : (m.slot a).1 = .val .bool) : List Instr :=
  MappedCondition.emit b m i a hi ha ++ [.mload (cell (b + Γ.length))]
theorem false_run {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    {L b : Nat} {F : Frag Γ} {caller : State C Γ} {machine : Machine}
    (m : ContextMap srcΓ Γ) (i a : Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool)
    (entry : Sim C L b F caller machine)
    (read : TEnv.get (boolSlot m a ha) caller.env = false) (left right : List Instr) :
    run (Branch.emit (condition b m i a hi ha) left right) machine =
      run right (MappedCondition.after b m i a hi ha machine)
end Solidity.Backend.StructuredFlow.MappedBranch
Draft statement only, not elaborated or counted as proof evidence. Import the
published BranchSelector and the new checked MappedCondition; do not define a
new representation or assume the condition's run.
## MappedBranch interface now implemented
The previously drafted Solidity/Backend/StructuredFlow/MappedBranch.lean
condition signature is now implemented unchanged. code_exact, condition_run,
condition_represented, true_run, true_pending_skip, admitted and correct are
proved by Sol with inhabited compiler/exit controls. The earlier false_run
statement remains the routine Terra item, unimplemented and not counted as
proof evidence. Use condition_represented plus the initial false-read fact and
published Branch.false_run; do not copy condition into a parallel module.
The prior draft is preserved verbatim as historical handoff context.
## ConditionalSourceCompiler source field projection
- Module: Solidity/Backend/StructuredFlow/ConditionalSourceCompilerControls.lean
- Lemma: source_fields (draft below, unimplemented and not evidence).
- Routine: rewrite joined.1, split flag, reduce the three local reads. Do not change joined or any premise. Keep MappedBranch.false_run with its existing Terra owner.
namespace Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls
open Solidity.Lowering.G19
open Source.SemanticsExamples (G0 F0)
theorem source_fields (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (match (Source.execS (G0 pipeline) F0 (fuel+4) 0 none (R := []) (M := false)
      (ConditionalStatement.statement (k := ⟨false,false⟩) sci sca sci .here sca sci)
      (source flag).1).run (.nil,(source flag).2) with
    | (.ok (.normal ls),_) => [(ls.get sca).key,(ls.get sci).key,(ls.get .here).key]
    | _ => []) = [some (if flag then 1 else 0),some 0,some 0]
end Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls
## ConditionalSequenceCompiler Source field projection
- Module: Solidity/Backend/StructuredFlow/ConditionalSequenceCompilerControls.lean
- Lemma: source_sequence_fields (draft only, unimplemented and not proof evidence).
- Routine: rewrite joined.1, split flag and reduce all three reached local reads. Keep the Source/typed/EVM statements and13 premises unchanged; the hard composition is already proved. Do not duplicate the older prefix source_fields or MappedBranch.false_run items.
namespace Solidity.Backend.StructuredFlow.ConditionalSequenceCompiler.Controls
open Solidity.Lowering.G19
open Source.SemanticsExamples (G0 F0)
open ConditionalSourceCompiler.Controls (source sci sca)
theorem source_sequence_fields (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (match (Source.execS (G0 pipeline) F0 (fuel+6) 0 none (R := []) (M := false)
      (ConditionalSequence.statement (k := ⟨false,false⟩) sci sca sci .here sca sci sca sci)
      (source flag).1).run (.nil,(source flag).2) with
    | (.ok (.normal ls),_) => [(ls.get sca).key,(ls.get sci).key,(ls.get .here).key]
    | _ => []) = [some 0,some 0,some 0]
end Solidity.Backend.StructuredFlow.ConditionalSequenceCompiler.Controls
## WhileContinueCompiler routine fragment closure (not proved)
Module: `Solidity/Backend/StructuredFlow/WhileContinueCompiler.lean`.
Lemma: `all_readable`. Routine finite fragment/list bookkeeping for the existing primitive-only reset body; use existing Frag/inFragP definitions. This statement is a draft only, has not been compiled, and does not discharge correct.checked. Do not change the checker or infer a primitive-local refusal from alias flags.
theorem all_readable {srcΓ : Solidity.Source.RCtx} {C : Solidity.Contract} {Γ : Solidity.Ctx}
    (m : Solidity.Lowering.V07.ContextMap srcΓ Γ) (i a : Solidity.Source.Idx srcΓ .bool)
    (hi : (m.slot i).1 = .val .bool) (ha : (m.slot a).1 = .val .bool) :
    Solidity.Evm.inFragP (Solidity.Evm.Frag.init Γ)
      (Solidity.Lowering.G19.AssignmentWhileReset.code (C := C) m i a hi ha) =
      some (Solidity.Evm.Frag.init Γ)
