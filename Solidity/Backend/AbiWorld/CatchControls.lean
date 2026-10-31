import Solidity.Backend.AbiWorld.CatchTransport

/-! Inhabited intrinsic executions for catch transport. These are packet-specialized
controls of published semantics, not target ABI or arbitrary-world compilation. -/
namespace Solidity.Backend.AbiWorld.CatchControls
open CatchTransport PublishedLayout

private def contract : Contract := { vars := [] }
private abbrev Γ : Ctx := [.val .uint, .val .uint, .mem bytesR, .mem bytesR]
private def initial : State contract [] :=
  { State.init contract with tx := { selfAddress := ⟨7, by decide +kernel⟩ } }
private def older := initial.allocPush (bytesObj initial.H [0xa1, 0xb2] (by decide +kernel))
/-- Two aliases of an older allocation, a preserved marker, and a result slot. -/
private def caller : State contract Γ :=
  ((older.push (t := .mem bytesR) (TEnv.get .here older.env)).push
    (t := .val .uint) ⟨77, by decide +kernel⟩).push
    (t := .val .uint) ⟨0, by decide +kernel⟩
private def call (addr : Nat := 7) (h : addr < 2 ^ 256 := by decide +kernel) :
    ExtCall contract Γ := ⟨.lit addr (PrimTy.inRange_uint_of_lt h), "callee", []⟩
private def callee (d : List UInt8) : Prog contract [] [] :=
  .cons (.revertData [.bytes d]) .nil
private def unpadded : List UInt8 :=
  Semantics.errorSelector ++ Semantics.wordBytes 32 ++ Semantics.wordBytes 3 ++ [0x42, 0, 0xfe]
private def truncated : List UInt8 :=
  Semantics.errorSelector ++ Semantics.wordBytes 32 ++ Semantics.wordBytes 3 ++ [0x42, 0]
private def custom : List UInt8 := [0xde, 0xad, 0xbe, 0xef, 0, 0xff]

/-- A genuine typed callee executes through `Prog.runR` and `TRun.call`. -/
theorem actual_reverting_call (d : List UInt8) :
    TRun.call (Args.nil : Args contract Γ []) (.rets .nil) (callee d).ext
      (callee d).runR caller = .error (THalt.ofData d) := by
  simp only [TRun.call, callee, Prog.runR, TRun.seq, TRun.revertData, RevPart.evalT,
    List.mapM_cons, List.mapM_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    Args.evalT, bind, Except.bind, pure, Except.pure]

/-- No abstract halt premise remains: arbitrary literal packets are extracted
from a real typed callee in the inhabited nonempty caller frame. -/
theorem extracted_actual (d : List UInt8) :
    TRun.catchBytes (call 7) .nil .nil (callee d).ext (callee d).runR true caller = .ok d :=
  TRun.catchBytes_self_data (call 7) .nil .nil (callee d).ext (callee d).runR caller d
    (by decide +kernel) rfl (actual_reverting_call d)

private def branch (n : Nat) (hn : n < 2 ^ 256) :
    Prog contract Γ (.val .bool :: Γ) :=
  .cons (.assignLocal .here (.simple (.lit n (PrimTy.inRange_uint_of_lt hn))))
    (.cons (.declLocal .bool (.user "clauseLocal") (some (.simple (.bool true)))) .nil)
private def panicBranch : Prog contract (.val .uint :: Γ)
    (.val .bool :: .val .uint :: Γ) :=
  .cons (.assignLocal (.there .here) (.simple (.local .here)))
    (.cons (.declLocal .bool (.user "clauseLocal") (some (.simple (.bool true)))) .nil)
private def attempt (body : Prog contract [] []) (addr : Nat := 7)
    (h : addr < 2 ^ 256 := by decide +kernel) : Stmt contract Γ Γ :=
  .tryCall (call addr h) .nil (branch 10 (by decide +kernel))
    (branch 20 (by decide +kernel)) (.some (.user "panicCode")) panicBranch
    (branch 30 (by decide +kernel)) .nil body true
private def locals (σ : State contract Γ) : Nat × Nat × Nat :=
  ((TEnv.get .here σ.env).val.toNat,
   (TEnv.get (.there .here) σ.env).val.toNat, σ.H.length)

/-- Error, Panic, custom, bare and successful calls choose distinct real clauses.
The Panic binder is copied before its own slot and the clause local are popped. -/
theorem classified_execution :
    ((attempt (callee (Source.errorData [0x42]))).runR caller).map (fun o => locals o.st) = .ok (20, 77, 1) ∧
    ((attempt (callee (Source.panicData .alloc))).runR caller).map (fun o => locals o.st) = .ok (65, 77, 1) ∧
    ((attempt (callee custom)).runR caller).map (fun o => locals o.st) = .ok (30, 77, 1) ∧
    ((attempt (callee [])).runR caller).map (fun o => locals o.st) = .ok (30, 77, 1) ∧
    ((attempt .nil).runR caller).map (fun o => locals o.st) = .ok (10, 77, 1) := by with_unfolding_all exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Noncanonical accepted Error data is not narrowed to padded canonical packets;
a truncated reason goes through the actual catch-all, not the Error clause. -/
theorem noncanonical_classification :
    ((attempt (callee unpadded)).runR caller).map (fun o => locals o.st) = .ok (20, 77, 1) ∧
    ((attempt (callee truncated)).runR caller).map (fun o => locals o.st) = .ok (30, 77, 1) := by with_unfolding_all exact ⟨rfl, rfl⟩

private def inspectBytes : Prog contract (.mem bytesR :: Γ)
    (.val .bool :: .mem bytesR :: Γ) :=
  .cons (.assignLocal (.there .here) (.readMem (litLoc 0 (by decide +kernel))))
    (.cons (.declLocal .bool (.user "clauseLocal") (some (.simple (.bool true)))) .nil)
private def rethrow : Prog contract (.mem bytesR :: Γ) (.mem bytesR :: Γ) :=
  .cons (.revertData [.mem .raw .here]) .nil
private def caught (d : List UInt8) (kind : CatchKind) : Stmt contract Γ Γ :=
  .catchData (call 7) .nil .nil (callee d) true kind (.user "caught") inspectBytes
private def thrown (d : List UInt8) (kind : CatchKind) : Stmt contract Γ Γ :=
  .catchData (call 7) .nil .nil (callee d) true kind (.user "caught") rethrow
private def aliases (σ : State contract Γ) : List (Nat × List Nat) :=
  ([TEnv.get (.there (.there .here)) σ.env,
   TEnv.get (.there (.there (.there .here))) σ.env] : List (Option (HRef σ.H bytesR))).filterMap
    (fun r => r.map (fun (r : HRef σ.H bytesR) =>
      (r.id, (σ.heap.get r : MObj σ.H bytesR).1.map (fun b => b.val.toNat))))

private theorem allocated_observe (d bs : List UInt8) (kind : CatchKind)
    (hd : kind.decode d = some bs) :
    ((caught d kind).runR caller).map (fun o => (locals o.st, aliases o.st)) =
      (inspectBytes.runR (caller.allocPush (bytesObj caller.H bs (kind.decode_lt hd)))).map
        (fun o => (locals (o.st.drop ((Ext.push .refl).trans inspectBytes.ext)),
          aliases (o.st.drop ((Ext.push .refl).trans inspectBytes.ext)))) := by
  change (TRun.catchData (call 7) .nil .nil (callee d).ext (callee d).runR true kind
    inspectBytes.ext inspectBytes.runR caller).map _ = _
  have hm : ∀ r : TRes (Out contract caller.H Γ),
      r.map (fun o => (locals o.st, aliases o.st)) =
        (r.map (·.st)).map (fun σ => (locals σ, aliases σ)) := by
    intro r; cases r <;> rfl
  rw [hm, catch_allocated (call 7) .nil .nil (callee d) kind inspectBytes caller d bs
    (by decide +kernel) rfl (actual_reverting_call d) hd]
  cases inspectBytes.runR (caller.allocPush (bytesObj caller.H bs (kind.decode_lt hd))) <;> rfl

/-- Source Error agreement feeds actual extraction, decoding, fresh allocation,
byte-reading clause execution and popping. Both older aliases keep their object. -/
theorem allocated_source_error :
    ((caught (Source.errorData [0x42, 0, 0xfe]) .reason).runR caller).map
      (fun o => (locals o.st, aliases o.st)) =
      .ok ((66, 77, 2), [(0, [161, 178]), (0, [161, 178])]) := by
  change (TRun.catchData (call 7) .nil .nil (callee (Source.errorData [0x42, 0, 0xfe])).ext
    (callee (Source.errorData [0x42, 0, 0xfe])).runR true .reason inspectBytes.ext
    inspectBytes.runR caller).map (fun o => (locals o.st, aliases o.st)) = _
  have hm : ∀ r : TRes (Out contract caller.H Γ),
      r.map (fun o => (locals o.st, aliases o.st)) =
        (r.map (·.st)).map (fun σ => (locals σ, aliases σ)) := by
    intro r; cases r <;> rfl
  rw [hm]
  rw [catch_allocated (call 7) .nil .nil (callee (Source.errorData [0x42, 0, 0xfe]))
    .reason inspectBytes caller _ [0x42, 0, 0xfe] (by decide +kernel) rfl
    (actual_reverting_call _) (by rw [source_error_bytes]; exact catch_error _ (by decide +kernel))]
  with_unfolding_all rfl

/-- Exact byte order is observed by an actual clause memory read and rethrow. -/
theorem observed_payloads :
    ((thrown (Source.errorData [0x42, 0, 0xfe]) .reason).runR caller).halt? =
      some (.revertWith [0x42, 0, 0xfe]) ∧
    ((thrown unpadded .reason).runR caller).halt? = some (.revertWith [0x42, 0, 0xfe]) ∧
    ((thrown custom .raw).runR caller).halt? = some (.revertWith custom) ∧
    ((thrown (Source.panicData .alloc) .raw).runR caller).halt? =
      some (.revertWith (Source.panicData .alloc)) := by with_unfolding_all decide +kernel

/-- Validation fails before entering a byte-reading clause; raw catches do not
pretend an unknown custom packet is an Error reason. Empty bytes read out of bounds. -/
theorem catch_refusals :
    ((caught truncated .reason).runR caller).halt? = some .revert ∧
    ((caught custom .reason).runR caller).halt? = some .revert ∧
    ((caught (Source.panicData .alloc) .reason).runR caller).halt? = some .revert ∧
    ((caught [] .raw).runR caller).halt? = some .revert ∧
    (TRun.catchBytes (call 7) .nil .nil Ext.refl (Prog.nil : Prog contract [] []).runR
      true caller).halt? = some .revert := by with_unfolding_all exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Zero receiver refuses before the successful/self branches; a nonself missing
callee refuses. Exhaustion of the real intrinsic assumeFalse body is not a
completed revert; assumeFalse is not Solidity source syntax. -/
theorem call_refusals :
    ((attempt (callee custom) 0).runR caller).halt? = some .revert ∧
    ((attempt (callee custom) 8).runR caller).halt? = some .revert ∧
    ((attempt (.cons .assumeFalse .nil)).runR caller).halt? = some .exhausted ∧
    (TRun.catchBytes (call 7) .nil .nil Ext.refl
      (Prog.cons .assumeFalse .nil : Prog contract [] []).runR true caller).halt? =
      some .exhausted := by with_unfolding_all decide +kernel

/-- The generic branch law is inhabited by the real typed Source-byte callee;
its execution premise is discharged, not left as a simulation assumption. -/
theorem source_error_clause :
    ((attempt (callee (Source.errorData [0x42]))).runR caller).map
      (fun o => locals o.st) = .ok (20, 77, 1) := by
  have h := try_revertWith (call 7) .nil (branch 10 (by decide +kernel))
    (branch 20 (by decide +kernel)) (.some (.user "panicCode")) panicBranch
    (branch 30 (by decide +kernel)) .nil (callee (Source.errorData [0x42]))
    caller (Source.errorData [0x42]) (by decide +kernel) rfl (actual_reverting_call _)
  rw [source_error_bytes, error_roundtrip _ (by decide +kernel)] at h
  exact (congrArg (fun r => r.map (fun o => locals o.st)) h).trans (by rfl)

/-- Source Panic agreement and the actual typed Panic decoder feed the real
named-code clause; the literal callee discharges the call-execution premise. -/
theorem source_panic_clause :
    ((attempt (callee (Source.panicData .alloc))).runR caller).map
      (fun o => locals o.st) = .ok (65, 77, 1) := by
  have he : Semantics.decodeError (Source.panicData .alloc) = none := by decide +kernel
  have hp : Semantics.decodePanic (Source.panicData .alloc) =
      some (⟨65, by decide +kernel⟩ : Semantics.Word) := by
    rw [source_panic_bytes]
    exact panic_roundtrip ⟨65, by decide +kernel⟩
  have h := try_revertWith (call 7) .nil (branch 10 (by decide +kernel))
    (branch 20 (by decide +kernel)) (.some (.user "panicCode")) panicBranch
    (branch 30 (by decide +kernel)) .nil (callee (Source.panicData .alloc))
    caller (Source.panicData .alloc) (by decide +kernel) rfl (actual_reverting_call _)
  rw [he, hp] at h
  exact (congrArg (fun r => r.map (fun o => locals o.st)) h).trans (by rfl)

/-- These actual clauses do not allocate or mutate either older alias. -/
theorem branch_aliases :
    ((attempt (callee (Source.panicData .alloc))).runR caller).map
      (fun o => aliases o.st) = .ok [(0, [161, 178]), (0, [161, 178])] ∧
    ((attempt .nil).runR caller).map (fun o => aliases o.st) =
      .ok [(0, [161, 178]), (0, [161, 178])] := by
  with_unfolding_all exact ⟨rfl, rfl⟩

/-- Raw bytes also allocate successfully; absent padding remains accepted by the
actual reason consumer, with the same preserved caller marker and old aliases. -/
theorem allocated_other_packets :
    ((caught custom .raw).runR caller).map (fun o => (locals o.st, aliases o.st)) =
      .ok ((222, 77, 2), [(0, [161, 178]), (0, [161, 178])]) ∧
    ((caught unpadded .reason).runR caller).map (fun o => (locals o.st, aliases o.st)) =
      .ok ((66, 77, 2), [(0, [161, 178]), (0, [161, 178])]) := by
  constructor
  · rw [allocated_observe custom custom .raw (by decide +kernel)]
    with_unfolding_all rfl
  · rw [allocated_observe unpadded [0x42, 0, 0xfe] .reason (by decide +kernel)]
    with_unfolding_all rfl

/-- Empty raw data is accepted and freshly allocated when the clause does not
read out of bounds; both the data binder and an additional local are popped. -/
theorem empty_allocation :
    ((Stmt.catchData (call 7) .nil .nil (callee []) true .raw (.user "caught")
      (.cons (.declLocal .bool (.user "clauseLocal") (some (.simple (.bool true)))) .nil)).runR
      caller).map (fun o => (locals o.st, aliases o.st)) =
      .ok ((0, 77, 2), [(0, [161, 178]), (0, [161, 178])]) := by
  with_unfolding_all rfl

/-- Intrinsic assertion panic uses the published default code, which is distinct
from the encoded Source allocation Panic code used above. -/
theorem intrinsic_panic_code :
    ((attempt (.cons (.assert (.simple (.bool false))) .nil)).runR caller).map
      (fun o => locals o.st) = .ok (1, 77, 1) := by rfl

/-- Extraction refuses zero/missing/successful calls, before a catch can allocate. -/
theorem extraction_refusals :
    (TRun.catchBytes (call 0) .nil .nil (callee custom).ext (callee custom).runR true caller).halt? =
      some .revert ∧
    (TRun.catchBytes (call 8) .nil .nil (callee custom).ext (callee custom).runR true caller).halt? =
      some .revert ∧
    (TRun.catchBytes (call 7) .nil .nil Ext.refl (Prog.nil : Prog contract [] []).runR
      true caller).halt? = some .revert := by decide +kernel

/-- The existing real-instruction emitter and the executed catch consumer agree
on the same Source packet. This is a byte boundary, not a CALL simulation. -/
theorem emitted_and_consumed :
    let machine : Failure.Slice.Machine := ⟨[], fun _ => 0xee⟩
    Failure.Slice.checkedRun (emitError 31 [0x42, 0, 0xfe]) machine =
      some ({ machine with memory := Failure.Slice.putBytes machine.memory 31 (Source.errorData [0x42, 0, 0xfe]) },
        some (.revert (Source.errorData [0x42, 0, 0xfe]))) ∧
    ((thrown (Source.errorData [0x42, 0, 0xfe]) .reason).runR caller).halt? =
      some (.revertWith [0x42, 0, 0xfe]) := by
  constructor
  · simpa only [List.append_nil] using execute_source_error 31 [0x42, 0, 0xfe] []
      (⟨[], fun _ => 0xee⟩ : Failure.Slice.Machine)
      (by unfold Failure.Fits; decide +kernel) (by decide)
  · exact observed_payloads.1

private def forever : Prog contract [] [] :=
  .cons (.loop .auto (.simple (.bool true)) .nil) .nil

private theorem forever_run (σ : State contract []) :
    forever.runR σ = .error .diverge := by
  have hl : TRun.loop (.simple (.bool true)) Ext.refl
      (Prog.nil : Prog contract [] []).runR σ = .error .diverge := by
    change TLoop.run (fun o : Out contract σ.H [] => .ok o)
      (fun _ => .ok true) _ = _
    have hi : ∀ n (o : Out contract σ.H []),
        TLoop.iterN (fun o => .ok o) (fun _ => .ok true) n o = .inl o := by
      intro n o
      induction n with
      | zero => rfl
      | succ n ih => exact ih
    unfold TLoop.run
    split
    · rename_i h
      obtain ⟨r, n, h⟩ := h
      rw [hi] at h
      cases h
    · rfl
  change TRun.seq (TRun.loop (.simple (.bool true)) Ext.refl
    (Prog.nil : Prog contract [] []).runR) TRun.nil σ = _
  simp only [TRun.seq, hl]

/-- An actual infinite typed callee is propagated as divergence, never selected
as a completed revert or handed to a catch clause. No finite-fuel adequacy claim. -/
theorem divergence_execution :
    ((attempt forever).runR caller).halt? = some .diverge ∧
    (TRun.catchBytes (call 7) .nil .nil forever.ext forever.runR true caller).halt? =
      some .diverge := by
  have hc : TRun.call (Args.nil : Args contract Γ []) (.rets .nil)
      forever.ext forever.runR caller = .error .diverge := by
    simp only [TRun.call, Args.evalT, bind, Except.bind, pure, Except.pure, forever_run]
  have hz : ((call 7).addr.evalT caller).1 ≠ 0 := by decide +kernel
  have hs : decide (((call 7).addr.evalT caller).1 = caller.tx.selfAddress.1) = true := rfl
  constructor
  · change (TRun.tryCall (call 7) .nil _ _ _ _ _ _ _ _ _ .nil forever.ext forever.runR
      true caller).halt? = _
    simp only [TRun.tryCall, if_neg hz, hs, Bool.and_self, ite_true, hc, TRes.halt?]
  · simp only [TRun.catchBytes, if_neg hz, hs, Bool.and_self, ite_true, hc, TRes.halt?]

/-- info: 'Solidity.Backend.AbiWorld.CatchControls.extracted_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms extracted_actual
/-- info: 'Solidity.Backend.AbiWorld.CatchControls.source_error_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_error_clause
/-- info: 'Solidity.Backend.AbiWorld.CatchControls.source_panic_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_panic_clause
/-- info: 'Solidity.Backend.AbiWorld.CatchControls.allocated_source_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocated_source_error
/-- info: 'Solidity.Backend.AbiWorld.CatchControls.observed_payloads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observed_payloads
/-- info: 'Solidity.Backend.AbiWorld.CatchControls.empty_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_allocation
/-- info: 'Solidity.Backend.AbiWorld.CatchControls.divergence_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms divergence_execution
/-- info: 'Solidity.Backend.AbiWorld.CatchControls.emitted_and_consumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms emitted_and_consumed
/-- info: 'Solidity.Backend.AbiWorld.CatchControls.classified_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms classified_execution
/-- info: 'Solidity.Backend.AbiWorld.CatchControls.noncanonical_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms noncanonical_classification
/-- info: 'Solidity.Backend.AbiWorld.CatchControls.allocated_other_packets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocated_other_packets
/-- info: 'Solidity.Backend.AbiWorld.CatchControls.catch_refusals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms catch_refusals
/-- info: 'Solidity.Backend.AbiWorld.CatchControls.call_refusals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms call_refusals
end Solidity.Backend.AbiWorld.CatchControls
