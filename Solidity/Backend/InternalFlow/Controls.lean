import Solidity.Backend.InternalFlow.FrameLaws
import Solidity.Backend.InternalFlow.PrefixLaws
import Solidity.Backend.InternalFlow.RootAdapter
import Solidity.Backend.InternalFlow.Gap

/-! Inhabited controls for partial independent backfill. These do not turn
intrinsic return equations into backend or source-to-bytecode theorems. -/
namespace Solidity.Backend.InternalFlow.Controls

open Backend.Failure

def arrayType : RefTy := .array (.prim .uint)
def contract : Contract :=
  { vars := [("p", .prim .uint), ("t", .prim .uint),
      ("a", .ref arrayType), ("b", .ref arrayType)]
    transientRoots := ["t"] }
def persistent : Storage.RegionRoot contract false (.prim .uint) := ⟨"p", rfl, rfl⟩
def transient : Storage.RegionRoot contract true (.prim .uint) := ⟨"t", rfl, rfl⟩
def referenceA : SRef contract (.ref arrayType) := ⟨"a", rfl, .nil⟩
def referenceB : SRef contract (.ref arrayType) := ⟨"b", rfl, .nil⟩
def seven : PrimTy.uint.Denote := ⟨7, rfl⟩
def nine : PrimTy.uint.Denote := ⟨9, rfl⟩
def eleven : PrimTy.uint.Denote := ⟨11, rfl⟩

def caller : State contract [.val .uint, .val .uint] :=
  (State.init contract).withEnv (nine, eleven, ())
def arguments : Args contract [.val .uint, .val .uint] [.alias arrayType] :=
  .snocStorage .nil arrayType (.user "argument") (.loc (.root "a" rfl))
def result : CallRet [.val .uint, .val .uint] [.alias arrayType]
    [.alias arrayType, .val .uint, .val .uint] := .storage arrayType (.user "result")
def body : TStep contract [.alias arrayType, .alias arrayType]
    [.alias arrayType, .alias arrayType] :=
  TRun.rebind .here (.path (.alias (.there .here)))

theorem nonempty_arguments : arguments.evalT caller = .ok (some referenceA, ()) := rfl

/-- Actual reference argument, actual rebind in the call body, actual return. -/
theorem reference_call :
    (TRun.call arguments result .refl body caller).map (fun out => out.st.env) =
      .ok (some referenceA, nine, eleven, ()) := rfl

theorem wrong_reference :
    (TRun.call arguments result .refl body caller).map
      (fun out => (out.st.env.1 : Option (SRef contract (.ref arrayType))).map SRef.root) ≠ .ok (some "b") := by
  intro h
  have impossible : ("a" : String) = "b" := Option.some.inj (Except.ok.inj h)
  exact (by decide +kernel : ("a" : String) ≠ "b") impossible

/-- Returning into slot zero must leave the same-typed slot one intact. -/
theorem scalar_noninterference :
    (CallRet.val .uint (.user "r") (some .here)).leaveT caller.env (seven, ()) =
      (seven, eleven, ()) := rfl

theorem wrong_scalar_destination :
    (TEnv.get (.there .here)
      ((CallRet.val .uint (.user "r") (some .here)).leaveT caller.env (seven, ()))).1 ≠ 7 := by
  decide +kernel

def first : Grew contract [] [] (MVal · (.ref arrayType)) := (State.init contract).allocDefaultG arrayType rfl
def second : Grew contract [] first.st.H (MVal · (.ref arrayType)) := first.st.allocDefaultG arrayType rfl

/-- Two genuinely allocated arrays, with their old and new heap identities. -/
theorem grown_reference_ids :
    ((first.val : HRef first.st.H arrayType).id, (HRef.wk second.ext (first.val : HRef first.st.H arrayType)).id, (second.val : HRef second.st.H arrayType).id, second.st.H.length) =
      (0, 0, 1, 2) := by decide +kernel

theorem wrong_grown_reference : HRef.wk second.ext (first.val : HRef first.st.H arrayType) ≠ second.val := by
  intro h
  have old_id : (HRef.wk second.ext (first.val : HRef first.st.H arrayType)).id = 0 :=
    congrArg (fun ids => ids.2.1) grown_reference_ids
  have new_id : (second.val : HRef second.st.H arrayType).id = 1 :=
    congrArg (fun ids => ids.2.2.1) grown_reference_ids
  have impossible : (0 : Nat) = 1 := old_id.symm.trans ((congrArg HRef.id h).trans new_id)
  cases impossible

def memoryCaller : TEnv contract second.st.H [.mem arrayType] :=
  (some (HRef.wk second.ext (first.val : HRef first.st.H arrayType)), ())

theorem memory_result_controls :
    (CallRet.mem (Γ := [.mem arrayType]) arrayType (.user "r") rfl rfl).leaveT
      (C := contract) (H := second.st.H) memoryCaller (some second.val, ()) =
      (some second.val, some (HRef.wk second.ext (first.val : HRef first.st.H arrayType)), ()) := rfl

/-- Actual byte-reverting body; THalt retains exactly de-ad-00. -/
theorem exact_body_failure :
    TRun.call arguments result .refl (TRun.revertData [.bytes [0xde, 0xad, 0x00]]) caller =
      .error (.revertWith [0xde, 0xad, 0x00]) := rfl

def saved : Storage contract :=
  ((Storage.init contract).set persistent.declared (.prim seven)).set transient.declared (.prim nine)
def live : Storage contract :=
  ((Storage.init contract).set persistent.declared (.prim eleven)).set transient.declared (.prim seven)
def machine : Slice.Machine := ⟨[], fun _ => 0x73⟩

theorem populated_roots : saved.get persistent.declared = .prim seven ∧
    saved.get transient.declared = .prim nine := ⟨rfl, rfl⟩

theorem mixed_reset :
    (Storage.resetTransient saved).get persistent.declared = .prim seven ∧
    (Storage.resetTransient saved).get transient.declared = .prim (PrimTy.dflt .uint) := ⟨rfl, rfl⟩

/-- Real emission adapter with distinct dirty roots and a nonempty exact payload. -/
theorem emitted_failure :
    Local.execute (Local.save (rootJournal persistent transient saved machine)) 5
      (.custom [0xde, 0xad, 0]) (rootJournal persistent transient live machine) =
      some (rootJournal persistent transient saved machine, .revert [0xde, 0xad, 0]) :=
  root_failure persistent transient saved live machine machine 5 [0xde, 0xad, 0]
    (by unfold Fits; decide +kernel) (by decide +kernel)

/-- Same bytes on RETURN must remain a success, and live roots are committed. -/
theorem emitted_return :
    Local.execute (Local.save (rootJournal persistent transient saved machine)) 5
      (.returned [0xde, 0xad, 0]) (rootJournal persistent transient live machine) =
      some (rootJournal persistent transient live
        { machine with memory := Slice.putBytes machine.memory 5 [0xde, 0xad, 0] },
        .success [0xde, 0xad, 0]) :=
  root_return persistent transient saved live machine machine 5 [0xde, 0xad, 0]
    (by unfold Fits; decide +kernel) (by decide +kernel)

theorem wrong_root_rollback :
    rootJournal persistent transient saved machine ≠ rootJournal persistent transient live machine := by
  intro h
  have roots : (SVal.prim seven : SVal (.prim .uint)) = .prim eleven :=
    congrArg Local.Journal.persistent h
  have impossible : (7 : Int) = 11 := congrArg Subtype.val (SVal.prim.inj roots)
  cases impossible

/-- Only the transient snapshot is wrong; the persistent value stays seven. -/
theorem wrong_transient_rollback :
    rootJournal persistent transient saved machine ≠
      rootJournal persistent transient (saved.set transient.declared (.prim seven)) machine := by
  intro h
  have roots : (SVal.prim nine : SVal (.prim .uint)) = .prim seven :=
    congrArg Local.Journal.transient h
  have impossible : (9 : Int) = 7 := congrArg Subtype.val (SVal.prim.inj roots)
  cases impossible

def dirtyHeap : State contract [] := { first.st with storage := saved }

theorem dirty_reset_heap :
    (dirtyHeap.H.length, dirtyHeap.transactionEntry.H.length) = (1, 0) := by decide +kernel

theorem dirty_reset_roots :
    dirtyHeap.transactionEntry.storage.get persistent.declared = .prim seven ∧
    dirtyHeap.transactionEntry.storage.get transient.declared = .prim (PrimTy.dflt .uint) := ⟨rfl, rfl⟩

theorem distinct_root_identity : persistent.name ≠ transient.name := persistent.disjoint transient

/-- Nonzero split with a changed state and later successful exit. -/
theorem finite_loop_split :
    TLoop.iterN (fun n : Nat => .ok (n + 1)) (fun n => .ok (decide (n < 3))) (1 + 3) 0 =
      .inr (.ok 3) := rfl

/-- Exact byte failures remain terminal at later horizons. -/
theorem split_rejoins :
    TLoop.iterN (fun n : Nat => .ok (n + 1)) (fun n => .ok (decide (n < 3))) (1 + 3) 0 =
      TLoop.iterN (fun n : Nat => .ok (n + 1)) (fun n => .ok (decide (n < 3))) 3 1 :=
  loop_prefix_continue _ _ 1 3 0 1 rfl

theorem loop_byte_failure :
    TLoop.iterN (fun _ : Nat => .error (.revertWith [0xde, 0xad]))
      (fun _ => .ok true) 7 0 = .inr (.error (.revertWith [0xde, 0xad])) := rfl

theorem running_prefixes (n initial : Nat) :
    TLoop.iterN (fun k : Nat => .ok (k + 1)) (fun _ => .ok true) n initial =
      .inl (initial + n) := by
  induction n generalizing initial with
  | zero => rfl
  | succ n ih =>
    simp only [TLoop.iterN, TLoop.step]
    rw [ih]
    congr 1
    omega

theorem unbounded_loop :
    TLoop.run (fun k : Nat => .ok (k + 1)) (fun _ => .ok true) 0 = .error .diverge :=
  loop_all_prefixes_running _ _ _ (fun n => ⟨n, by simpa only [Nat.zero_add] using running_prefixes n 0⟩)

def completed : Roadmap.Prefix Nat (List UInt8) := ⟨[3], some [0xde, 0xad]⟩

theorem nonempty_history : prefixContext [1, 2] completed = ⟨[1, 2, 3], some [0xde, 0xad]⟩ := rfl

theorem wrong_history_order : prefixContext [1, 2] completed ≠ prefixContext [2, 1] completed := by
  intro h
  have impossible : (1 : Nat) = 2 := congrArg (fun p => p.events.head!) h
  cases impossible

theorem completed_cannot_grow :
    ¬ completed.Le (⟨[3, 4], some [0xde, 0xad]⟩ : Roadmap.Prefix Nat (List UInt8)) := by
  intro h
  have impossible : ([3, 4] : List Nat) = [3] :=
    congrArg Roadmap.Prefix.events (h.final_eq rfl)
  cases impossible

/-- info: 'Solidity.Backend.InternalFlow.call_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms call_return
/-- info: 'Solidity.Backend.InternalFlow.result_renaming' depends on axioms: [propext] -/
#guard_msgs in
#print axioms result_renaming
/-- info: 'Solidity.Backend.InternalFlow.loop_prefix_add' does not depend on any axioms -/
#guard_msgs in
#print axioms loop_prefix_add
/-- info: 'Solidity.Backend.InternalFlow.loop_all_prefixes_running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_all_prefixes_running
/-- info: 'Solidity.Backend.InternalFlow.root_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms root_failure
/-- info: 'Solidity.Backend.InternalFlow.transaction_entry_idempotent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms transaction_entry_idempotent
/-- info: 'Solidity.Backend.InternalFlow.Controls.reference_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reference_call
/-- info: 'Solidity.Backend.InternalFlow.Controls.unbounded_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unbounded_loop
/-- info: 'Solidity.Backend.InternalFlow.Controls.emitted_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms emitted_failure

/-- info: 'Solidity.Backend.InternalFlow.call_body_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms call_body_failure
/-- info: 'Solidity.Backend.InternalFlow.loop_observed_of_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_observed_of_prefix
/-- info: 'Solidity.Backend.InternalFlow.root_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms root_return
/-- info: 'Solidity.Backend.InternalFlow.reset_root_pair' depends on axioms: [propext] -/
#guard_msgs in
#print axioms reset_root_pair

end Solidity.Backend.InternalFlow.Controls
