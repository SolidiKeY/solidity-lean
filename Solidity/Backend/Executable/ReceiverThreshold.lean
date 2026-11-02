import Solidity.Backend.Executable.IterationThresholdChecks

/-! A repeated actual typed receiver observes its credited self balance and
reverts on the third call. This is intrinsic World/constructor-independent
payment-prefix preparation, not source compiler or EVM execution. -/
namespace Solidity.Backend.Executable.ReceiverThreshold
open ContractWorld WorldPrefixes IterationThreshold WorldPrefixChecks
open PaymentCheckpointChecks (contracts sender fresh reference)
abbrev C : Contract := contracts ()
def atThree : Val C [] .bool := .binop .eqB rfl rfl
  (.simple (.env .selfBalance rfl)) (.simple (.lit 3 (by decide)))
def receiver : Entry C Unit := Entry.unit
  (.cons (.ite atThree (.cons (.revertData [.bytes [0xde,0xad]]) .nil) .nil) .nil) true
def op : Operation contracts := .call () reference receiver {sender,mode := .ordinary one}

theorem first_agrees : op.run created = pay.run created := by rfl
def secondState : State C [] where
  storage := Storage.init C
  H := []
  heap := Heap.empty
  env := ()
  selfBalance := ⟨2,by decide⟩
  net := [(sender.1,1)]
  tx := ({sender,mode := .ordinary one} : Context).tx paidOne fresh

theorem second_enters : paidOne.enter fresh {sender,mode := .ordinary one}
    (Storage.init C) true = .ok secondState := by
  have debit : paidOne.funds sender = (⟨2,by decide⟩ : Word) := Subtype.ext (by decide +kernel)
  have credit : paidOne.funds fresh = one := Subtype.ext (by decide +kernel)
  unfold World.enter
  rw [debit,credit]
  rfl

theorem second_storage : paidOne.storage? reference = some (Storage.init C) := by
  have present : (paidOne.storage? reference).isSome = true := by decide +kernel
  cases stored : paidOne.storage? reference with
  | none => rw [stored] at present; cases present
  | some st =>
    have empty : st = Storage.init C := by cases st; rfl
    rw [empty]

theorem second_body : receiver.body.run secondState = (.nil : Prog C [] []).run secondState := by rfl

theorem second_agrees : op.run paidOne = pay.run paidOne := by
  unfold op pay Operation.run World.call World.callFrame
  rw [show paidOne.isLibrary () = false from by decide +kernel]
  simp only [Context.isStatic,Bool.false_and,Bool.or_self,Bool.false_eq_true,↓reduceIte]
  rw [second_storage]
  simp only [TRes.ofOpt,bind,Except.bind]
  rw [show receiver.payable = true from rfl]
  rw [show reference.address = fresh from rfl]
  rw [show (Entry.unit (.nil : Prog C [] []) true).payable = true from rfl]
  rw [second_enters]
  dsimp only
  rw [second_body]
  simp only [receiver,Entry.unit]

theorem third_reverts : op.run paidTwo = .error (.revertWith [0xde,0xad]) := by
  have observed : (match op.run paidTwo with | .ok _ => none | .error e => some e) =
      some (THalt.revertWith [0xde,0xad]) := by decide +kernel
  cases ran : op.run paidTwo with
  | ok next => rw [ran] at observed; cases observed
  | error e => rw [ran] at observed; cases Option.some.inj observed; rfl

def thirdState : State C [] where
  storage := Storage.init C
  H := []
  heap := Heap.empty
  env := ()
  selfBalance := ⟨3,by decide⟩
  net := [(sender.1,1)]
  tx := ({sender,mode := .ordinary one} : Context).tx paidTwo fresh

theorem third_enters : paidTwo.enter fresh {sender,mode := .ordinary one}
    (Storage.init C) true = .ok thirdState := by
  have debit : paidTwo.funds sender = one := Subtype.ext (by decide +kernel)
  have credit : paidTwo.funds fresh = (⟨2,by decide⟩ : Word) := Subtype.ext (by decide +kernel)
  unfold World.enter
  rw [debit,credit]
  rfl

theorem third_body : receiver.body.run thirdState = .error (.revertWith [0xde,0xad]) := by rfl

theorem funded_receiver_boundary : (paidTwo.funds sender).val = 1 ∧
    (paidTwo.funds fresh).val = 2 ∧ thirdState.selfBalance.val = 3 ∧
    atThree.evalT thirdState = .ok true := ⟨by decide +kernel,by decide +kernel,rfl,rfl⟩

theorem first_runs : op.run created = .ok paidOne := first_agrees.trans first_payment
theorem second_runs : op.run paidOne = .ok paidTwo := second_agrees.trans second_payment

theorem two_runs : (List.replicate 2 op).foldlM
    (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok paidTwo := by
  simp only [List.replicate_succ,List.replicate_zero,List.foldlM_cons,List.foldlM_nil,
    first_runs,second_runs,bind,Except.bind,pure,Except.pure]

theorem three_fail : (List.replicate 3 op).foldlM
    (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .error (.revertWith [0xde,0xad]) := by
  rw [show 3 = 2+1 from rfl,iteration_split op 2 1 created,two_runs]
  simp only [bind,Except.bind,List.replicate_succ,List.replicate_zero,List.foldlM_cons,third_reverts]

/-- The repeated receiver's threshold/world are again extracted from a real
finite failure, then identified by independent actual earlier/next runs. -/
theorem discovered : ∃ k middle, k < 3 ∧ k = 2 ∧ middle = paidTwo ∧
    (List.replicate k op).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok middle ∧
    op.run middle = .error (.revertWith [0xde,0xad]) ∧
    (∀ m, k < m → (List.replicate m op).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .error (.revertWith [0xde,0xad])) := by
  obtain ⟨k,middle,bound,ran,failed,_,later,_⟩ := of_failure op created 3 (.revertWith [0xde,0xad]) three_fail
  obtain ⟨index,world,_⟩ := cut_unique op created middle paidTwo k 2
    (.revertWith [0xde,0xad]) (.revertWith [0xde,0xad]) ran failed two_runs third_reverts
  exact ⟨k,middle,bound,index,world,ran,failed,later⟩

theorem all_later (m : Nat) (later : 2 < m) : (List.replicate m op).foldlM
    (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .error (.revertWith [0xde,0xad]) :=
  later_failure op created paidTwo 2 (.revertWith [0xde,0xad]) two_runs third_reverts m later

theorem prefix_commits : atomic created (((List.replicate 2 op).foldlM
    (fun (w : World contracts) (op : Operation contracts) => op.run w) created).map (fun next => (next,()))) =
      (paidTwo,.ok ()) := by rw [two_runs]; rfl

theorem local_rollback : atomic paidTwo ((op.run paidTwo).map (fun next => (next,()))) =
    (paidTwo,.error (.revertWith [0xde,0xad])) := by rw [third_reverts]; rfl

theorem outer_rollback (m : Nat) (later : 2 < m) : atomic created (((List.replicate m op).foldlM
    (fun (w : World contracts) (op : Operation contracts) => op.run w) created).map (fun next => (next,()))) =
      (created,.error (.revertWith [0xde,0xad])) := by rw [all_later m later]; rfl

private theorem rollback_world_ne (a b : World contracts) (left right : TRes Unit)
    (different : (a.funds sender).val ≠ (b.funds sender).val) : (a,left) ≠ (b,right) := by
  intro same
  exact different (congrArg (fun pair : World contracts × TRes Unit => (pair.1.funds sender).val) same)

theorem no_prefix_world_rollback (m : Nat) (later : 2 < m) :
    atomic created (((List.replicate m op).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) created).map (fun next => (next,()))) ≠
        (paidTwo,.error (.revertWith [0xde,0xad])) := by
  rw [outer_rollback m later]
  apply rollback_world_ne
  decide +kernel

theorem no_reversed_bytes (m : Nat) (later : 2 < m) :
    (List.replicate m op).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created ≠
      .error (.revertWith [0xad,0xde]) := by
  rw [all_later m later]
  intro wrong
  cases wrong

theorem no_late_threshold : ¬ ∃ middle e,
    (List.replicate 3 op).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok middle ∧
    op.run middle = .error e := by
  rintro ⟨middle,e,ran,failed⟩
  have wrong := (cut_unique op created middle paidTwo 3 2 e (.revertWith [0xde,0xad]) ran failed two_runs third_reverts).1
  cases wrong

theorem no_wrong_world : ¬ ∃ k e,
    (List.replicate k op).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok paidThree ∧
    op.run paidThree = .error e := by
  rintro ⟨k,e,ran,failed⟩
  have wrong := (cut_unique op created paidThree paidTwo k 2 e (.revertWith [0xde,0xad]) ran failed two_runs third_reverts).2.1
  have distinct : (paidThree.funds sender).val ≠ (paidTwo.funds sender).val := by decide +kernel
  exact distinct (congrArg (fun w : World contracts => (w.funds sender).val) wrong)

/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.first_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms first_agrees
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.second_enters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms second_enters
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.second_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms second_storage
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.second_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms second_body
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.second_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms second_agrees
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.third_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms third_reverts
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.third_enters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms third_enters
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.third_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms third_body
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.funded_receiver_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms funded_receiver_boundary
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.first_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms first_runs
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.second_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms second_runs
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms two_runs
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.three_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms three_fail
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.discovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms discovered
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.all_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms all_later
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.prefix_commits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_commits
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.local_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_rollback
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.outer_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outer_rollback
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.no_prefix_world_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_prefix_world_rollback
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.no_reversed_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_reversed_bytes
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.no_late_threshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_late_threshold
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.no_wrong_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_wrong_world
end Solidity.Backend.Executable.ReceiverThreshold

namespace Solidity.Backend.Executable.ReceiverThreshold
open ContractWorld WorldPrefixChecks
open PaymentCheckpointChecks (contracts sender reference)

private theorem operation_receive (w : World contracts) : op.run w = (do
    let (next,_) ← w.receiveRun reference receiver sender one
    pure next) := rfl

private theorem receive_success (w next : World contracts) (ran : op.run w = .ok next) :
    w.receiveRun reference receiver sender one = .ok (next,()) := by
  rw [operation_receive] at ran
  cases h : w.receiveRun reference receiver sender one with
  | error e => simp only [h,bind,Except.bind] at ran; cases ran
  | ok pair =>
    rcases pair with ⟨actual,⟨⟩⟩
    simp only [h,bind,Except.bind,pure,Except.pure] at ran
    cases Except.ok.inj ran
    rfl

private theorem receive_error (w : World contracts) (e : THalt) (ran : op.run w = .error e) :
    w.receiveRun reference receiver sender one = .error e := by
  rw [operation_receive] at ran
  cases h : w.receiveRun reference receiver sender one with
  | error original =>
    simp only [h,bind,Except.bind] at ran
    cases Except.error.inj ran
    rfl
  | ok pair => cases pair with | mk next u => cases u; simp only [h,bind,Except.bind,pure,Except.pure] at ran; cases ran

/-- Exact failure of the actual history-dependent receive. -/
theorem stipend_receive_failure : paidTwo.receiveRun reference receiver sender one =
    .error (.revertWith [0xde,0xad]) := receive_error _ _ third_reverts

theorem stipend_admitted : (paidTwo.isLibrary () || (paidTwo.storage? reference).isNone) = false := by
  decide +kernel

/-- Caught send retains the whole reached world, not just its balance. -/
theorem stipend_send_failure : paidTwo.stipend .send reference receiver sender one =
    .ok (paidTwo,false) := by
  simp only [World.stipend,stipend_admitted,Bool.false_eq_true,↓reduceIte,
    stipend_receive_failure,sendResult,catchable]

/-- Transfer preserves the original nested bytes. -/
theorem stipend_transfer_failure : paidTwo.stipend .transfer reference receiver sender one =
    .error (.revertWith [0xde,0xad]) :=
  World.stipend_transfer_failure paidTwo reference receiver sender one _
    stipend_admitted stipend_receive_failure

/-- Arbitrarily many caught retries retain the full world and ordered results.
This uses the existing fold and stipend, without a new loop semantics. -/
theorem caught_retries (n : Nat) (observed : List Bool) :
    (List.replicate n ()).foldlM
      (fun (pair : World contracts × List Bool) (_ : Unit) => do
        let (next,result) ← pair.1.stipend .send reference receiver sender one
        pure (next,pair.2 ++ [result])) (paidTwo,observed) =
      .ok (paidTwo,observed ++ List.replicate n false) := by
  induction n generalizing observed with
  | zero => simp only [List.replicate_zero,List.foldlM_nil,List.append_nil,pure,Except.pure]
  | succ n ih =>
    simp only [List.replicate_succ,List.foldlM_cons,stipend_send_failure,bind,Except.bind,pure,Except.pure]
    simpa only [bind,Except.bind,pure,Except.pure,List.replicate_succ,List.append_assoc,List.singleton_append] using ih (observed ++ [false])

private theorem send_success (w next : World contracts) (ran : op.run w = .ok next)
    (admitted : (w.isLibrary () || (w.storage? reference).isNone) = false) :
    w.stipend .send reference receiver sender one = .ok (next,true) := by
  simp only [World.stipend,admitted,Bool.false_eq_true,↓reduceIte,
    receive_success w next ran,sendResult]

theorem first_send : created.stipend .send reference receiver sender one = .ok (paidOne,true) :=
  send_success _ _ first_runs (by decide +kernel)
theorem second_send : paidOne.stipend .send reference receiver sender one = .ok (paidTwo,true) :=
  send_success _ _ second_runs (by decide +kernel)

/-- Both true observations come from actual stipend executions, followed by
all caught retries in their original order and the exact full reached world. -/
theorem prefix_then_send (n : Nat) :
    (do
      let (first,a) ← created.stipend .send reference receiver sender one
      let (middle,b) ← first.stipend .send reference receiver sender one
      (List.replicate n ()).foldlM
        (fun (pair : World contracts × List Bool) (_ : Unit) => do
          let (next,result) ← pair.1.stipend .send reference receiver sender one
          pure (next,pair.2 ++ [result])) (middle,[a,b])) =
      .ok (paidTwo,[true,true] ++ List.replicate n false) := by
  rw [first_send]
  simp only [bind,Except.bind]
  rw [second_send]
  simpa only [bind,Except.bind,pure,Except.pure] using caught_retries n [true,true]

/-- The same successful prefix followed by transfer failure rolls back to the
outer checkpoint, preserving the original halt rather than returning false. -/
theorem prefix_then_transfer : atomic created (do
    let middle ← (List.replicate 2 op).foldlM
      (fun (w : World contracts) (operation : Operation contracts) => operation.run w) created
    middle.stipend .transfer reference receiver sender one) =
      (created,.error (.revertWith [0xde,0xad])) := by
  rw [two_runs]
  simp only [bind,Except.bind]
  rw [stipend_transfer_failure]
  rfl

theorem no_transfer_false : paidTwo.stipend .transfer reference receiver sender one ≠
    .ok (paidTwo,false) := by rw [stipend_transfer_failure]; intro bad; cases bad

private theorem different_world_results (a b : World contracts)
    (different : (a.funds sender).val ≠ (b.funds sender).val) :
    (Except.ok (a,false) : TRes (World contracts × Bool)) ≠ .ok (b,false) := by
  intro wrong
  exact different (congrArg (fun p : World contracts × Bool => (p.1.funds sender).val) (Except.ok.inj wrong))

theorem no_send_changed_world : paidTwo.stipend .send reference receiver sender one ≠
    .ok (paidThree,false) := by
  rw [stipend_send_failure]
  exact different_world_results paidTwo paidThree (by decide +kernel)

theorem no_transfer_reversed_bytes : paidTwo.stipend .transfer reference receiver sender one ≠
    .error (.revertWith [0xad,0xde]) := by
  rw [stipend_transfer_failure]; intro wrong; cases wrong

/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.stipend_receive_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stipend_receive_failure
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.stipend_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stipend_admitted
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.stipend_send_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stipend_send_failure
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.stipend_transfer_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stipend_transfer_failure
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.caught_retries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms caught_retries
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.first_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms first_send
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.second_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms second_send
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.prefix_then_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_then_send
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.prefix_then_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_then_transfer
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.no_transfer_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_transfer_false
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.no_send_changed_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_send_changed_world
/-- info: 'Solidity.Backend.Executable.ReceiverThreshold.no_transfer_reversed_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_transfer_reversed_bytes
end Solidity.Backend.Executable.ReceiverThreshold
