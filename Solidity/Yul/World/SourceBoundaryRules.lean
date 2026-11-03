import Solidity.Yul.World.ReturningStaticControls
import Solidity.Yul.World.ReturningTimeout

/-! Lean-only rules in the owner's actual Source.Hoare judgment. These rules
execute the selected resolved source bodies; their postcondition premises are
ordinary consequence obligations, never supplied callee-adequacy laws. No new
judgment, state, source/Yul embedding or general G51 soundness is introduced. -/
namespace Solidity.Yul.World.SourceBoundaryRules
open Solidity.Source
open Solidity.Roadmap (Outcome)

/-- Eliminate the actual owner judgment using an already proved run equation.
Keeping the computation symbolic here avoids eager unfolding of a concrete
selector/dispatcher while elaborating negative controls. -/
theorem normal_of_run {E Γ α} {P : EMState E Γ → Prop}
    {Q : α → EMState E Γ → Prop} {X : Halt → EMState E Γ → Prop}
    {m : EM E Γ α} {s t : EMState E Γ} {a : α}
    (h : Source.Hoare P m Q X) (pre : P s) (ran : m.run s=(.ok a,t)) : Q a t := by
  have ready := h s pre
  rw [ran] at ready
  exact ready

theorem halt_of_run {E Γ α} {P : EMState E Γ → Prop}
    {Q : α → EMState E Γ → Prop} {X : Halt → EMState E Γ → Prop}
    {m : EM E Γ α} {s t : EMState E Γ} {halt : Halt}
    (h : Source.Hoare P m Q X) (pre : P s) (ran : m.run s=(.error halt,t)) : X halt t := by
  have ready := h s pre
  rw [ran] at ready
  exact ready

/-- Actual code selection depends only on the receiver's code index, not on
the rest of the caller world, heap, locals or journal prefix. -/
theorem selected_at_code (G : Glob ReturningCall.env) (s : EMState ReturningCall.env [])
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0) :
    (Source.instanceAt (ReturningCall.glob G) CallerFrameChecks.receiver).run s=(.ok (some "Finite"),s) := by
  simp only [Source.instanceAt,Source.Hoare.run_bind,ReturningCall.run_st,code,ReturningCall.run_pure]
  rfl

/-- General initial-world case of this actual selected pure return body.
The premise is equality of the existing concrete transfer operation, not
callee adequacy, an operation script or a requested outcome. -/
theorem source_success_at_transfer (G : Glob ReturningCall.env) (s : EMState ReturningCall.env [])
    (next : ExecState ReturningCall.env.layout ReturningCall.env.lay ReturningCall.env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next) :
    (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false).run s=
      (.ok (.success ReturningCall.output),(s.1,{s.2 with ex:=next})) := by
  simp only [Source.callAddr,ReturningCall.parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,selected_at_code G s code,
    ReturningCall.run_mark,ReturningCall.run_st,show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,
    transfer,ReturningCall.run_modSt,Bool.not_true,Bool.false_or]
  rw [ReturningCall.enter_run]

/-- Transfer refusal (insufficient funds OR recipient overflow) uses actual
transfer=None. No code runs and
all caller state is retained; this is a normal empty revert, not timeout. -/
theorem source_transfer_refused (G : Glob ReturningCall.env) (s : EMState ReturningCall.env [])
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=none) :
    (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false).run s=
      (.ok (.revert []),s) := by
  simp only [Source.callAddr,ReturningCall.parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,selected_at_code G s code,
    ReturningCall.run_mark,ReturningCall.run_st,show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,
    transfer,Bool.not_false,if_true]

/-- Source Hoare rule over arbitrary caller worlds/journal prefixes with a
real successful transfer. No initial-state equality to a finite fixture. -/
theorem call_success_general (G : Glob ReturningCall.env)
    (P : EMState ReturningCall.env [] → Prop) (Q : Outcome → EMState ReturningCall.env [] → Prop)
    (X : Halt → EMState ReturningCall.env [] → Prop)
    (entry : ∀ s, P s → (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0 ∧
      ∃ next, s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next)
    (post : ∀ s, P s → ∀ next,
      s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next →
      Q (.success ReturningCall.output) (s.1,{s.2 with ex:=next})) :
    Source.Hoare P (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false) Q X := by
  intro s hs
  obtain ⟨code,next,transfer⟩ := entry s hs
  rw [source_success_at_transfer G s next code transfer]
  exact post s hs next transfer

/-- Actual selected CALL success. The full returned Source state is `ReturningCall.after s`.
The caller supplies only the desired logical consequence of that exact state. -/
theorem call_success (G : Glob ReturningCall.env)
    (P : EMState ReturningCall.env [] → Prop) (Q : Outcome → EMState ReturningCall.env [] → Prop)
    (X : Halt → EMState ReturningCall.env [] → Prop)
    (entry : ∀ s, P s → s.2.ex=ReturningCall.entryExecution)
    (post : ∀ s, P s → Q (.success ReturningCall.output) (ReturningCall.after s)) :
    Source.Hoare P (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false) Q X := by
  intro s hs
  rw [ReturningCall.source_run G s (entry s hs)]
  exact post s hs

/-- Actual selected STATICCALL; `ReturningStatic.after` retains the two no-op journal entries.
Replacing it by the entry state would lose real source journal information. -/
theorem static_success (G : Glob ReturningCall.env)
    (P : EMState ReturningCall.env [] → Prop) (Q : Outcome → EMState ReturningCall.env [] → Prop)
    (X : Halt → EMState ReturningCall.env [] → Prop)
    (entry : ∀ s, P s → s.2.ex=ReturningCall.entryExecution)
    (post : ∀ s, P s → Q (.success ReturningCall.output) (ReturningStatic.after s)) :
    Source.Hoare P (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 0 (ReturningCall.input G) true) Q X := by
  intro s hs
  rw [ReturningStatic.source_run G s (entry s hs)]
  exact post s hs

/-- The external call catches the actual internal custom-error halt and returns
an ordinary `.revert` Outcome. This is the normal postcondition, not X. -/
theorem call_revert (G : Glob ReturningCall.env)
    (P : EMState ReturningCall.env [] → Prop) (Q : Outcome → EMState ReturningCall.env [] → Prop)
    (X : Halt → EMState ReturningCall.env [] → Prop)
    (entry : ∀ s, P s → s.2.ex=ReturningCall.entryExecution)
    (post : ∀ s, P s → Q (.revert (ReturningCall.errorData G)) s) :
    Source.Hoare P (Source.callAddr (ReturningCall.failingGlob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false) Q X := by
  intro s hs
  rw [ReturningCall.failure_source G s (entry s hs)]
  exact post s hs

/-- A smaller actual source horizon retains the dirty transferred state and
uses the halt postcondition. It is not a failed EVM call or rollback. -/
theorem call_timeout (G : Glob ReturningCall.env)
    (P : EMState ReturningCall.env [] → Prop) (Q : Outcome → EMState ReturningCall.env [] → Prop)
    (X : Halt → EMState ReturningCall.env [] → Prop)
    (entry : ∀ s, P s → s.2.ex=ReturningCall.entryExecution)
    (post : ∀ s, P s → X .timeout (ReturningCall.after s)) :
    Source.Hoare P (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 6 CallerFrameChecks.receiver 7 (ReturningCall.input G) false) Q X := by
  intro s hs
  rw [ReturningCall.source_timeout G s (entry s hs)]
  exact post s hs

/-- Before the external call catcher, the same real custom error is a halt.
No account/execution premise is necessary for this pure typed body. -/
theorem internal_revert (G : Glob ReturningCall.env)
    (P : EMState ReturningCall.env [] → Prop) (X : Halt → EMState ReturningCall.env [] → Prop)
    (post : ∀ s, P s → X (.revert (ReturningCall.errorData G)) s) :
    Source.Hoare P (Source.callInternal (ReturningCall.failingGlob G) ReturningCall.child 7 ReturningCall.answerDecl .nil [ReturningCall.uint])
      (fun _ _ => False) X := by
  intro s hs
  rw [ReturningCall.failure_internal G s]
  exact post s hs

/-- Nonempty caller heap and function-local aliases are retained in the actual
complete state postcondition. Empty `[]` indexes the callee local context. -/
def snapshot (G : Glob ReturningCall.env) : EMState ReturningCall.env [] := ⟨Source.L0 ReturningCall.env,(ReturningCall.caller G).2⟩

theorem snapshot_entry (G : Glob ReturningCall.env) : (snapshot G).2.ex=ReturningCall.entryExecution := rfl

theorem success_witness (G : Glob ReturningCall.env) :
    Source.Hoare (fun s=>s=snapshot G)
      (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false)
      (fun out s=>out=.success ReturningCall.output ∧ s=ReturningCall.after (snapshot G)) (fun _ _=>False) := by
  apply call_success G
  · intro s hs; rw [hs]; exact snapshot_entry G
  · intro s hs; exact ⟨rfl,congrArg ReturningCall.after hs⟩

theorem static_witness (G : Glob ReturningCall.env) :
    Source.Hoare (fun s=>s=snapshot G)
      (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 0 (ReturningCall.input G) true)
      (fun out s=>out=.success ReturningCall.output ∧ s=ReturningStatic.after (snapshot G)) (fun _ _=>False) := by
  apply static_success G
  · intro s hs; rw [hs]; exact snapshot_entry G
  · intro s hs; exact ⟨rfl,congrArg ReturningStatic.after hs⟩

theorem revert_witness (G : Glob ReturningCall.env) :
    Source.Hoare (fun s=>s=snapshot G)
      (Source.callAddr (ReturningCall.failingGlob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false)
      (fun out s=>out=.revert (ReturningCall.errorData G) ∧ s=snapshot G) (fun _ _=>False) := by
  apply call_revert G
  · intro s hs; rw [hs]; exact snapshot_entry G
  · intro s hs; exact ⟨rfl,hs⟩

theorem timeout_witness (G : Glob ReturningCall.env) :
    Source.Hoare (fun s=>s=snapshot G)
      (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 6 CallerFrameChecks.receiver 7 (ReturningCall.input G) false)
      (fun _ _=>False) (fun halt s=>halt=.timeout ∧ s=ReturningCall.after (snapshot G)) := by
  apply call_timeout G
  · intro s hs; rw [hs]; exact snapshot_entry G
  · intro s hs; exact ⟨rfl,congrArg ReturningCall.after hs⟩

theorem internal_witness (G : Glob ReturningCall.env) :
    Source.Hoare (fun s=>s=snapshot G)
      (Source.callInternal (ReturningCall.failingGlob G) ReturningCall.child 7 ReturningCall.answerDecl .nil [ReturningCall.uint])
      (fun _ _=>False) (fun halt s=>halt=.revert (ReturningCall.errorData G) ∧ s=snapshot G) := by
  apply internal_revert G
  intro s hs
  exact ⟨rfl,hs⟩

/-- External custom-error completion cannot be justified solely by an internal
revert-halt postcondition. Its actual normal postcondition would be False. -/
theorem wrong_revert_branch (G : Glob ReturningCall.env) :
    ¬ Source.Hoare (fun s=>s=snapshot G)
      (Source.callAddr (ReturningCall.failingGlob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false)
      (fun _ _=>False) (fun halt _=>halt=.revert (ReturningCall.errorData G)) := by
  intro h
  exact normal_of_run h rfl (ReturningCall.failure_source G (snapshot G) (snapshot_entry G))

/-- Timeout cannot be silently moved into the normal EVM outcome branch. -/
theorem wrong_timeout_branch (G : Glob ReturningCall.env) :
    ¬ Source.Hoare (fun s=>s=snapshot G)
      (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 6 CallerFrameChecks.receiver 7 (ReturningCall.input G) false)
      (fun _ _=>True) (fun _ _=>False) := by
  intro h
  exact halt_of_run h rfl (ReturningCall.source_timeout G (snapshot G) (snapshot_entry G))

/-- The two source account writes are visible even though STATICCALL world
balances are equal. The actual-state conclusion cannot be replaced by entry. -/
theorem static_not_entry (G : Glob ReturningCall.env) : ReturningStatic.after (snapshot G)≠snapshot G := by
  intro same
  have journals := congrArg (fun s : EMState ReturningCall.env []=>s.2.ex.journal) same
  exact ReturningStatic.journal_not_unchanged.2.2 journals

theorem snapshot_aliases (G : Glob ReturningCall.env) :
    (snapshot G).2.heap.get 1=some ⟨.bytes .memory,.bytes ReturningCall.old⟩ ∧
    (Source.bytesOfRV (E:=ReturningCall.env) ReturningCall.parentFrame 1 (.val ((snapshot G).2.fnLocals.2.get .here))).run (snapshot G)=
      (.ok ReturningCall.old,snapshot G) := ⟨rfl,rfl⟩

/-- A distinct account nonce update before entry is an actual fourth journal
item, not a supplied list of callee outcomes. -/
def prefixedExecution := ReturningCall.entryExecution.apply
  (.account CallerFrameChecks.target (fun a=>{a with nonce:=37}))
def prefixedMoved := (prefixedExecution.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 4))).apply
  (.account CallerFrameChecks.receiver (fun a=>a.withBalance 30))
def prefixedSnapshot (G : Glob ReturningCall.env) : EMState ReturningCall.env [] :=
  ⟨(snapshot G).1,{(snapshot G).2 with ex:=prefixedExecution}⟩

theorem prefixed_run (G : Glob ReturningCall.env) :
    (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false).run (prefixedSnapshot G)=
      (.ok (.success ReturningCall.output),((prefixedSnapshot G).1,{(prefixedSnapshot G).2 with ex:=prefixedMoved})) :=
  source_success_at_transfer G (prefixedSnapshot G) prefixedMoved rfl rfl

theorem prefixed_rule (G : Glob ReturningCall.env) :
    Source.Hoare (fun s=>s=prefixedSnapshot G)
      (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false)
      (fun out s=>out=.success ReturningCall.output ∧
        s=((prefixedSnapshot G).1,{(prefixedSnapshot G).2 with ex:=prefixedMoved})) (fun _ _=>False) := by
  apply call_success_general G
  · intro s hs
    subst s
    exact ⟨rfl,prefixedMoved,rfl⟩
  · intro s hs next transfer
    subst s
    have same : next=prefixedMoved := Option.some.inj transfer.symm
    subst next
    exact ⟨rfl,rfl⟩

theorem prefixed_accounts : prefixedExecution.journal.length=4 ∧ prefixedMoved.journal.length=6 ∧
    (prefixedMoved.world.accounts CallerFrameChecks.target).nonce=37 ∧
    (prefixedMoved.world.accounts CallerFrameChecks.owner).balance.val=4 ∧
    (prefixedMoved.world.accounts CallerFrameChecks.receiver).balance.val=30 := ⟨rfl,rfl,rfl,rfl,rfl⟩

def insufficientExecution := prefixedExecution.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 0))
def insufficientSnapshot (G : Glob ReturningCall.env) : EMState ReturningCall.env [] :=
  ⟨(snapshot G).1,{(snapshot G).2 with ex:=insufficientExecution}⟩

theorem insufficient_run (G : Glob ReturningCall.env) :
    (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false).run (insufficientSnapshot G)=
      (.ok (.revert []),insufficientSnapshot G) :=
  source_transfer_refused G (insufficientSnapshot G) rfl rfl

theorem insufficient_rule (G : Glob ReturningCall.env) :
    Source.Hoare (fun s=>s=insufficientSnapshot G)
      (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false)
      (fun out s=>out=.revert [] ∧ s=insufficientSnapshot G) (fun _ _=>False) := by
  intro s hs
  subst s
  rw [insufficient_run]
  exact ⟨rfl,rfl⟩

theorem insufficient_keeps_prefix : insufficientExecution.journal.length=5 ∧
    (insufficientExecution.world.accounts CallerFrameChecks.target).nonce=37 ∧
    (insufficientExecution.world.accounts CallerFrameChecks.owner).balance.val=0 ∧
    (insufficientExecution.world.accounts CallerFrameChecks.receiver).balance.val=23 := ⟨rfl,rfl,rfl,rfl⟩

/-- Transfer=None also covers recipient overflow; do not relabel the general
refusal theorem as exclusively insufficient sender funds. -/
def overflowExecution := prefixedExecution.apply (.account CallerFrameChecks.receiver
  (fun a=>a.withBalance ⟨2^256-1,by decide⟩))
def overflowSnapshot (G : Glob ReturningCall.env) : EMState ReturningCall.env [] :=
  ⟨(snapshot G).1,{(snapshot G).2 with ex:=overflowExecution}⟩

theorem overflow_run (G : Glob ReturningCall.env) :
    (Source.callAddr (ReturningCall.glob G) ReturningCall.parentFrame 10 CallerFrameChecks.receiver 7 (ReturningCall.input G) false).run (overflowSnapshot G)=
      (.ok (.revert []),overflowSnapshot G) :=
  source_transfer_refused G (overflowSnapshot G) rfl rfl

theorem overflow_keeps_prefix : overflowExecution.journal.length=5 ∧
    (overflowExecution.world.accounts CallerFrameChecks.target).nonce=37 ∧
    (overflowExecution.world.accounts CallerFrameChecks.owner).balance.val=11 ∧
    (overflowExecution.world.accounts CallerFrameChecks.receiver).balance.val=2^256-1 := ⟨rfl,rfl,rfl,rfl⟩

end Solidity.Yul.World.SourceBoundaryRules
