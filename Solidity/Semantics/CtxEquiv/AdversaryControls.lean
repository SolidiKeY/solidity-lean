import Solidity.Semantics.CtxEquiv.Controls

/-!
# Controls that exercise the G50 adversary (S1.1)

G07's toy language ignores its environment and emits no events, so the
controls of `Solidity/Semantics/CtxEquiv/Controls.lean` would pass with the adversary fixed.  The
language here reads the session: on the first request it answers with a
transaction event, and a program may call an external account whose answer
(possibly a callback) decides its outcome.

- **Requests observe state.**  `store 1` and `store 2` (a getter returning
  the stored byte) agree on the session without requests
  (`store_agree_quiet`) but not on one with a request
  (`store_not_ctxEquiv`): a later transaction reads the final state, and the
  relation quantifies over sessions, not one.
- **Callbacks.**  `guarded` reverts when the callee calls back, `unguarded`
  never: equivalent against every callback-free session
  (`guard_ctxEquiv_noCallback`), not against every session
  (`guard_not_ctxEquiv`); so the no-callback reading is strictly weaker.
- **Sequencing reads the history.**  A continuation reading the length of
  the events so far shows `[1]` after the transaction
  (`seq_reads_history`), which a history-blind continuation does not
  (`seq_history_observed`); the completed prefix keeps the transaction's
  event in front of the continuation's.
-/

namespace Solidity.CtxEquiv.AdversaryControls

open Solidity.Roadmap
open Solidity.Roadmap.Controls (quietEnv quietEnv_allowed)
open Solidity.CtxEquiv
open Solidity.CtxEquiv.Controls (prefix_ne_of_final)

/-- The external account the programs call: not address 0, no precompile. -/
def ext : Address := ⟨4096, by decide⟩

/-- The call to `ext`, as an event. -/
def callExt : Event := .call ext 0 [] false

/-- Programs reading the session. -/
inductive Adv where
  /-- A getter returning the stored byte `k`. -/
  | store (k : UInt8)
  /-- Calls `ext`; reverts with `[1]` if it calls back. -/
  | guarded
  /-- Calls `ext`; succeeds whatever it does. -/
  | unguarded
  deriving DecidableEq

/-- The outcome of the first transaction. -/
def Adv.out : Adv → SessionEnv → Outcome
  | .store k, _ => .success [k]
  | .guarded, e => match e.callee [callExt] with
    | .reenter .. => .revert [1]
    | _ => .success []
  | .unguarded, _ => .success []

/-- The events a program's run emits before its transaction completes. -/
def Adv.calls : Adv → List Event
  | .store _ => []
  | _ => [callExt]

/-- The session: the first request's transaction, or nothing. -/
def Adv.run (p : Adv) (e : SessionEnv) : Prefix Event Outcome :=
  match e.requests [] 0 with
  | some (.request q) =>
    ⟨p.calls ++ [.tx q.sender q.target q.value q.timestamp q.input (p.out e)], some (p.out e)⟩
  | _ => ⟨[], some (.success [])⟩

/-- The language: one bound, every session environment allowed by G01. -/
def advLang : Lang Event Outcome where
  Prog := Adv
  Env := SessionEnv
  Res := Unit
  resLE := ⟨fun _ _ => True⟩
  Allowed := SessionEnv.Allowed
  Admissible := fun _ => True
  sem := fun p e _ => p.run e
  consistent := fun _ _ _ _ _ => Prefix.Le.refl _

/-- A program deployed against G50 adversaries. -/
def advC (p : Adv) : Contract := Deployed.mk' advLang p id

theorem advC_faithful (p : Adv) : (advC p).Faithful := ⟨fun _ h => h, id, fun _ => rfl⟩

theorem advC_behav_eq {p q : Adv} {s : SessionEnv} (h : p.run s = q.run s) :
    (advC p).behav s = (advC q).behav s := by
  funext π
  apply propext
  exact ⟨fun ⟨r, hr, he⟩ => ⟨r, hr, h.symm.trans he⟩, fun ⟨r, hr, he⟩ => ⟨r, hr, h.trans he⟩⟩

/-! ## Sessions -/

/-- A request. -/
def q0 : Request := ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 0, 0, []⟩

/-- One request, no code, every call answered. -/
def reqEnv : SessionEnv := { quietEnv with requests := fun _ i => if i = 0 then some (.request q0) else none }

theorem reqEnv_allowed : reqEnv.Allowed :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- One request; `ext` has code and calls back when called. -/
def cbEnv : SessionEnv :=
  { reqEnv with
    hasCode := fun _ a => a == ext
    callee := fun h => match h.getLast? with
      | some (.call a _ _ _) => if a = ext then .reenter ext ext 0 [] false else .answer (.success [])
      | _ => .answer (.success []) }

theorem cbEnv_allowed : cbEnv.Allowed := by
  refine ⟨fun _ => rfl, fun _ a ha => ?_, fun h a v i s hx => ?_⟩
  · show (a == ext) = false
    cases hx : (a == ext)
    · rfl
    · rw [beq_iff_eq.1 hx] at ha
      exact absurd ha (by show ¬ (Evm.Precompile.ofAddress? 4096).isSome = true; decide)
  · change (a == ext) = false at hx
    have hne : a ≠ ext := fun e => by rw [e] at hx; exact absurd hx (by decide)
    show (match (h ++ [Event.call a v i s]).getLast? with
      | some (.call a _ _ _) =>
        if a = ext then Move.reenter ext ext 0 [] false else Move.answer (.success [])
      | _ => Move.answer (.success [])) = _
    rw [List.getLast?_concat]
    simp only [hne, if_false]

/-! ## Requests observe the state -/

theorem store_agree_quiet : (advC (.store 1)).behav quietEnv = (advC (.store 2)).behav quietEnv :=
  advC_behav_eq rfl

/-- **Negative control**: a transaction reads the stored byte. -/
theorem store_not_ctxEquiv : ¬ CtxEquiv (advC (.store 1)) (advC (.store 2)) :=
  not_ctxEquivOn_of_done reqEnv_allowed (o := .success [1]) ⟨(), trivial, rfl⟩
    fun ⟨r, _, h⟩ => by cases r; exact prefix_ne_of_final (by decide) h

/-! ## Callbacks -/

theorem out_noCallback {e : SessionEnv} (h : e.NoCallback) : Adv.guarded.out e = Adv.unguarded.out e := by
  show (match e.callee [callExt] with
    | .reenter .. => Outcome.revert [1]
    | _ => .success []) = .success []
  cases hc : e.callee [callExt] with
  | reenter t s v i st => exact absurd hc (h _ t s v i st)
  | answer _ => rfl
  | credit _ _ => rfl

/-- **Inhabited**: without callbacks the guard is unobservable. -/
theorem guard_ctxEquiv_noCallback :
    CtxEquivOn (fun e => e.Allowed ∧ e.NoCallback) (advC .guarded) (advC .unguarded) := by
  have hb : ∀ e : SessionEnv, e.NoCallback → (advC .guarded).behav e = (advC .unguarded).behav e :=
    fun e h => advC_behav_eq (by
      show (match e.requests [] 0 with
        | some (.request q) => (⟨[callExt] ++ [Event.tx q.sender q.target q.value q.timestamp q.input
            (Adv.guarded.out e)], some (Adv.guarded.out e)⟩ : Prefix Event Outcome)
        | _ => ⟨[], some (.success [])⟩) = _
      rw [out_noCallback h]
      rfl)
  exact ⟨fun e he => by rw [hb e he.2]; exact Behav.Below.refl _,
    fun e he => by rw [hb e he.2]; exact Behav.Below.refl _⟩

/-- **Negative control**: a callback is observed. -/
theorem guard_not_ctxEquiv : ¬ CtxEquiv (advC .guarded) (advC .unguarded) :=
  not_ctxEquivOn_of_done cbEnv_allowed (o := .revert [1]) ⟨(), trivial, rfl⟩
    fun ⟨r, _, h⟩ => by cases r; exact prefix_ne_of_final (by decide) h

/-- The no-callback reading is strictly weaker. -/
theorem noCallback_strictly_weaker :
    CtxEquivOn (fun e => e.Allowed ∧ e.NoCallback) (advC .guarded) (advC .unguarded) ∧
      ¬ CtxEquiv (advC .guarded) (advC .unguarded) :=
  ⟨guard_ctxEquiv_noCallback, guard_not_ctxEquiv⟩

/-! ## Sequencing reads the history -/

/-- A continuation reverting with the number of events so far. -/
def countK : SessionEnv → List Event → Outcome → Behav Event Outcome :=
  fun _ h _ π => π = ⟨[], some (.revert [h.length.toUInt8])⟩

/-- A history-blind continuation reverting with `[0]`. -/
def zeroK : SessionEnv → List Event → Outcome → Behav Event Outcome :=
  fun _ _ _ π => π = ⟨[], some (.revert [0])⟩

/-- The transaction's event, at `reqEnv`. -/
def txEv : Event := .tx q0.sender q0.target q0.value q0.timestamp q0.input (.success [1])

/-- **Inhabited**: after the transaction, the continuation reads one event,
and the completed prefix keeps it in front. -/
theorem seq_reads_history :
    (advC (.store 1)).seqBehav countK reqEnv ⟨[txEv], some (.revert [1])⟩ :=
  .inr (.inr ⟨⟨[txEv], some (.success [1])⟩, .success [1], ⟨[], some (.revert [1])⟩,
    ⟨(), trivial, rfl⟩, rfl, rfl, rfl⟩)

/-- **Negative control**: a history-blind continuation does not show it. -/
theorem seq_history_observed :
    ¬ ((advC (.store 1)).seqBehav countK reqEnv).Below ((advC (.store 1)).seqBehav zeroK reqEnv) := by
  intro h
  have hd := h.completes seq_reads_history rfl
  rcases hd with ⟨_, hn⟩ | ⟨a, o, _, _, he⟩ | ⟨a, o, k, _, _, hk, he⟩
  · cases hn
  · exact prefix_ne_of_final (fun h => by cases h) he
  · rw [hk] at he
    have hf := congrArg Prefix.final he
    change some (Outcome.revert [1]) = some (Outcome.revert [0]) at hf
    exact absurd hf (by decide)

end Solidity.CtxEquiv.AdversaryControls

/-- info: 'Solidity.CtxEquiv.AdversaryControls.store_not_ctxEquiv' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.AdversaryControls.store_not_ctxEquiv
/-- info: 'Solidity.CtxEquiv.AdversaryControls.noCallback_strictly_weaker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.AdversaryControls.noCallback_strictly_weaker
/-- info: 'Solidity.CtxEquiv.AdversaryControls.seq_history_observed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.CtxEquiv.AdversaryControls.seq_history_observed
