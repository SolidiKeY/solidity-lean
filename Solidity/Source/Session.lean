import Solidity.Source.HorizonDeploy

/-!
# Sessions that show the events of unfinished transactions (S05 item 2)

`sessionAt` (`Solidity/Source/Semantics.lean`) ends a session's prefix at a
transaction that completes within no horizon up to `n`, showing none of its
events.  `sessionAtEvents` shows them: at horizon `n` the prefix ends with
the events the transaction's run at horizon `n` produced (calls to the
environment, callbacks, their answers), and with a `stuck` run's events
when it is stuck.  The family is still consistent
(`sessionAtEvents_consistent`), because a run that has not completed at
`n` shows a prefix of its events at every larger horizon
(`runTx_events_mono`, `Solidity/Source/Horizon.lean`), so
`sourceLangEvents` has the type of G01's `Lang Event Outcome`.

An unfinished deployment shows its run's events at `n` as well
(`deploy_events_mono`, `Solidity/Source/HorizonDeploy.lean`).
-/

namespace Solidity.Source

open Solidity.Roadmap (Address Word Bytes Event Outcome Request Action SessionEnv Prefix Prefixes Lang)
open EM

variable {E : Env}

theorem firstDone_none_le {α σ : Type} {f : Nat → Except Halt α × σ} {n : Nat} (h : firstDone f n = none) :
    ∀ k ≤ n, Done (f k) = false := by
  intro k hk
  simp only [firstDone, List.findSome?_eq_none_iff, List.mem_range] at h
  have e := h k (by omega)
  cases hd : Done (f k)
  · rfl
  · simp only [hd, if_true, reduceCtorEq] at e

/-- **A session with the events of unfinished transactions** after the
deployment: as `sessionGo`, except that a transaction which completes
within no horizon up to `n` shows its run's events at `n`, and a stuck one
its events when stuck. -/
def sessionGoEvents (P : SrcProg E) (env : SessionEnv) (n : Nat) : Nat → Nat → St E → Outcome →
    Prefix Event Outcome
  | 0, _, s, _ => ⟨s.events, none⟩
  | k + 1, i, s, last =>
    match env.requests s.events i with
    | none => ⟨s.events, some last⟩
    | some (.credit t v) =>
      let s' := (runAt (fun _ => do
        if (← instanceAt (P.glob env) t).isSome then credit t v) s 0).2
      sessionGoEvents P env n k (i + 1) { s' with events := s.events ++ [.credit t v] } last
    | some (.request q) =>
      match firstDone (runAt (fun f => runTx (P.glob env) f q) s) n with
      | some (_, (.ok o, s')) =>
        sessionGoEvents P env n k (i + 1) { s' with events := s.events ++ s'.events.drop s.events.length } o
      | some (_, (.error _, s')) => ⟨s'.events, none⟩
      | none => ⟨(runAt (fun f => runTx (P.glob env) f q) s n).2.events, none⟩

theorem sessionGoEvents_extends (P : SrcProg E) (env : SessionEnv) (n : Nat) :
    ∀ k i (s : St E) last, s.events <+: (sessionGoEvents P env n k i s last).events
  | 0, _, s, _ => List.prefix_refl _
  | k + 1, i, s, last => by
    simp only [sessionGoEvents]
    split
    · exact List.prefix_refl _
    · refine List.IsPrefix.trans ?_ (sessionGoEvents_extends P env n k _ _ _)
      exact List.prefix_append _ _
    · rename_i q _
      split
      · rename_i j o s' hf
        refine List.IsPrefix.trans ?_ (sessionGoEvents_extends P env n k _ _ _)
        exact List.prefix_append _ _
      · rename_i j h s' hf
        obtain ⟨_, hr, _⟩ := firstDone_spec hf
        have := runTx_extends (P.glob env) q s j
        rw [← hr] at this
        exact this
      · exact runTx_extends (P.glob env) q s n

/-- The events a completed transaction leaves are its run's. -/
theorem events_drop {s s' : St E} (h : s.events <+: s'.events) :
    s.events ++ s'.events.drop s.events.length = s'.events := by
  obtain ⟨t, ht⟩ := h
  rw [← ht, List.drop_left]

/-- **Consistent**: a larger horizon (more transaction horizon, more
actions) extends the prefix, and a completed prefix is final. -/
theorem sessionGoEvents_mono (P : SrcProg E) (env : SessionEnv) :
    ∀ k k' n n' i (s : St E) last, k ≤ k' → n ≤ n' →
      (sessionGoEvents P env n k i s last).Le (sessionGoEvents P env n' k' i s last)
  | 0, _, _, _, _, s, last, _, _ => ⟨sessionGoEvents_extends P env _ _ _ s last, .inl rfl⟩
  | k + 1, 0, _, _, _, _, _, h, _ => absurd h (by omega)
  | k + 1, k' + 1, n, n', i, s, last, hk, hn => by
    simp only [sessionGoEvents]
    split
    · exact Prefix.Le.refl _
    · exact sessionGoEvents_mono P env k k' n n' _ _ _ (by omega) hn
    · rename_i q _
      split
      · rename_i j o s' hf
        rw [firstDone_mono _ hn hf]
        exact sessionGoEvents_mono P env k k' n n' _ _ _ (by omega) hn
      · rename_i j h s' hf
        rw [firstDone_mono _ hn hf]
        exact Prefix.Le.refl _
      · rename_i hf
        have hdn := firstDone_none_le hf n (Nat.le_refl _)
        refine ⟨?_, .inl rfl⟩
        show (runAt (fun f => runTx (P.glob env) f q) s n).2.events <+: _
        split
        · rename_i j o s' hf'
          obtain ⟨hj, hr, hd⟩ := firstDone_spec hf'
          have hnj : n ≤ j := by
            by_cases h' : j ≤ n
            · rw [firstDone_none_le hf j h'] at hd; cases hd
            · omega
          have hm := runTx_events_mono (P.glob env) q s hnj hdn
          rw [← hr] at hm
          have hx := runTx_extends (P.glob env) q s j
          rw [← hr] at hx
          refine hm.trans ?_
          have := sessionGoEvents_extends P env n' k' (i + 1)
            { s' with events := s.events ++ s'.events.drop s.events.length } o
          refine List.IsPrefix.trans ?_ this
          show s'.events <+: s.events ++ s'.events.drop s.events.length
          rw [events_drop hx]
          exact List.prefix_refl _
        · rename_i j h s' hf'
          obtain ⟨hj, hr, hd⟩ := firstDone_spec hf'
          have hnj : n ≤ j := by
            by_cases h' : j ≤ n
            · rw [firstDone_none_le hf j h'] at hd; cases hd
            · omega
          have hm := runTx_events_mono (P.glob env) q s hnj hdn
          rw [← hr] at hm
          exact hm
        · exact runTx_events_mono (P.glob env) q s hn hdn

/-- The deployment as a session runs it: its outcome recorded as an event. -/
def deployRun (P : SrcProg E) (env : SessionEnv) (addr : Address) (f : Nat) : EM E [] Outcome := do
  let o ← deploy (P.glob env) f P.main addr env.deployer env.deployValue env.deployArgs
  emitEvent (.deploy env.deployer env.deployValue env.deployArgs o
    (match o with | .success _ => some addr | .revert _ => none))
  pure o

theorem deployRun_grow (P : SrcProg E) (env : SessionEnv) (addr : Address) (f : Nat) :
    Grow (deployRun P env addr f) := by
  unfold deployRun
  exact Grow.bind (deploy_grow _ _ _ _ _ _ _) fun _ => Grow.bind (emitEvent_grow _) fun _ => Grow.pure _

theorem deployRun_approx (P : SrcProg E) (env : SessionEnv) (addr : Address) (f : Nat) :
    Approx (deployRun P env addr f) (deployRun P env addr (f + 1)) := by
  unfold deployRun
  exact Approx.bind (deploy_approx _ _ _ _ _ _ _) fun _ =>
    Approx.refl (Grow.bind (emitEvent_grow _) fun _ => Grow.pure _)

theorem deployRun_events_mono (P : SrcProg E) (env : SessionEnv) (addr : Address) (s : St E) {k k' : Nat}
    (hk : k ≤ k') :
    (runAt (deployRun P env addr) s k).2.events <+: (runAt (deployRun P env addr) s k').2.events := by
  have ha := Approx.mono (f := deployRun P env addr) (deployRun_approx P env addr)
    (deployRun_grow P env addr) hk
  simp only [runAt]
  rcases ha.2.2 (L0 E, s) with ⟨_, he⟩ | he
  · exact he
  · rw [he]; exact List.prefix_refl _

/-- **A session with unfinished transactions' events**, from the
deployment at `addr`; an unfinished deployment shows its run's events at
`n`, and a stuck one its events when stuck. -/
def sessionFromEvents (P : SrcProg E) (env : SessionEnv) (addr : Address) (n : Nat) : Prefix Event Outcome :=
  match firstDone (runAt (deployRun P env addr) (St.init E)) n with
  | some (_, (.ok o, s)) => sessionGoEvents P env n n 0 s o
  | some (_, (.error _, s)) => ⟨s.events, none⟩
  | none => ⟨(runAt (deployRun P env addr) (St.init E) n).2.events, none⟩

/-- The session at the deployment's creation address. -/
def sessionAtEvents (P : SrcProg E) (env : SessionEnv) (n : Nat) : Prefix Event Outcome :=
  sessionFromEvents P env (P.fixed.createAddress env.deployer env.deployNonce) n

theorem sessionFromEvents_consistent (P : SrcProg E) (env : SessionEnv) (addr : Address) :
    Prefixes.Consistent (sessionFromEvents P env addr) := by
  intro n m hnm
  simp only [sessionFromEvents]
  split
  · rename_i j o s hf
    rw [firstDone_mono _ hnm hf]
    exact sessionGoEvents_mono P env n m n m 0 s o hnm hnm
  · rename_i j h s hf
    rw [firstDone_mono _ hnm hf]
    exact Prefix.Le.refl _
  · rename_i hf
    refine ⟨?_, .inl rfl⟩
    show (runAt (deployRun P env addr) (St.init E) n).2.events <+: _
    split
    · rename_i j o s' hf'
      obtain ⟨hj, hr, hd⟩ := firstDone_spec hf'
      have hnj : n ≤ j := by
        by_cases h' : j ≤ n
        · rw [firstDone_none_le hf j h'] at hd; cases hd
        · omega
      have hm := deployRun_events_mono P env addr (St.init E) hnj
      rw [← hr] at hm
      exact hm.trans (sessionGoEvents_extends P env m m 0 s' o)
    · rename_i j h s' hf'
      obtain ⟨hj, hr, hd⟩ := firstDone_spec hf'
      have hnj : n ≤ j := by
        by_cases h' : j ≤ n
        · rw [firstDone_none_le hf j h'] at hd; cases hd
        · omega
      have hm := deployRun_events_mono P env addr (St.init E) hnj
      rw [← hr] at hm
      exact hm
    · exact deployRun_events_mono P env addr (St.init E) hnm

/-- **Consistent** (G01 `Prefixes.Consistent`). -/
theorem sessionAtEvents_consistent (P : SrcProg E) (env : SessionEnv) :
    Prefixes.Consistent (sessionAtEvents P env) :=
  sessionFromEvents_consistent P env _

/-- **The source language with the events of unfinished transactions**
(G01 `Lang Event Outcome`), as `sourceLang` otherwise. -/
def sourceLangEvents (E : Env) : Lang Event Outcome where
  Prog := SrcProg E
  Env := SessionEnv
  Res := Nat
  resLE := inferInstance
  Allowed := SessionEnv.Allowed
  Admissible := fun _ => True
  sem := sessionAtEvents
  consistent := sessionAtEvents_consistent

/-! ## Stuck is not divergence

A transaction's **fate** within horizon `n`: it completes, halts (stuck at a
run-time mismatch), or is pending (it times out at every horizon up to
`n`).  A pending fate can still change; a completed or halted one is the
fate at every larger horizon (`txFate_mono`).  Divergence is pending at
every horizon; it is a timeout at every horizon (`diverges_iff`).  A
stuck fate within some horizon is a run stuck at some horizon
(`stuck_iff`, by `runTx_stable`: the least completing horizon has the
same result), and from then on the fate is that halt at every horizon
(`stuck_eventually`), so a stuck transaction never reads as a divergent
one (`stuck_not_diverges`).  `runTx` turns a revert into a completed
outcome, so `halted` is in practice `stuck`. -/

/-- The fate of a transaction within horizon `n`. -/
inductive TxFate where
  | done (o : Outcome)
  | halted (h : Halt)
  | pending
  deriving DecidableEq

def txFate (G : Glob E) (q : Request) (s : St E) (n : Nat) : TxFate :=
  match firstDone (runAt (fun f => runTx G f q) s) n with
  | some (_, (.ok o, _)) => .done o
  | some (_, (.error h, _)) => .halted h
  | none => .pending

/-- A fate that is not pending is the fate at every larger horizon. -/
theorem txFate_mono (G : Glob E) (q : Request) (s : St E) {n n' : Nat} (hn : n ≤ n')
    (h : txFate G q s n ≠ .pending) : txFate G q s n' = txFate G q s n := by
  simp only [txFate] at h ⊢
  cases hf : firstDone (runAt (fun f => runTx G f q) s) n with
  | none => rw [hf] at h; exact absurd rfl h
  | some x => rw [firstDone_mono _ hn hf]

theorem not_done_iff {α σ : Type} (r : Except Halt α × σ) : Done r = false ↔ r.1 = .error .timeout := by
  rcases r with ⟨r, s⟩
  cases r with
  | ok a => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | error h =>
    cases h with
    | timeout => exact ⟨(fun _ => rfl), (fun _ => rfl)⟩
    | revert _ => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    | stuck _ => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- Pending within `n` is a timeout at every horizon up to `n`. -/
theorem txFate_pending_iff (G : Glob E) (q : Request) (s : St E) (n : Nat) :
    txFate G q s n = .pending ↔ ∀ k ≤ n, (runAt (fun f => runTx G f q) s k).1 = .error .timeout := by
  simp only [txFate]
  cases hf : firstDone (runAt (fun f => runTx G f q) s) n with
  | none =>
    refine ⟨fun _ k hk => (not_done_iff _).1 (firstDone_none_le hf k hk), fun _ => rfl⟩
  | some x =>
    rcases x with ⟨k, r⟩
    obtain ⟨hk, rfl, hd⟩ := firstDone_spec hf
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hr : runAt (fun f => runTx G f q) s k with ⟨o | e, t⟩ <;> rw [hr] at h <;> cases h
    · have := h k hk
      rw [← not_done_iff, hd] at this
      cases this

/-- A run that is done at a horizon within `n` is the fate within `n`. -/
theorem txFate_of_done (G : Glob E) (q : Request) (s : St E) {n k : Nat} (hk : k ≤ n)
    (hd : Done (runAt (fun f => runTx G f q) s k) = true) :
    txFate G q s n = match (runAt (fun f => runTx G f q) s k).1 with
      | .ok o => .done o
      | .error h => .halted h := by
  simp only [txFate]
  cases hf : firstDone (runAt (fun f => runTx G f q) s) n with
  | none => rw [firstDone_none_le hf k hk] at hd; cases hd
  | some x =>
    rcases x with ⟨j, r⟩
    obtain ⟨_, rfl, hdj⟩ := firstDone_spec hf
    have e : runAt (fun f => runTx G f q) s j = runAt (fun f => runTx G f q) s k := by
      rw [← runTx_stable G q s (Nat.le_max_left j k) hdj, runTx_stable G q s (Nat.le_max_right j k) hd]
    rw [e]
    rcases (runAt (fun f => runTx G f q) s k) with ⟨o | h, _⟩ <;> rfl

/-- **Divergence**: pending at every horizon. -/
def Diverges (G : Glob E) (q : Request) (s : St E) : Prop := ∀ n, txFate G q s n = .pending

/-- **Stuck**: halted at a run-time mismatch within some horizon. -/
def Stuck (G : Glob E) (q : Request) (s : St E) : Prop := ∃ n msg, txFate G q s n = .halted (.stuck msg)

theorem diverges_iff (G : Glob E) (q : Request) (s : St E) :
    Diverges G q s ↔ ∀ k, (runAt (fun f => runTx G f q) s k).1 = .error .timeout :=
  ⟨fun h k => (txFate_pending_iff G q s k).1 (h k) k (Nat.le_refl _),
    fun h n => (txFate_pending_iff G q s n).2 fun k _ => h k⟩

theorem stuck_iff (G : Glob E) (q : Request) (s : St E) :
    Stuck G q s ↔ ∃ k msg, (runAt (fun f => runTx G f q) s k).1 = .error (.stuck msg) := by
  constructor
  · rintro ⟨n, msg, h⟩
    simp only [txFate] at h
    cases hf : firstDone (runAt (fun f => runTx G f q) s) n with
    | none => rw [hf] at h; cases h
    | some x =>
      rcases x with ⟨k, r⟩
      obtain ⟨_, rfl, _⟩ := firstDone_spec hf
      rw [hf] at h
      refine ⟨k, msg, ?_⟩
      rcases hr : (runAt (fun f => runTx G f q) s k) with ⟨o | e, t⟩ <;> rw [hr] at h <;> cases h <;> rfl
  · rintro ⟨k, msg, h⟩
    have hd : Done (runAt (fun f => runTx G f q) s k) = true := by
      rw [done_iff, h]; exact fun h' => nomatch h'
    refine ⟨k, msg, ?_⟩
    rw [txFate_of_done G q s (Nat.le_refl k) hd, h]

/-- **Stuck is not divergence**: a run stuck at some horizon does not time
out there. -/
theorem stuck_not_diverges (G : Glob E) (q : Request) (s : St E) (h : Stuck G q s) : ¬ Diverges G q s := by
  intro hd
  obtain ⟨k, msg, hk⟩ := (stuck_iff G q s).1 h
  rw [(diverges_iff G q s).1 hd k] at hk
  cases hk

/-- A stuck transaction's fate is the same halt at every larger horizon. -/
theorem stuck_stable (G : Glob E) (q : Request) (s : St E) {n n' : Nat} (hn : n ≤ n') {msg : String}
    (h : txFate G q s n = .halted (.stuck msg)) : txFate G q s n' = .halted (.stuck msg) := by
  rw [txFate_mono G q s hn (by rw [h]; exact fun h' => nomatch h'), h]

/-- info: 'Solidity.Source.sessionAtEvents_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sessionAtEvents_consistent

/-- info: 'Solidity.Source.stuck_not_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stuck_not_diverges

/-- info: 'Solidity.Source.runTx_events_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runTx_events_mono

/-- **A stuck transaction is eventually always stuck**: from some horizon
on, its fate is the same `stuck` halt. -/
theorem stuck_eventually (G : Glob E) (q : Request) (s : St E) (h : Stuck G q s) :
    ∃ n msg, ∀ n', n ≤ n' → txFate G q s n' = .halted (.stuck msg) := by
  obtain ⟨n, msg, hn⟩ := h
  exact ⟨n, msg, fun _ h' => stuck_stable G q s h' hn⟩

end Solidity.Source
