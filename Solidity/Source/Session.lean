import Solidity.Source.HorizonDeploy


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
      if requestFunded P.fixed env.balance s.events q then
        match firstDone (runAt (fun f => runTx (P.glob env) f q) s) n with
        | some (_, (.ok o, s')) =>
          sessionGoEvents P env n k (i + 1) { s' with events := s.events ++ s'.events.drop s.events.length } o
        | some (_, (.error _, s')) => ⟨s'.events, none⟩
        | none => ⟨(runAt (fun f => runTx (P.glob env) f q) s n).2.events, none⟩
      else sessionGoEvents P env n k (i + 1) s last

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
      · split
        · rename_i j o s' hf
          refine List.IsPrefix.trans ?_ (sessionGoEvents_extends P env n k _ _ _)
          exact List.prefix_append _ _
        · rename_i j h s' hf
          obtain ⟨_, hr, _⟩ := firstDone_spec hf
          have := runTx_extends (P.glob env) q s j
          rw [← hr] at this
          exact this
        · exact runTx_extends (P.glob env) q s n
      · exact sessionGoEvents_extends P env n k (i + 1) s last

theorem events_drop {s s' : St E} (h : s.events <+: s'.events) :
    s.events ++ s'.events.drop s.events.length = s'.events := by
  obtain ⟨t, ht⟩ := h
  rw [← ht, List.drop_left]

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
      · split
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
      · exact sessionGoEvents_mono P env k k' n n' (i + 1) s last (by omega) hn

def deployRun (P : SrcProg E) (env : SessionEnv) (addr : Address) (f : Nat)
    (plan : FailureExecution.RuntimePlan := none) : EM E [] Outcome := do
  let o ← deploy (plan := plan) (P.glob env) f P.main addr env.deployer env.deployValue env.deployArgs
  emitEvent (plan := none) (.deploy env.deployer env.deployValue env.deployArgs o
    (match o with | .success _ => some addr | .revert _ => none))
  pure o

theorem deployRun_run {E : Env} (P : SrcProg E) (env : Roadmap.SessionEnv)
    (addr : Roadmap.Address) (f : Nat) (plan : FailureExecution.RuntimePlan)
    (l : Locals E.layout []) (s : St E) :
    (deployRun P env addr f plan).run (l,s) =
      match (deploy (plan := plan) (P.glob env) f P.main addr env.deployer env.deployValue env.deployArgs).run (l,s) with
      | (.ok o,(l',s')) =>
        (.ok o,(l',{ s' with events := s'.events ++
          [.deploy env.deployer env.deployValue env.deployArgs o
            (match o with | .success _ => some addr | .revert _ => none)] }))
      | (.error why,post) => (.error why,post) := by
  unfold deployRun
  rw [ExceptT.run_bind]
  show StateT.bind (ExceptT.run (deploy (plan := plan) (P.glob env) f P.main addr
    env.deployer env.deployValue env.deployArgs)) _ (l,s) = _
  simp only [StateT.bind]
  cases h : (deploy (plan := plan) (P.glob env) f P.main addr env.deployer
    env.deployValue env.deployArgs).run (l,s) with
  | mk result post => cases result <;> cases post <;> rfl

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

def sessionFromEvents (P : SrcProg E) (env : SessionEnv) (addr : Address) (n : Nat) : Prefix Event Outcome :=
  match firstDone (runAt (deployRun P env addr) (St.init E)) n with
  | some (_, (.ok o, s)) => sessionGoEvents P env n n 0 s o
  | some (_, (.error _, s)) => ⟨s.events, none⟩
  | none => ⟨(runAt (deployRun P env addr) (St.init E) n).2.events, none⟩

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

theorem sessionAtEvents_consistent (P : SrcProg E) (env : SessionEnv) :
    Prefixes.Consistent (sessionAtEvents P env) :=
  sessionFromEvents_consistent P env _

def sourceLangEvents (E : Env) : Lang Event Outcome where
  Prog := SrcProg E
  Env := SessionEnv
  Res := Nat
  resLE := inferInstance
  Allowed := SessionEnv.Allowed
  Admissible := fun _ => True
  sem := sessionAtEvents
  consistent := sessionAtEvents_consistent


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

def Diverges (G : Glob E) (q : Request) (s : St E) : Prop := ∀ n, txFate G q s n = .pending

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

theorem stuck_not_diverges (G : Glob E) (q : Request) (s : St E) (h : Stuck G q s) : ¬ Diverges G q s := by
  intro hd
  obtain ⟨k, msg, hk⟩ := (stuck_iff G q s).1 h
  rw [(diverges_iff G q s).1 hd k] at hk
  cases hk

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

theorem stuck_eventually (G : Glob E) (q : Request) (s : St E) (h : Stuck G q s) :
    ∃ n msg, ∀ n', n ≤ n' → txFate G q s n' = .halted (.stuck msg) := by
  obtain ⟨n, msg, hn⟩ := h
  exact ⟨n, msg, fun _ h' => stuck_stable G q s h' hn⟩

end Solidity.Source
