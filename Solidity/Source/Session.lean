import Solidity.Source.Horizon

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

The deployment is as in `sessionAt`: an unfinished deployment shows no
events (its monotonicity of events is not proved).
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

/-- **A session with unfinished transactions' events**, from the
deployment at `addr`. -/
def sessionFromEvents (P : SrcProg E) (env : SessionEnv) (addr : Address) (n : Nat) : Prefix Event Outcome :=
  let G := P.glob env
  let dep := fun f => do
    let o ← deploy G f P.main addr env.deployer env.deployValue env.deployArgs
    emitEvent (.deploy env.deployer env.deployValue env.deployArgs o
      (match o with | .success _ => some addr | .revert _ => none))
    pure o
  match firstDone (runAt dep (St.init E)) n with
  | some (_, (.ok o, s)) => sessionGoEvents P env n n 0 s o
  | _ => ⟨[], none⟩

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
  · exact ⟨List.nil_prefix, .inl rfl⟩

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

/-- info: 'Solidity.Source.sessionAtEvents_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sessionAtEvents_consistent

/-- info: 'Solidity.Source.runTx_events_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runTx_events_mono

end Solidity.Source
