import SolidityBridge.ExternalEvm.Assembly.SafeTrace

namespace Solidity.Evm.External.Assembly

/-! The existing source composition induction, carrying decoded packet and
scanner-membership evidence through every actual fetched microstep. -/

def SafeMacroRefinement (destinations : List EvmYul.UInt256) {code : List Instr} {base : Nat} (image : Image code base)
    (frame : EvmYul.EVM.State) : Prop :=
  ∀ (pre : List Instr) (i : Instr) (rest : List Instr),
    code = pre ++ i :: rest →
    ∀ (m m' : Machine) (skip : Nat) (s : EvmYul.EVM.State),
    i.step m = .ok m' skip → Boundary image frame pre.length m s →
    ∃ n t, SafeTrace destinations n s t ∧
      Boundary image frame (pre.length + 1 + skip) m' t

/-- General relocated suffix composition, by induction over the existing
core runner. No target evaluator expansion, fuel increase, or independent
whole-target-run premise is used here. -/
theorem safe_exec_simulation {destinations : List EvmYul.UInt256} {code : List Instr} {base : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (macros : SafeMacroRefinement destinations image frame)
    (pre rest : List Instr) (hc : code = pre ++ rest)
    (skip : Nat) (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary image frame (pre.length + skip) m s)
    (source : exec rest skip m = .ok m' 0) :
    ∃ n t, SafeTrace destinations n s t ∧
      Boundary image frame code.length m' t := by
  induction rest generalizing pre skip m s with
  | nil =>
    simp only [exec_nil, Out.ok.injEq] at source
    obtain ⟨rfl, rfl⟩ := source
    refine ⟨0, s, .nil _, ?_⟩
    simpa only [hc, List.append_nil, Nat.add_zero] using entry
  | cons i rest ih =>
    cases skip with
    | succ skip =>
      apply ih (pre ++ [i]) (by simpa only [List.append_assoc, List.singleton_append] using hc) skip m s
      · simpa only [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_comm skip 1] using entry
      · exact source
    | zero =>
      simp only [exec_cons_zero] at source
      cases hs : i.step m with
      | fault => simp only [hs, Out.fault_bind] at source
                 cases source
      | revert => simp only [hs, Out.revert_bind] at source
                  cases source
      | ok next k =>
        obtain ⟨n, t, ht, hb⟩ := macros pre i rest hc m next k s hs
          (by simpa only [Nat.add_zero] using entry)
        obtain ⟨n', u, hu, he⟩ := ih (pre ++ [i])
          (by simpa only [List.append_assoc, List.singleton_append] using hc) k next t
          (by simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using hb)
          (by simpa only [hs, Out.ok_bind] using source)
        refine ⟨n + n', u, ?_, he⟩
        exact ht.trans hu

theorem safe_run_simulation {destinations : List EvmYul.UInt256} {code : List Instr} {base : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State)
    (macros : SafeMacroRefinement destinations image frame) (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary image frame 0 m s) (source : run code m = .ok m' 0) :
    ∃ n t, SafeTrace destinations n s t ∧ Boundary image frame code.length m' t :=
  safe_exec_simulation image frame macros [] code rfl 0 m m' s entry source



def SafeTurnRefinement (destinations : List EvmYul.UInt256) (rc rb : Machine → Out)
    (header exit : Machine → EvmYul.EVM.State → Prop) : Prop :=
  ∀ m s, header m s →
    (∀ m', loopTurn rc rb m = .inl m' →
      ∃ n t, 0 < n ∧ SafeTrace destinations n s t ∧ header m' t) ∧
    (∀ m', loopTurn rc rb m = .inr (.ok m' 0) →
      ∃ n t, 0 < n ∧ SafeTrace destinations n s t ∧ exit m' t)

/-- Finite semantic loop iterations compose actual fetched traces, with
positive progress for every completed turn. -/
theorem safe_loopIterN_simulation {destinations : List EvmYul.UInt256} {rc rb : Machine → Out}
    {header exit : Machine → EvmYul.EVM.State → Prop}
    (turn : SafeTurnRefinement destinations rc rb header exit)
    (n : Nat) (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : header m s) (h : loopIterN rc rb n m = .inr (.ok m' 0)) :
    ∃ k t, 0 < k ∧ SafeTrace destinations k s t ∧ exit m' t := by
  induction n generalizing m s with
  | zero => cases h
  | succ n ih =>
    cases ht : loopTurn rc rb m with
    | inl next =>
      obtain ⟨k, t, hk, hs, he⟩ := (turn m s entry).1 next ht
      obtain ⟨k', u, hk', hu, hout⟩ := ih next t he
        (by simpa only [loopIterN, ht] using h)
      refine ⟨k + k', u, by omega, ?_, hout⟩
      exact hs.trans hu
    | inr out =>
      have ho : out = .ok m' 0 := by simpa only [loopIterN, ht, Sum.inr.injEq] using h
      subst out
      exact (turn m s entry).2 m' ht

theorem safe_structured_loop_simulation {destinations : List EvmYul.UInt256} {rc rb : Machine → Out}
    {header exit : Machine → EvmYul.EVM.State → Prop}
    (turn : SafeTurnRefinement destinations rc rb header exit)
    (m m' : Machine) (s : EvmYul.EVM.State) (entry : header m s)
    (source : loopRun rc rb m = .ok m' 0) :
    ∃ k t, 0 < k ∧ SafeTrace destinations k s t ∧ exit m' t := by
  obtain ⟨n, hn⟩ := loopRun_ok_witness source
  exact safe_loopIterN_simulation turn n m m' s entry hn

/-- Every still-running semantic prefix has an actual target prefix with
at least as many steps. There is no finite-fuel X divergence conclusion. -/
theorem safe_loop_prefix_simulation {destinations : List EvmYul.UInt256} {rc rb : Machine → Out}
    {header exit : Machine → EvmYul.EVM.State → Prop}
    (turn : SafeTurnRefinement destinations rc rb header exit)
    (n : Nat) (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : header m s) (h : loopIterN rc rb n m = .inl m') :
    ∃ k t, n ≤ k ∧ SafeTrace destinations k s t ∧ header m' t := by
  induction n generalizing m s with
  | zero =>
    have hm : m = m' := Sum.inl.inj h
    subst m'
    exact ⟨0, s, Nat.le_refl _, .nil _, entry⟩
  | succ n ih =>
    cases ht : loopTurn rc rb m with
    | inl next =>
      obtain ⟨k, t, hk, hs, he⟩ := (turn m s entry).1 next ht
      obtain ⟨k', u, hk', hu, hout⟩ := ih next t he
        (by simpa only [loopIterN, ht] using h)
      refine ⟨k + k', u, by omega, ?_, hout⟩
      exact hs.trans hu
    | inr out =>
      simp only [loopIterN, ht] at h
      cases h



theorem safe_turn_of_parts {destinations : List EvmYul.UInt256} {rc rb : Machine → Out}
    {header condition bodyEntry bodyExit exit : Machine → EvmYul.EVM.State → Prop}
    (cond : ∀ m s, header m s → ∀ mc, rc m = .ok mc 0 →
      ∃ n t, SafeTrace destinations n s t ∧ condition mc t)
    (zero : ∀ mc s w tail, condition mc s → mc.stack = .val w :: tail → w.val = 0 →
      ∃ n t, 0 < n ∧ SafeTrace destinations n s t ∧ exit {mc with stack := tail} t)
    (nonzero : ∀ mc s w tail, condition mc s → mc.stack = .val w :: tail → w.val ≠ 0 →
      ∃ n t, 0 < n ∧ SafeTrace destinations n s t ∧ bodyEntry {mc with stack := tail} t)
    (body : ∀ m s, bodyEntry m s → ∀ next, rb m = .ok next 0 →
      ∃ n t, SafeTrace destinations n s t ∧ bodyExit next t)
    (back : ∀ m s, bodyExit m s → ∃ n t,
      SafeTrace destinations n s t ∧ header m t) :
    SafeTurnRefinement destinations rc rb header exit := by
  intro m s he
  constructor
  · intro next ht
    obtain ⟨mc, w, tail, hc, hs, hn, hb⟩ := loopTurn_continue ht
    obtain ⟨a, t, hat, hct⟩ := cond m s he mc hc
    obtain ⟨b, u, hpos, hbu, hbe⟩ := nonzero mc t w tail hct hs hn
    obtain ⟨c, v, hcv, hce⟩ := body _ u hbe next hb
    obtain ⟨d, z, hdz, hze⟩ := back next v hce
    refine ⟨a + (b + (c + d)), z, by omega, ?_, hze⟩
    exact hat.trans (hbu.trans (hcv.trans hdz))
  · intro next ht
    obtain ⟨mc, w, tail, hc, hs, hz, rfl⟩ := loopTurn_exit ht
    obtain ⟨a, t, hat, hct⟩ := cond m s he mc hc
    obtain ⟨b, u, hpos, hbu, hbe⟩ := zero mc t w tail hct hs hz
    refine ⟨a + b, u, by omega, ?_, hbe⟩
    exact hat.trans hbu


end Solidity.Evm.External.Assembly
