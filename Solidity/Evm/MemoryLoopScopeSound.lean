import Solidity.Evm.MemoryLoopScopeMeta
namespace Solidity.Evm.Memory.LoopScopes
variable {C : Contract}

def StmtSound {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) (L frame : Nat) : Prop :=
  ∀ (σ : State C Γ) (base : Nat → Fin W) (m : Machine),
    StateRepr L b frame F σ base m → b + hs.need ≤ frame →
    (∀ amount, StmtDemand hs σ amount → AllocationInput b frame amount σ base m) →
    Result L b frame G σ base m (fun o amount => StmtCost hs σ o amount) (s.run σ) (run code m)

def ProgSound {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) (L frame : Nat) : Prop :=
  ∀ (σ : State C Γ) (base : Nat → Fin W) (m : Machine),
    StateRepr L b frame F σ base m → b + hp.need ≤ frame → Room hp frame σ base m →
    Result L b frame G σ base m (fun o amount => Cost hp σ o amount) (P.run σ) (run code m)

theorem run_singleton {Γ Δ : Ctx} (s : Stmt C Γ Δ) (σ : State C Γ) :
    (Prog.cons s .nil).run σ = s.run σ := by
  cases ho : s.run σ with
  | ok o => rw [Prog.run_cons_ok ho]; rfl
  | error halt =>
    show TRun.seq s.runR Prog.nil.runR σ = _
    simp only [TRun.seq, Stmt.run] at ho ⊢
    rw [ho]

private theorem base_sound {b L frame Γ Δ F G s code}
    (hs : Loops.StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) :
    StmtSound (.base hs) L frame := by
  intro σ base m hr cap room
  have cap' : b + (singleton hs).need ≤ frame := cap
  have room' : Loops.Room (singleton hs) frame σ base m := fun amount h => room amount (.base h)
  rcases (singleton hs).correct hr cap' room' with
    ⟨o, m', base', amount, ho, ht, hc, hr', stack, he, hg⟩ | ⟨ho, ht⟩ | ⟨ho, ht⟩
  · exact .inl ⟨o, m', base', amount, by simpa only [run_singleton] using ho,
      by simpa only [List.append_nil] using ht, .base hc, hr', stack, he, hg⟩
  · exact .inr (.inl ⟨by simpa only [run_singleton] using ho,
      by simpa only [List.append_nil] using ht⟩)
  · exact .inr (.inr ⟨by simpa only [run_singleton] using ho,
      by simpa only [List.append_nil] using ht⟩)

private theorem source_cons_halt {Γ Δ Ξ : Ctx} {σ : State C Γ} {s : Stmt C Γ Δ}
    {P : Prog C Δ Ξ} {halt : THalt} (h : s.run σ = .error halt) :
    (Prog.cons s P).run σ = .error halt := by
  show TRun.seq s.runR P.runR σ = _
  simp only [TRun.seq, Stmt.run] at h ⊢
  rw [h]

private theorem target_append_fault {head tail : List Instr} {m : Machine}
    (h : run head m = .fault) : run (head ++ tail) m = .fault := by
  simp only [run] at h ⊢
  rw [exec_append, h]
  rfl

private theorem nil_sound {b L frame Γ} (F : Frag Γ) :
    ProgSound (ProgCert.nil (C := C) (b := b) F) L frame := by
  intro σ base m hr cap room
  exact .inl ⟨⟨σ, List.prefix_refl _⟩, m, base, 0, rfl, rfl, .nil σ, hr, rfl,
    BaseExtends.refl base, fun _ _ ha _ => ha⟩

private theorem cons_sound {b L frame Γ Δ Ξ F G K s P head tail}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s head)
    (hp : ProgCert b (Γ := Δ) (Δ := Ξ) G K P tail)
    (ihs : StmtSound hs L frame) (ihp : ProgSound hp L frame) :
    ProgSound (.cons hs hp) L frame := by
  intro σ base m hr cap room
  have caps : b + hs.need ≤ frame := by change b + max hs.need hp.need ≤ frame at cap; omega
  have capp : b + hp.need ≤ frame := by change b + max hs.need hp.need ≤ frame at cap; omega
  rcases ihs σ base m hr caps (fun amount h => room amount (.head h)) with
    ⟨o, m', base', cost, ho, ht, hc, hr', stack, he, hg⟩ | ⟨ho, ht⟩ | ⟨ho, ht⟩
  · have next : Room hp frame o.st base' m' := by
      intro amount hd
      exact hg.nextInput (room _ (.tail ho hc hd))
    rcases ihp o.st base' m' hr' capp next with
      ⟨o', m'', base'', rest, ho', ht', hc', hr'', stack', he', hg'⟩ | ⟨ho', ht'⟩ | ⟨ho', ht'⟩
    · refine .inl ⟨⟨o'.st, o.ext.trans o'.ext⟩, m'', base'', cost + rest,
        ?_, ?_, .cons ho hc hc', hr'', stack'.trans stack, he.trans o.ext he', hg.comp hg'⟩
      · rw [Prog.run_cons_ok ho, ho']; rfl
      · rw [run_append_ok ht]; exact ht'
    · exact .inr (.inl ⟨by rw [Prog.run_cons_ok ho, ho']; rfl,
        by rw [run_append_ok ht]; exact ht'⟩)
    · exact .inr (.inr ⟨by rw [Prog.run_cons_ok ho, ho']; rfl,
        by rw [run_append_ok ht]; exact ht'⟩)
  · exact .inr (.inl ⟨source_cons_halt ho, run_append_revert ht⟩)
  · exact .inr (.inr ⟨source_cons_halt ho, target_append_fault ht⟩)

private theorem block_sound {b L frame Γ Δ F G body code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G body code)
    (ih : ProgSound hp L frame) : StmtSound (.block hp) L frame := by
  intro σ base m hr cap room
  have cap' : b + hp.need ≤ frame := by change b + max Γ.length hp.need ≤ frame at cap; omega
  have room' : Room hp frame σ base m := fun amount hd => room amount (.block hd)
  rcases ih σ base m hr cap' room' with
    ⟨o, m', base', amount, ho, ht, hc, hr', stack, he, hg⟩ | ⟨ho, ht⟩ | ⟨ho, ht⟩
  · refine .inl ⟨⟨o.st.drop body.ext, o.ext⟩, m', base', amount, ?_, ht,
      .block ho hc, hr'.drop body.ext, stack, he, hg⟩
    change (body.run σ).map (fun o => (⟨o.st.drop body.ext, o.ext⟩ : Solidity.Out C σ.H Γ)) = _
    rw [ho]
    rfl
  · refine .inr (.inl ⟨?_, ht⟩)
    change (body.run σ).map (fun o => (⟨o.st.drop body.ext, o.ext⟩ : Solidity.Out C σ.H Γ)) = _
    rw [ho]
    rfl
  · refine .inr (.inr ⟨?_, ht⟩)
    change (body.run σ).map (fun o => (⟨o.st.drop body.ext, o.ext⟩ : Solidity.Out C σ.H Γ)) = _
    rw [ho]
    rfl

private theorem ite_sound {b L frame Γ Δ Ξ F G K c thn els cond left right}
    (hc : ValFrag (C := C) b (Γ := Γ) F c cond)
    (ht : ProgCert b (Γ := Γ) (Δ := Δ) F G thn left)
    (he : ProgCert b (Γ := Γ) (Δ := Ξ) F K els right)
    (iht : ProgSound ht L frame) (ihe : ProgSound he L frame) :
    StmtSound (.ite hc ht he) L frame := by
  intro σ base m hr cap room
  have capt : b + ht.need ≤ frame := by
    change b + max Γ.length (max ht.need he.need) ≤ frame at cap
    omega
  have cape : b + he.need ≤ frame := by
    change b + max Γ.length (max ht.need he.need) ≤ frame at cap
    omega
  change Result _ _ _ _ _ _ _ _ (TRun.ite c thn.ext thn.runR els.ext els.runR σ) _
  simp only [TRun.ite, conditionalCode, List.append_assoc]
  rcases hc.correct hr with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain rfl := hrc.bool_inv
    rw [run_append_ok hrunc, hvc]
    simp only [bind, Except.bind, Solidity.boolT]
    cases vc
    · rw [run_append_skip (m' := m) (k := left.length + 1) rfl,
        exec_skip_append]
      simp only [Out.ok_bind, Bool.false_eq_true, ↓reduceIte]
      rcases ihe σ base m hr cape (fun amount hd => room amount (.iteFalse hvc hd)) with
        ⟨o, m', base', amount, ho, htgt, hcost, hr', stack, hb, hg⟩ |
        ⟨ho, htgt⟩ | ⟨ho, htgt⟩
      · refine .inl ⟨⟨o.st.drop els.ext, o.ext⟩, m', base', amount, ?_, htgt,
          .iteFalse hvc ho hcost, (hr'.drop els.ext).meetRight _, stack, hb, hg⟩
        change (els.run σ).map _ = _
        rw [ho]
        rfl
      · refine .inr (.inl ⟨?_, htgt⟩)
        change (els.run σ).map _ = _
        rw [ho]
        rfl
      · refine .inr (.inr ⟨?_, htgt⟩)
        change (els.run σ).map _ = _
        rw [ho]
        rfl
    · rw [run_append_skip (m' := m) (k := 0) rfl]
      simp only [↓reduceIte]
      rcases iht σ base m hr capt (fun amount hd => room amount (.iteTrue hvc hd)) with
        ⟨o, m', base', amount, ho, htgt, hcost, hr', stack, hb, hg⟩ |
        ⟨ho, htgt⟩ | ⟨ho, htgt⟩
      · refine .inl ⟨⟨o.st.drop thn.ext, o.ext⟩, m', base', amount, ?_, ?_,
          .iteTrue hvc ho hcost, (hr'.drop thn.ext).meet _, stack, hb, hg⟩
        · change (thn.run σ).map _ = _
          rw [ho]
          rfl
        · change run (left ++ ([Instr.jump right.length] ++ right)) m = _
          rw [run_append_ok htgt]
          exact exec_length _ _
      · refine .inr (.inl ⟨?_, run_append_revert htgt⟩)
        change (thn.run σ).map _ = _
        rw [ho]
        rfl
      · refine .inr (.inr ⟨?_, target_append_fault htgt⟩)
        change (thn.run σ).map _ = _
        rw [ho]
        rfl
  · exact .inr (.inl ⟨by simp only [bind, Except.bind, hvc], run_append_revert hrunc⟩)

theorem StmtCert.correct {b L frame Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) :
    StmtSound hs L frame := by
  induction hs using StmtCert.rec
    (motive_2 := fun F G P code hp => ProgSound hp L frame) with
  | base hs => exact base_sound hs
  | block hp ih => exact block_sound hp ih
  | ite hc ht he iht ihe => exact ite_sound hc ht he iht ihe
  | nil F => exact nil_sound F
  | cons hs hp ihs ihp => exact cons_sound hs hp ihs ihp

theorem ProgCert.correct {b L frame Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) :
    ProgSound hp L frame := by
  induction hp using ProgCert.rec
    (motive_1 := fun F G s code hs => StmtSound hs L frame) with
  | base hs => exact base_sound hs
  | block hp ih => exact block_sound hp ih
  | ite hc ht he iht ihe => exact ite_sound hc ht he iht ihe
  | nil F => exact nil_sound F
  | cons hs hp ihs ihp => exact cons_sound hs hp ihs ihp

end Solidity.Evm.Memory.LoopScopes
