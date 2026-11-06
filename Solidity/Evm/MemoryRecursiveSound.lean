import Solidity.Evm.MemoryRecursiveCert
namespace Solidity.Evm.Memory.Recursive
variable {C : Contract}

def StmtSound {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) (L frame : Nat) : Prop :=
  ∀ (σ : State C Γ) (base : Nat → Fin W) (m : Machine),
    StateRepr L b frame F σ base m → b + hs.need ≤ frame →
    (∀ amount, StmtDemand hs σ amount → AllocationInput b frame amount σ base m) →
    LoopScopes.Result L b frame G σ base m (fun o amount => StmtCost hs σ o amount) (s.run σ) (run code m)

def ProgSound {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) (L frame : Nat) : Prop :=
  ∀ (σ : State C Γ) (base : Nat → Fin W) (m : Machine),
    StateRepr L b frame F σ base m → b + hp.need ≤ frame → Room hp frame σ base m →
    LoopScopes.Result L b frame G σ base m (fun o amount => Cost hp σ o amount) (P.run σ) (run code m)

private theorem base_sound {b L frame Γ Δ F G s code}
    (hs : LoopScopes.StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code) :
    StmtSound (.base hs) L frame := by
  intro σ base m repr cap room
  rcases hs.correct σ base m repr cap (fun amount demand=>room amount (.base demand)) with
    ⟨out,next,newBase,amount,sourceRun,targetRun,cost,represented,stack,bases,growth⟩ |
    ⟨sourceRun,targetRun⟩ | ⟨sourceRun,targetRun⟩
  · exact .inl ⟨out,next,newBase,amount,sourceRun,targetRun,.base cost,represented,stack,bases,growth⟩
  · exact .inr (.inl ⟨sourceRun,targetRun⟩)
  · exact .inr (.inr ⟨sourceRun,targetRun⟩)

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
  change LoopScopes.Result _ _ _ _ _ _ _ _ (TRun.ite c thn.ext thn.runR els.ext els.runR σ) _
  simp only [TRun.ite, conditionalCode, List.append_assoc]
  rcases hc.correct hr with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain rfl := hrc.bool_inv
    rw [run_append_ok hrunc, hvc]
    simp only [bind, Except.bind, Solidity.boolT]
    cases vc
    · rw [run_append_skip (m' := m) (k := left.length + 1) rfl,
        exec_skip_append]
      simp only [Bool.false_eq_true, ↓reduceIte]
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

/-- A real loop kit, with profile data computed from this actual body cert. -/
def loopKit {b Γ Δ F G c body cond code}
    (hc : ValFrag (C:=C) b (Γ:=Γ) F c cond)
    (hp : ProgCert b (Γ:=Γ) (Δ:=Δ) F G body code) (stable : G.restrict Γ=F) :
    RecursiveLift.Certificate b F c body cond code := ⟨hc,profile hp,stable⟩

theorem LoopPrefix.ofLift {b Γ Δ F G c body cond code}
    {hc : ValFrag (C:=C) b (Γ:=Γ) F c cond}
    {hp : ProgCert b (Γ:=Γ) (Δ:=Δ) F G body code} {stable : G.restrict Γ=F}
    {σ : State C Γ} {out amount} (h : RecursiveLift.Prefix (loopKit hc hp stable) σ out amount) :
    LoopPrefix hp c σ out amount := by
  induction h with
  | start => exact .start _ _ _
  | next before condition run cost ih => exact .next ih condition run cost

private theorem loop_sound {b L frame Γ Δ F G c body cond code}
    (a : LoopAnn C Γ) (hc : ValFrag b (Γ:=Γ) F c cond)
    (hp : ProgCert b (Γ:=Γ) (Δ:=Δ) F G body code) (stable : G.restrict Γ=F)
    (ih : ∀ L frame,ProgSound hp L frame) : StmtSound (.loop a hc hp stable) L frame := by
  intro σ base m repr cap room
  have bodySound : (loopKit hc hp stable).profile.Sound := by
    intro L frame σ base m repr cap room
    exact ih L frame σ base m repr cap room
  have capacity : b+hp.need≤frame := by
    change b+max Γ.length hp.need≤frame at cap
    omega
  have reached : RecursiveLift.Room (loopKit hc hp stable) frame σ base m := by
    intro out amount hpref condition spent demand
    exact room _ (.loopBody (LoopPrefix.ofLift hpref) condition demand)
  rcases (loopKit hc hp stable).correct bodySound a repr capacity reached with
    ⟨out,next,newBase,amount,sourceRun,targetRun,cost,represented,stack,bases,growth⟩ |
    ⟨sourceRun,targetRun⟩ | ⟨sourceRun,targetRun⟩
  · exact .inl ⟨out,next,newBase,amount,sourceRun,targetRun,.loop (LoopPrefix.ofLift cost),represented,stack,bases,growth⟩
  · exact .inr (.inl ⟨sourceRun,targetRun⟩)
  · exact .inr (.inr ⟨sourceRun,targetRun⟩)

/-- Closed mutual recursor: the final theorem exposes no body Sound law. -/
theorem StmtCert.correct {b L frame Γ Δ F G s code}
    (hs : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code) : StmtSound hs L frame := by
  exact (StmtCert.rec
    (motive_1 := fun F G s code hs=>∀ L frame,StmtSound hs L frame)
    (motive_2 := fun F G P code hp=>∀ L frame,ProgSound hp L frame)
    (fun hs L frame=>base_sound hs)
    (fun hp ih L frame=>block_sound hp (ih L frame))
    (fun hc ht he iht ihe L frame=>ite_sound hc ht he (iht L frame) (ihe L frame))
    (fun a hc hp stable ih L frame=>loop_sound a hc hp stable ih)
    (fun F L frame=>nil_sound F)
    (fun hs hp ihs ihp L frame=>cons_sound hs hp (ihs L frame) (ihp L frame))
    hs) L frame

theorem ProgCert.correct {b L frame Γ Δ F G P code}
    (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code) : ProgSound hp L frame := by
  exact (ProgCert.rec
    (motive_1 := fun F G s code hs=>∀ L frame,StmtSound hs L frame)
    (motive_2 := fun F G P code hp=>∀ L frame,ProgSound hp L frame)
    (fun hs L frame=>base_sound hs)
    (fun hp ih L frame=>block_sound hp (ih L frame))
    (fun hc ht he iht ihe L frame=>ite_sound hc ht he (iht L frame) (ihe L frame))
    (fun a hc hp stable ih L frame=>loop_sound a hc hp stable ih)
    (fun F L frame=>nil_sound F)
    (fun hs hp ihs ihp L frame=>cons_sound hs hp (ihs L frame) (ihp L frame))
    hp) L frame

theorem ProgCert.profile_sound {b Γ Δ F G P code}
    (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code) : (profile hp).Sound := by
  intro L frame σ base m repr cap room
  exact hp.correct σ base m repr cap room

end Solidity.Evm.Memory.Recursive
