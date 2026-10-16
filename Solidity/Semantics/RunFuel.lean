import Solidity.Semantics.RunWk

/-!
# The typed run with fuel

`Prog.run` iterates a loop until it is done (`TLoop.run`, `Classical` in
the kernel, `runImpl` compiled, which heeds no heartbeats): neither the
kernel nor a search can run a loop bounded by an argument at `2^256 - 1`.
`Stmt.runF n` is the typed run with each loop entered at most `n`
iterations (`TLoop.iterN`); a loop not done by then is `diverge`, which
no statement catches, so the run's outcome is the typed run's wherever it
is not `diverge` (`Prog.runF_approx`, by `TRes.Approx`).  It is the typed
run's recursor form (`Stmt.runR`), only the loop changed, with its
compiled twin (`Stmt.runFC`).
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-- `a` is `b`, or `diverge`: what a run with fuel says of the run. -/
def TRes.Approx {α : Type} (a b : TRes α) : Prop := a = .error .diverge ∨ a = b

/-- Two steps that agree as `TRes.Approx` says, from every state. -/
def TStep.Approx {Γ Γ' : Ctx} (f g : TStep C Γ Γ') : Prop := ∀ σ, TRes.Approx (f σ) (g σ)

theorem TRes.Approx.refl {α : Type} (a : TRes α) : TRes.Approx a a := .inr rfl

theorem TRes.Approx.map {α β : Type} {a b : TRes α} (f : α → β) (h : TRes.Approx a b) :
    TRes.Approx (a.map f) (b.map f) := by
  rcases h with h | h
  · exact .inl (by rw [h]; rfl)
  · exact .inr (by rw [h])

theorem TRes.Approx.bind {α β : Type} {a b : TRes α} {f g : α → TRes β} (h : TRes.Approx a b)
    (hf : ∀ x, TRes.Approx (f x) (g x)) : TRes.Approx (a >>= f) (b >>= g) := by
  rcases h with h | h
  · exact .inl (by rw [h]; rfl)
  · subst h
    cases a with
    | error e => exact .inr rfl
    | ok x => exact hf x

theorem TRes.Approx.eq {α : Type} {a b : TRes α} (h : TRes.Approx a b)
    (hd : a ≠ .error .diverge) : a = b := h.resolve_left hd

namespace TLoop

variable {α : Type}

/-- At most `n` iterations: the loop's outcome, or `diverge` when they do
not finish it. -/
def runF (body : α → TRes α) (c : α → TRes Bool) (n : Nat) (σ : α) : TRes α :=
  match iterN body c n σ with
  | .inr r => r
  | .inl _ => .error .diverge

/-- One iteration with a body that agrees: the same, but where the body
said `diverge`. -/
theorem step_approx {f g : α → TRes α} {c : α → TRes Bool}
    (hfg : ∀ x, TRes.Approx (f x) (g x)) (σ : α) :
    (∀ r, step f c σ = .inr r → r ≠ .error .diverge → step g c σ = .inr r) ∧
      (∀ τ, step f c σ = .inl τ → step g c σ = .inl τ) := by
  unfold step
  cases c σ with
  | error e => exact ⟨fun _ h _ => h, fun _ h => h⟩
  | ok b =>
    cases b with
    | false => exact ⟨fun _ h _ => h, fun _ h => h⟩
    | true =>
      simp only
      rcases hfg σ with h' | h'
      · rw [h']
        refine ⟨fun r h hr => ?_, fun _ h => nomatch h⟩
        cases h
        exact absurd rfl hr
      · rw [← h']
        exact ⟨fun _ h _ => h, fun _ h => h⟩

/-- Where a step with fuel agrees with the body, so do its iterations. -/
theorem iterN_approx {f g : α → TRes α} {c : α → TRes Bool}
    (hfg : ∀ x, TRes.Approx (f x) (g x)) :
    (n : Nat) → ∀ (σ : α) (r : TRes α), iterN f c n σ = .inr r → r ≠ .error .diverge →
      ∃ m, iterN g c m σ = .inr r
  | 0, _, _, h, _ => by simp only [iterN, reduceCtorEq] at h
  | n + 1, σ, r, h, hr => by
    simp only [iterN] at h
    cases hs : step f c σ with
    | inr r' =>
      rw [hs] at h
      cases h
      exact ⟨1, by simp only [iterN, (step_approx hfg σ).1 r hs hr]⟩
    | inl τ =>
      rw [hs] at h
      obtain ⟨m, hm⟩ := iterN_approx hfg n τ r h hr
      exact ⟨m + 1, by simp only [iterN, (step_approx hfg σ).2 τ hs]; exact hm⟩

/-- A loop with fuel agrees with the loop. -/
theorem runF_approx {f g : α → TRes α} {c : α → TRes Bool}
    (hfg : ∀ x, TRes.Approx (f x) (g x)) (n : Nat) (σ : α) :
    TRes.Approx (runF f c n σ) (run g c σ) := by
  unfold runF
  split
  · rename_i r h
    by_cases hr : r = .error .diverge
    · exact .inl hr
    · obtain ⟨m, hm⟩ := iterN_approx hfg n σ r h hr
      exact .inr (run_of_iterN hm).symm
  · exact .inl rfl

end TLoop

namespace TRun

/-- `while` with at most `n` iterations. -/
def loopF {Γ₁ : Ctx} (n : Nat) (c : Val C Γ .bool) (h : Ext Γ Γ₁) (body : TStep C Γ Γ₁) :
    TStep C Γ Γ :=
  fun σ => TLoop.runF
    (fun o : Out C σ.H Γ => (body o.st).map fun o' => ⟨o'.st.drop h, o.ext.trans o'.ext⟩)
    (fun o => c.evalT o.st) n ⟨σ, List.prefix_refl _⟩

theorem loopF_approx {Γ₁ : Ctx} (n : Nat) (c : Val C Γ .bool) (h : Ext Γ Γ₁)
    {f g : TStep C Γ Γ₁} (hfg : TStep.Approx f g) :
    TStep.Approx (loopF n c h f) (loop c h g) := fun σ => by
  unfold loopF loop
  exact TLoop.runF_approx (fun (o : Out C σ.H Γ) => (hfg o.st).map _) n _

theorem ite_approx {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) (h₂ : Ext Γ Γ₂)
    {f g : TStep C Γ Γ₁} {f' g' : TStep C Γ Γ₂} (hf : TStep.Approx f g)
    (hf' : TStep.Approx f' g') : TStep.Approx (ite c h₁ f h₂ f') (ite c h₁ g h₂ g') := fun σ =>
  (TRes.Approx.refl _).bind fun v => by
    cases boolT v
    · exact (hf' σ).map _
    · exact (hf σ).map _

theorem call_approx {Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) {f g : TStep C (rs ++ ps) Γf} (hfg : TStep.Approx f g) :
    TStep.Approx (call args ret hb f) (call args ret hb g) := fun _ =>
  (TRes.Approx.refl _).bind fun _ => (hfg _).bind fun _ => .refl _

theorem tryCall_approx {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (h₂ : Ext Γ Γ₂) (code : CodeBinder κ) (h₃ : Ext (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) {ok ok' : TStep C (ρ ++ Γ) Γ₁} {err err' : TStep C Γ Γ₂}
    {pnc pnc' : TStep C (κ ++ Γ) Γ₃} {oth oth' : TStep C Γ Γ₄} (hok : TStep.Approx ok ok')
    (herr : TStep.Approx err err') (hpnc : TStep.Approx pnc pnc') (hoth : TStep.Approx oth oth') :
    TStep.Approx (tryCall ec rets h₁ ok h₂ err code h₃ pnc h₄ oth)
      (tryCall ec rets h₁ ok' h₂ err' code h₃ pnc' h₄ oth') := fun _ => by
  simp only [tryCall]
  split
  · exact .refl _
  · exact (TRes.Approx.refl _).bind fun _ => (hok _).map _
  · exact (herr _).map _
  · exact (hpnc _).map _
  · exact (hoth _).map _

theorem block_approx {Γ₁ : Ctx} (h : Ext Γ Γ₁) {f g : TStep C Γ Γ₁} (hfg : TStep.Approx f g) :
    TStep.Approx (block h f) (block h g) := fun σ => (hfg σ).map _

theorem seq_approx {Γ₁ Γ₂ : Ctx} {s s' : TStep C Γ Γ₁} {P P' : TStep C Γ₁ Γ₂}
    (hs : TStep.Approx s s') (hP : TStep.Approx P P') : TStep.Approx (seq s P) (seq s' P') :=
  fun σ => by
    simp only [seq]
    rcases hs σ with h | h
    · rw [h]; exact .inl rfl
    · rw [h]
      cases s' σ with
      | error e => exact .refl _
      | ok o => exact (hP o.st).map _

end TRun

/-! ## Running a program with fuel -/

mutual

/-- The compiled typed run with fuel of a statement. -/
def Stmt.runFC (n : Nat) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → TStep C Γ Γ'
  | _, _, .assign l r => TRun.assign l r
  | _, _, .rebind i r => TRun.rebind i r
  | _, _, .assignLocal i r => TRun.assignLocal i r
  | _, _, .declLocal p _ init => TRun.declLocal p init
  | _, _, .declStorage R _ init => TRun.declStorage R init
  | _, _, .opAssign op _ _ l r => TRun.opAssign op l r
  | _, _, .incDec op _ l => TRun.incDec op l
  | _, _, .pushOpAssign op _ _ b r => TRun.pushOpAssign op b r
  | _, _, .pushIncDec op _ b => TRun.pushIncDec op b
  | _, _, .assignIncDec i op _ l _ => TRun.assignIncDec i op l
  | _, _, .assignLocalPush i b => TRun.assignLocalPush i b
  | _, _, .push b v _ => TRun.push b v
  | _, _, .pop b => TRun.pop b
  | _, _, .transfer r a => TRun.transfer r a
  | _, _, .send pv r a => TRun.send pv r a
  | _, _, .declMem R _ init _ hm => TRun.declMem R init hm
  | _, _, .rebindMem i r => TRun.rebindMem i r
  | _, _, .assignFromMem l p => TRun.assignFromMem l p
  | _, _, .assignMem l r => TRun.assignMem l r
  | _, _, .delete l => TRun.delete l
  | _, _, .deleteMem p _ => TRun.deleteMem p
  | _, _, .assignNew l n' h => TRun.assignNew l n' h
  | _, _, .ite c thn els => TRun.ite c thn.ext (Prog.runFC n thn) els.ext (Prog.runFC n els)
  | _, _, .require c => TRun.require c
  | _, _, .assert c => TRun.assert c
  | _, _, .revert => fun _ => .error .revert
  | _, _, .call _ args ret body => TRun.call args ret body.ext (Prog.runFC n body)
  | _, _, .callReceiver _ args r body op =>
    TRun.callReceiver args r body.ext (Prog.runFC n body) op
  | _, _, .callReceiverPush _ args r body code value =>
    TRun.callReceiverPush args r body.ext (Prog.runFC n body)
      code.ext (Prog.runFC n code) value
  | _, _, .tryCall call rets ok err code pnc other =>
    TRun.tryCall call rets ok.ext (Prog.runFC n ok) err.ext (Prog.runFC n err) code pnc.ext
      (Prog.runFC n pnc) other.ext (Prog.runFC n other)
  | _, _, .loop _ c body => TRun.loopF n c body.ext (Prog.runFC n body)
  | _, _, .block body => TRun.block body.ext (Prog.runFC n body)

/-- The compiled typed run with fuel of a sequence. -/
def Prog.runFC (n : Nat) : {Γ Γ' : Ctx} → Prog C Γ Γ' → TStep C Γ Γ'
  | _, _, .nil => TRun.nil
  | _, _, .cons s P => TRun.seq (Stmt.runFC n s) (Prog.runFC n P)

end

/-- The typed run of a statement with each loop entered at most `n`
iterations, by its recursor (`Stmt.runR`'s, the loop `TRun.loopF`). -/
@[implemented_by Stmt.runFC]
def Stmt.runF (n : Nat) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : TStep C Γ Γ' :=
  Stmt.rec (motive_1 := fun Γ Γ' _ => TStep C Γ Γ') (motive_2 := fun Γ Γ' _ => TStep C Γ Γ')
    (fun l r => TRun.assign l r) (fun i r => TRun.rebind i r) (fun i r => TRun.assignLocal i r)
    (fun p _ init => TRun.declLocal p init) (fun R _ init => TRun.declStorage R init)
    (fun op _ _ l r => TRun.opAssign op l r) (fun op _ l => TRun.incDec op l)
    (fun i op _ l _ => TRun.assignIncDec i op l) (fun i b => TRun.assignLocalPush i b)
    (fun b v _ => TRun.push b v)
    (fun b => TRun.pop b) (fun r a => TRun.transfer r a) (fun pv r a => TRun.send pv r a)
    (fun R _ init _ hm => TRun.declMem R init hm) (fun i r => TRun.rebindMem i r)
    (fun l p => TRun.assignFromMem l p) (fun l r => TRun.assignMem l r)
    (fun l => TRun.delete l) (fun p _ => TRun.deleteMem p) (fun l n h => TRun.assignNew l n h)
    (fun c thn els ihThn ihEls => TRun.ite c thn.ext ihThn els.ext ihEls)
    (fun c => TRun.require c) (fun c => TRun.assert c) (fun _ => .error .revert)
    (fun _ args ret body ih => TRun.call args ret body.ext ih)
    (fun call rets ok err code pnc other ihOk ihErr ihPnc ihOther =>
      TRun.tryCall call rets ok.ext ihOk err.ext ihErr code pnc.ext ihPnc other.ext ihOther)
    (fun _ c body ih => TRun.loopF n c body.ext ih) (fun body ih => TRun.block body.ext ih)
    (fun op _ _ b r => TRun.pushOpAssign op b r) (fun op _ b => TRun.pushIncDec op b)
    (fun _ args r body op ih => TRun.callReceiver args r body.ext ih op)
    (fun _ args r body code value ihBody ihCode =>
      TRun.callReceiverPush args r body.ext ihBody code.ext ihCode value)
    TRun.nil (fun _ _ ihS ihP => TRun.seq ihS ihP) s

/-- The typed run of a sequence with fuel, by its recursor. -/
@[implemented_by Prog.runFC]
def Prog.runF (n : Nat) {Γ Γ' : Ctx} (P : Prog C Γ Γ') : TStep C Γ Γ' :=
  Prog.rec (motive_1 := fun Γ Γ' _ => TStep C Γ Γ') (motive_2 := fun Γ Γ' _ => TStep C Γ Γ')
    (fun l r => TRun.assign l r) (fun i r => TRun.rebind i r) (fun i r => TRun.assignLocal i r)
    (fun p _ init => TRun.declLocal p init) (fun R _ init => TRun.declStorage R init)
    (fun op _ _ l r => TRun.opAssign op l r) (fun op _ l => TRun.incDec op l)
    (fun i op _ l _ => TRun.assignIncDec i op l) (fun i b => TRun.assignLocalPush i b)
    (fun b v _ => TRun.push b v)
    (fun b => TRun.pop b) (fun r a => TRun.transfer r a) (fun pv r a => TRun.send pv r a)
    (fun R _ init _ hm => TRun.declMem R init hm) (fun i r => TRun.rebindMem i r)
    (fun l p => TRun.assignFromMem l p) (fun l r => TRun.assignMem l r)
    (fun l => TRun.delete l) (fun p _ => TRun.deleteMem p) (fun l n h => TRun.assignNew l n h)
    (fun c thn els ihThn ihEls => TRun.ite c thn.ext ihThn els.ext ihEls)
    (fun c => TRun.require c) (fun c => TRun.assert c) (fun _ => .error .revert)
    (fun _ args ret body ih => TRun.call args ret body.ext ih)
    (fun call rets ok err code pnc other ihOk ihErr ihPnc ihOther =>
      TRun.tryCall call rets ok.ext ihOk err.ext ihErr code pnc.ext ihPnc other.ext ihOther)
    (fun _ c body ih => TRun.loopF n c body.ext ih) (fun body ih => TRun.block body.ext ih)
    (fun op _ _ b r => TRun.pushOpAssign op b r) (fun op _ b => TRun.pushIncDec op b)
    (fun _ args r body op ih => TRun.callReceiver args r body.ext ih op)
    (fun _ args r body code value ihBody ihCode =>
      TRun.callReceiverPush args r body.ext ihBody code.ext ihCode value)
    TRun.nil (fun _ _ ihS ihP => TRun.seq ihS ihP) P

mutual

theorem Stmt.runF_eq (n : Nat) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    Stmt.runF n s = Stmt.runFC n s
  | _, _, .ite c thn els => by
    show TRun.ite c thn.ext (thn.runF n) els.ext (els.runF n) =
      TRun.ite c thn.ext (thn.runFC n) els.ext (els.runFC n)
    rw [Prog.runF_eq n thn, Prog.runF_eq n els]
  | _, _, .call f args ret body => by
    show TRun.call args ret body.ext (body.runF n) = TRun.call args ret body.ext (body.runFC n)
    rw [Prog.runF_eq n body]
  | _, _, .callReceiver _ args r body op => by
    change TRun.callReceiver args r body.ext (body.runF n) op =
      TRun.callReceiver args r body.ext (body.runFC n) op
    rw [Prog.runF_eq n body]
  | _, _, .callReceiverPush _ args r body code value => by
    change TRun.callReceiverPush args r body.ext (body.runF n) code.ext (code.runF n) value =
      TRun.callReceiverPush args r body.ext (body.runFC n) code.ext (code.runFC n) value
    rw [Prog.runF_eq n body, Prog.runF_eq n code]
  | _, _, .tryCall call rets ok err code pnc other => by
    show TRun.tryCall call rets ok.ext (ok.runF n) err.ext (err.runF n) code pnc.ext
        (pnc.runF n) other.ext (other.runF n) =
      TRun.tryCall call rets ok.ext (ok.runFC n) err.ext (err.runFC n) code pnc.ext
        (pnc.runFC n) other.ext (other.runFC n)
    rw [Prog.runF_eq n ok, Prog.runF_eq n err, Prog.runF_eq n pnc, Prog.runF_eq n other]
  | _, _, .loop a c body => by
    show TRun.loopF n c body.ext (body.runF n) = TRun.loopF n c body.ext (body.runFC n)
    rw [Prog.runF_eq n body]
  | _, _, .block body => by
    show TRun.block body.ext (body.runF n) = TRun.block body.ext (body.runFC n)
    rw [Prog.runF_eq n body]
  | _, _, .assign .. | _, _, .rebind .. | _, _, .assignLocal .. | _, _, .declLocal ..
  | _, _, .declStorage .. | _, _, .opAssign .. | _, _, .incDec .. | _, _, .assignIncDec ..
  | _, _, .pushOpAssign .. | _, _, .pushIncDec ..
  | _, _, .assignLocalPush .. | _, _, .push .. | _, _, .pop .. | _, _, .transfer ..
  | _, _, .send .. | _, _, .declMem ..
  | _, _, .rebindMem .. | _, _, .assignFromMem .. | _, _, .assignMem .. | _, _, .delete ..
  | _, _, .deleteMem .. | _, _, .assignNew .. | _, _, .require .. | _, _, .assert ..
  | _, _, .revert => rfl

theorem Prog.runF_eq (n : Nat) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    Prog.runF n P = Prog.runFC n P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    show TRun.seq (s.runF n) (P.runF n) = TRun.seq (s.runFC n) (P.runFC n)
    rw [Stmt.runF_eq n s, Prog.runF_eq n P]

end

mutual

/-- **A run with fuel agrees with the typed run.** -/
theorem Stmt.runF_approx (n : Nat) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    TStep.Approx (Stmt.runF n s) (Stmt.runR s)
  | _, _, .ite c thn els =>
    TRun.ite_approx c thn.ext els.ext (Prog.runF_approx n thn) (Prog.runF_approx n els)
  | _, _, .call _ args ret body => TRun.call_approx args ret body.ext (Prog.runF_approx n body)
  | _, _, .callReceiver _ args r body op => by
    intro σ
    exact (TRun.call_approx args (.storage _ r) body.ext (Prog.runF_approx n body) σ).bind
      fun _ => .refl _
  | _, _, .callReceiverPush _ args r body code value => by
    intro σ
    change TRes.Approx (TRun.callReceiverPush args r body.ext (body.runF n)
      code.ext (code.runF n) value σ) (TRun.callReceiverPush args r body.ext body.runR
      code.ext code.runR value σ)
    unfold TRun.callReceiverPush
    apply (TRun.call_approx args (.storage _ r) body.ext (Prog.runF_approx n body) σ).bind
    intro a
    apply TRes.Approx.map
    unfold TRun.afterReceiverPrefix TRun.pushAfterPrefix
    exact (TRes.Approx.refl _).bind fun _ => (Prog.runF_approx n code _).bind fun _ => .refl _
  | _, _, .tryCall call rets ok err code pnc other =>
    TRun.tryCall_approx call rets ok.ext err.ext code pnc.ext other.ext
      (Prog.runF_approx n ok) (Prog.runF_approx n err) (Prog.runF_approx n pnc)
      (Prog.runF_approx n other)
  | _, _, .loop _ c body => TRun.loopF_approx n c body.ext (Prog.runF_approx n body)
  | _, _, .block body => TRun.block_approx body.ext (Prog.runF_approx n body)
  | _, _, .assign .. | _, _, .rebind .. | _, _, .assignLocal .. | _, _, .declLocal ..
  | _, _, .declStorage .. | _, _, .opAssign .. | _, _, .incDec .. | _, _, .assignIncDec ..
  | _, _, .pushOpAssign .. | _, _, .pushIncDec ..
  | _, _, .assignLocalPush .. | _, _, .push .. | _, _, .pop .. | _, _, .transfer ..
  | _, _, .send .. | _, _, .declMem ..
  | _, _, .rebindMem .. | _, _, .assignFromMem .. | _, _, .assignMem .. | _, _, .delete ..
  | _, _, .deleteMem .. | _, _, .assignNew .. | _, _, .require .. | _, _, .assert ..
  | _, _, .revert => fun _ => .refl _

theorem Prog.runF_approx (n : Nat) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    TStep.Approx (Prog.runF n P) (Prog.runR P)
  | _, _, .nil => fun _ => .refl _
  | _, _, .cons s P => TRun.seq_approx (Stmt.runF_approx n s) (Prog.runF_approx n P)

end

/-- The frames after a program, run with fuel (`Frames.run`). -/
def Frames.runF (n : Nat) {Γ₀ : Ctx} : {Γ : Ctx} → (σ : State C Γ) → Frames C Γ Γ₀ →
    TRes (Out C σ.H Γ₀)
  | _, σ, .nil => .ok ⟨σ, List.prefix_refl _⟩
  | _, σ, .seq ω κ => TRun.seq (fun τ => Prog.runF n ω τ) (fun τ => Frames.runF n τ κ) σ
  | _, σ, .pop _ h κ => Frames.runF n (σ.drop h) κ
  | _, σ, .drop h κ => Frames.runF n (σ.thin h) κ

theorem Frames.runF_approx (n : Nat) {Γ₀ : Ctx} : {Γ : Ctx} → (σ : State C Γ) →
    (κ : Frames C Γ Γ₀) → TRes.Approx (Frames.runF n σ κ) (Frames.run σ κ)
  | _, _, .nil => .refl _
  | _, σ, .seq ω κ =>
    TRun.seq_approx (Prog.runF_approx n ω) (fun τ => Frames.runF_approx n τ κ) σ
  | _, σ, .pop _ h κ => Frames.runF_approx n (σ.drop h) κ
  | _, σ, .drop h κ => Frames.runF_approx n (σ.thin h) κ

end Solidity
