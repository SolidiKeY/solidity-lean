import Solidity.Semantics.Core.TypedRunWk

/-!
# The typed run with fuel

`Prog.trun` iterates a loop until it is done (`TLoop.run`, `Classical` in
the kernel, `runImpl` compiled, which heeds no heartbeats): neither the
kernel nor a search can run a loop bounded by an argument at `2^256 - 1`.
`Stmt.trunF n` is the typed run with each loop entered at most `n`
iterations (`TLoop.iterN`); a loop not done by then is `diverge`, which
no statement catches, so the run's outcome is the typed run's wherever it
is not `diverge` (`Prog.trunF_sound`, by `TRes.Approx`).  It is the typed
run's recursor form (`Stmt.trunR`), only the loop changed, with its
compiled twin (`Stmt.trunFC`).
-/

namespace Solidity.Core

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
  · exact (TRes.Approx.refl _).bind fun _ => (hpnc _).map _
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
def Stmt.trunFC (n : Nat) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → TStep C Γ Γ'
  | _, _, .assign l r => TRun.assign l r
  | _, _, .rebind i r => TRun.rebind i r
  | _, _, .assignLocal i r => TRun.assignLocal i r
  | _, _, .declLocal p _ init => TRun.declLocal p init
  | _, _, .declStorage R _ init => TRun.declStorage R init
  | _, _, .opAssign op _ _ l r => TRun.opAssign op l r
  | _, _, .incDec op _ l => TRun.incDec op l
  | _, _, .assignIncDec i op _ l _ => TRun.assignIncDec i op l
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
  | _, _, .ite c thn els => TRun.ite c thn.ext (Prog.trunFC n thn) els.ext (Prog.trunFC n els)
  | _, _, .require c => TRun.require c
  | _, _, .assert c => TRun.assert c
  | _, _, .revert => fun _ => .error .revert
  | _, _, .call _ args ret body => TRun.call args ret body.ext (Prog.trunFC n body)
  | _, _, .tryCall call rets ok err code pnc other =>
    TRun.tryCall call rets ok.ext (Prog.trunFC n ok) err.ext (Prog.trunFC n err) code pnc.ext
      (Prog.trunFC n pnc) other.ext (Prog.trunFC n other)
  | _, _, .loop _ c body => TRun.loopF n c body.ext (Prog.trunFC n body)
  | _, _, .block body => TRun.block body.ext (Prog.trunFC n body)

/-- The compiled typed run with fuel of a sequence. -/
def Prog.trunFC (n : Nat) : {Γ Γ' : Ctx} → Prog C Γ Γ' → TStep C Γ Γ'
  | _, _, .nil => TRun.nil
  | _, _, .cons s P => TRun.seq (Stmt.trunFC n s) (Prog.trunFC n P)

end

/-- The typed run of a statement with each loop entered at most `n`
iterations, by its recursor (`Stmt.trunR`'s, the loop `TRun.loopF`). -/
@[implemented_by Stmt.trunFC]
def Stmt.trunF (n : Nat) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : TStep C Γ Γ' :=
  Stmt.rec (motive_1 := fun Γ Γ' _ => TStep C Γ Γ') (motive_2 := fun Γ Γ' _ => TStep C Γ Γ')
    (fun l r => TRun.assign l r) (fun i r => TRun.rebind i r) (fun i r => TRun.assignLocal i r)
    (fun p _ init => TRun.declLocal p init) (fun R _ init => TRun.declStorage R init)
    (fun op _ _ l r => TRun.opAssign op l r) (fun op _ l => TRun.incDec op l)
    (fun i op _ l _ => TRun.assignIncDec i op l) (fun b v _ => TRun.push b v)
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
    TRun.nil (fun _ _ ihS ihP => TRun.seq ihS ihP) s

/-- The typed run of a sequence with fuel, by its recursor. -/
@[implemented_by Prog.trunFC]
def Prog.trunF (n : Nat) {Γ Γ' : Ctx} (P : Prog C Γ Γ') : TStep C Γ Γ' :=
  Prog.rec (motive_1 := fun Γ Γ' _ => TStep C Γ Γ') (motive_2 := fun Γ Γ' _ => TStep C Γ Γ')
    (fun l r => TRun.assign l r) (fun i r => TRun.rebind i r) (fun i r => TRun.assignLocal i r)
    (fun p _ init => TRun.declLocal p init) (fun R _ init => TRun.declStorage R init)
    (fun op _ _ l r => TRun.opAssign op l r) (fun op _ l => TRun.incDec op l)
    (fun i op _ l _ => TRun.assignIncDec i op l) (fun b v _ => TRun.push b v)
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
    TRun.nil (fun _ _ ihS ihP => TRun.seq ihS ihP) P

mutual

/-- **A run with fuel agrees with the typed run.** -/
theorem Stmt.trunF_approx (n : Nat) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    TStep.Approx (Stmt.trunF n s) (Stmt.trunR s)
  | _, _, .ite c thn els =>
    TRun.ite_approx c thn.ext els.ext (Prog.trunF_approx n thn) (Prog.trunF_approx n els)
  | _, _, .call _ args ret body => TRun.call_approx args ret body.ext (Prog.trunF_approx n body)
  | _, _, .tryCall call rets ok err code pnc other =>
    TRun.tryCall_approx call rets ok.ext err.ext code pnc.ext other.ext
      (Prog.trunF_approx n ok) (Prog.trunF_approx n err) (Prog.trunF_approx n pnc)
      (Prog.trunF_approx n other)
  | _, _, .loop _ c body => TRun.loopF_approx n c body.ext (Prog.trunF_approx n body)
  | _, _, .block body => TRun.block_approx body.ext (Prog.trunF_approx n body)
  | _, _, .assign .. | _, _, .rebind .. | _, _, .assignLocal .. | _, _, .declLocal ..
  | _, _, .declStorage .. | _, _, .opAssign .. | _, _, .incDec .. | _, _, .assignIncDec ..
  | _, _, .push .. | _, _, .pop .. | _, _, .transfer .. | _, _, .send .. | _, _, .declMem ..
  | _, _, .rebindMem .. | _, _, .assignFromMem .. | _, _, .assignMem .. | _, _, .delete ..
  | _, _, .deleteMem .. | _, _, .assignNew .. | _, _, .require .. | _, _, .assert ..
  | _, _, .revert => fun _ => .refl _

theorem Prog.trunF_approx (n : Nat) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    TStep.Approx (Prog.trunF n P) (Prog.trunR P)
  | _, _, .nil => fun _ => .refl _
  | _, _, .cons s P => TRun.seq_approx (Stmt.trunF_approx n s) (Prog.trunF_approx n P)

end

/-- The frames after a program, run with fuel (`Frames.trun`). -/
def Frames.trunF (n : Nat) {Γ₀ : Ctx} : {Γ : Ctx} → (σ : TState C Γ) → Frames C Γ Γ₀ →
    TRes (Out C σ.H Γ₀)
  | _, σ, .nil => .ok ⟨σ, List.prefix_refl _⟩
  | _, σ, .seq ω κ => TRun.seq (fun τ => Prog.trunF n ω τ) (fun τ => Frames.trunF n τ κ) σ
  | _, σ, .pop _ h κ => Frames.trunF n (σ.drop h) κ
  | _, σ, .drop h κ => Frames.trunF n (σ.thin h) κ

theorem Frames.trunF_approx (n : Nat) {Γ₀ : Ctx} : {Γ : Ctx} → (σ : TState C Γ) →
    (κ : Frames C Γ Γ₀) → TRes.Approx (Frames.trunF n σ κ) (Frames.trun σ κ)
  | _, _, .nil => .refl _
  | _, σ, .seq ω κ =>
    TRun.seq_approx (Prog.trunF_approx n ω) (fun τ => Frames.trunF_approx n τ κ) σ
  | _, σ, .pop _ h κ => Frames.trunF_approx n (σ.drop h) κ
  | _, σ, .drop h κ => Frames.trunF_approx n (σ.thin h) κ

end Solidity.Core
