import Solidity.Correctness.Panic.Provenance.Eval
import Solidity.Semantics.Panic.Run.Control

/-!
# Panic code provenance: the step leaves of the runner

The functions of `Semantics/Panic/Run/{Loop,Calls,Control}.lean` keep every
halt coded. The loop engine, the call machinery and the control combinators
build no intrinsic halt of their own except `Run.assert`, whose halt is raised
by `evalProducer (.assertion _)`; the others only pass on halts of their
arguments. A combinator taking `Step`s is coded when every argument step is
coded at every state (`StepCoded`).

`catchHalt` hands a caught intrinsic halt to its panic handler as
`codeWord code`, which for a coded halt is the word of the retained site's
code (`catchHalt_coded_intrinsic`); what escapes is a handler's outcome or
`exhausted`/`diverge`. `haltBytes` and `catchBytes` never fail intrinsically.
-/

namespace Solidity.Correctness.Panic

open Solidity.Semantics.Panic

/-- A step whose every failure, from every state, is coded. -/
def StepCoded {C : Contract} {Γ Δ : Ctx} (s : Step C Γ Δ) : Prop :=
  ∀ σ, ErrCoded (s σ)

theorem ErrCoded.exhausted {α : Type} : ErrCoded (.error .exhausted : EvalResult α) :=
  ErrCoded.error _ fun _ _ e => nomatch e

theorem ErrCoded.diverge {α : Type} : ErrCoded (.error .diverge : EvalResult α) :=
  ErrCoded.error _ fun _ _ e => nomatch e

/-! ## The loop engine -/

namespace Loop

variable {α : Type} {body : α → EvalResult α} {c : α → EvalResult Bool}

/-- One loop step ends only with a condition or body result. -/
theorem step_coded (hb : ∀ σ, ErrCoded (body σ)) (hc : ∀ σ, ErrCoded (c σ)) (σ : α)
    {r : EvalResult α} (h : Loop.step body c σ = .inr r) : ErrCoded r := by
  unfold Loop.step at h
  cases hcσ : c σ with
  | error halt =>
    rw [hcσ] at h
    cases h
    exact fun _ e => by cases e; exact hc σ _ hcσ
  | ok b =>
    rw [hcσ] at h
    cases b with
    | false => cases h; exact ErrCoded.ok _
    | true =>
      cases hbσ : body σ with
      | error halt =>
        rw [hbσ] at h
        cases h
        exact fun _ e => by cases e; exact hb σ _ hbσ
      | ok τ => rw [hbσ] at h; cases h

/-- A loop with a coded body and condition at every state is coded. -/
theorem run_coded (hb : ∀ σ, ErrCoded (body σ)) (hc : ∀ σ, ErrCoded (c σ)) (σ : α) :
    ErrCoded (Loop.run body c σ) :=
  Loop.run_induct (P := fun _ => True) (Q := ErrCoded) trivial
    (fun τ _ => by
      cases h : Loop.step body c τ with
      | inl _ => trivial
      | inr r => exact step_coded hb hc τ h)
    ErrCoded.diverge

/-- The terminal result of a halting loop is coded. -/
theorem iterN_coded (hb : ∀ σ, ErrCoded (body σ)) (hc : ∀ σ, ErrCoded (c σ))
    {n : Nat} {σ : α} {r : EvalResult α} (h : Loop.iterN body c n σ = .inr r) :
    ErrCoded r :=
  Loop.run_of_iterN h ▸ run_coded hb hc σ

end Loop

/-! ## Calls -/

variable {C : Contract} {Γ : Ctx}

open ErrCoded in
theorem args_coded (σ : State C Γ) {ps : Ctx} (as : Args C Γ ps) :
    ErrCoded (args σ as) := by
  induction as with
  | nil => exact ok _
  | snoc as p name e ih => exact bind ih fun _ => bind (value_coded σ e) fun _ => ok _
  | snocStorage as R name e ih => exact bind ih fun _ => bind (path_coded σ e) fun _ => ok _
  | snocMemory as R name e ih => exact bind ih fun _ => bind (mpath_coded σ e) fun _ => ok _

open ErrCoded in
theorem decode_coded {H : HTy} {ρ : Ctx} (bs : Binders ρ) (vs : List Semantics.Word) :
    ErrCoded (decode (C := C) (H := H) bs vs) := by
  induction bs generalizing vs with
  | nil => exact ok _
  | snoc bs p name ih =>
    refine bind (ih vs) fun (e, rest) => ?_
    cases rest with
    | nil => exact revert
    | cons v rest => exact bind (ofOpt _) fun _ => ok _

namespace Run

open ErrCoded in
/-- An internal call with a coded body is coded. -/
theorem call_coded {Γ' ps rs Γf : Ctx} (as : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) {body : Step C (rs ++ ps) Γf} (hbody : StepCoded body) :
    StepCoded (Run.call as ret hb body) := fun σ =>
  bind (args_coded σ as) fun _ => bind (hbody _) fun _ => ok _

/-- Halt bytes fail only with a resource failure. -/
theorem haltBytes_coded (halt : Halt Raised) : ErrCoded (Run.haltBytes halt) := by
  cases halt with
  | exhausted => exact ErrCoded.exhausted
  | diverge => exact ErrCoded.diverge
  | _ => exact ErrCoded.ok _

/-- Catching passes on a handler's outcome or a resource failure. -/
theorem catchHalt_coded {α : Type} (halt : Halt Raised) {err : Unit → EvalResult α}
    {pnc : Semantics.Word → EvalResult α} {other : Unit → EvalResult α}
    (herr : ErrCoded (err ())) (hpnc : ∀ w, ErrCoded (pnc w)) (hother : ErrCoded (other ())) :
    ErrCoded (Run.catchHalt halt err pnc other) := by
  unfold Run.catchHalt
  split
  · exact hpnc _
  · exact hother
  · split
    · exact herr
    · split
      · exact hpnc _
      · exact hother
  · split
    · exact herr
    · split
      · exact hpnc _
      · exact hother
  · exact ErrCoded.exhausted
  · exact ErrCoded.diverge

/-- A caught coded intrinsic halt reaches the panic handler with its site's code. -/
theorem catchHalt_coded_intrinsic {α : Type} {code : Code} {origin : Raised}
    (h : Coded (.intrinsic code origin)) (err : Unit → EvalResult α)
    (pnc : Semantics.Word → EvalResult α) (other : Unit → EvalResult α) :
    Run.catchHalt (.intrinsic code origin) err pnc other =
      pnc (Run.codeWord (siteCode origin.site)) := by
  rw [Run.catchHalt_intrinsic, show code = siteCode origin.site from h]

open ErrCoded in
/-- `try`: coded when every handler is coded. The self-call needs no premise: its
halt is caught, and what escapes is a handler's outcome or a resource failure. -/
theorem tryCall_coded {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (ext : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) {ok : Step C (ρ ++ Γ) Γ₁}
    (h₂ : Ext Γ Γ₂) {err : Step C Γ Γ₂} (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) {pnc : Step C (κ ++ Γ) Γ₃}
    (h₄ : Ext Γ Γ₄) {other : Step C Γ Γ₄} (sargs : Args C Γ ps)
    (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf) (self : Bool)
    (hok : StepCoded ok) (herr : StepCoded err) (hpnc : StepCoded pnc)
    (hother : StepCoded other) :
    StepCoded (Run.tryCall ext rets h₁ ok h₂ err code h₃ pnc h₄ other sargs hs sbody self) := by
  intro σ
  have hE := map (fun o => (⟨o.st.drop h₂, o.ext⟩ : Out C σ.H Γ)) (herr σ)
  have hP := fun c => map (fun o => (⟨o.st.drop ((Ext.append Γ κ).trans h₃), o.ext⟩ :
    Out C σ.H Γ)) (hpnc (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) c) σ.env)))
  have hO := map (fun o => (⟨o.st.drop h₄, o.ext⟩ : Out C σ.H Γ)) (hother σ)
  unfold Run.tryCall
  split
  · exact revert
  · split
    · split
      · exact map _ (hok _)
      · exact catchHalt_coded _ hE hP hO
    · split
      · exact revert
      · exact bind (decode_coded rets _) fun _ => map _ (hok _)
      · exact hE
      · exact hP _
      · exact hO

/-- Catch data fails only with a revert or a resource failure. -/
theorem catchBytes_coded {ρ ps Γf : Ctx} (c : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf)
    (self : Bool) (σ : State C Γ) :
    ErrCoded (Run.catchBytes c rets sargs hs sbody self σ) := by
  unfold Run.catchBytes
  split
  · exact ErrCoded.revert
  · split
    · split
      · exact ErrCoded.revert
      · exact haltBytes_coded _
    · split <;> first | exact haltBytes_coded _ | exact ErrCoded.revert

/-! ## Control -/

open ErrCoded in
theorem ite_coded {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) {thn : Step C Γ Γ₁}
    (h₂ : Ext Γ Γ₂) {els : Step C Γ Γ₂} (hthn : StepCoded thn) (hels : StepCoded els) :
    StepCoded (Run.ite c h₁ thn h₂ els) := fun σ =>
  bind (value_coded σ c) fun v => by
    by_cases hv : boolT v
    · simp only [hv, if_true]; exact map _ (hthn σ)
    · simp only [hv]; exact map _ (hels σ)

open ErrCoded in
theorem require_coded (c : Val C Γ .bool) : StepCoded (Run.require c) := fun σ =>
  bind (value_coded σ c) fun v => by
    by_cases hv : boolT v
    · simp only [hv, if_true]; exact ok _
    · simp only [hv]; exact revert

open ErrCoded in
/-- The assertion's own halt is raised by its producer, hence coded. -/
theorem assert_coded (c : Val C Γ .bool) : StepCoded (Run.assert c) := fun σ =>
  bind (value_coded σ c) fun _ => bind (evalProducer _) fun _ => pure _

/-- A failed assertion carries code 1, the code of the assertion site. -/
theorem assert_false_code (c : Val C Γ .bool) (σ : State C Γ)
    (h : value σ c = .ok false) {code : Code} {origin : Raised}
    (e : Run.assert c σ = .error (.intrinsic code origin)) :
    code = .assert ∧ origin.site = .assertion := by
  rw [Run.assert_false c σ h] at e
  cases e
  exact ⟨rfl, Raised.ofOrigin_site _ _ _⟩

theorem loop_coded {Γ₁ : Ctx} (c : Val C Γ .bool) (h : Ext Γ Γ₁) {body : Step C Γ Γ₁}
    (hbody : StepCoded body) : StepCoded (Run.loop c h body) := fun σ => by
  unfold Run.loop
  exact Loop.run_coded (fun (o : Out C σ.H Γ) => ErrCoded.map _ (hbody o.st))
    (fun (o : Out C σ.H Γ) => value_coded o.st c) _

theorem block_coded {Γ₁ : Ctx} (h : Ext Γ Γ₁) {body : Step C Γ Γ₁}
    (hbody : StepCoded body) : StepCoded (Run.block h body) := fun σ =>
  ErrCoded.map _ (hbody σ)

theorem seq_coded {Γ₁ Γ₂ : Ctx} {s : Step C Γ Γ₁} {P : Step C Γ₁ Γ₂}
    (hs : StepCoded s) (hP : StepCoded P) : StepCoded (Run.seq s P) := fun σ => by
  unfold Run.seq
  split
  · exact ErrCoded.map _ (hP _)
  · rename_i e he
    exact fun _ h => by cases h; exact hs σ _ he

theorem nil_coded : StepCoded (Run.nil : Step C Γ Γ) := fun _ => ErrCoded.ok _

end Run

end Solidity.Correctness.Panic

