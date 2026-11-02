import Solidity.Backend.InternalFlow.RuntimeCalls
import Solidity.Semantics.ContractWorld

/-! Exact ordinary world/body/internal-call execution bridge. World.callFrame
and its static/library admission remain unchanged. No world or target evaluator. -/
namespace Solidity.Backend.InternalFlow.RuntimeWorld
open ContractWorld
variable {C : Contract}

/-- Concatenate the EXISTING typed program constructors; no new syntax. -/
def concat {Γ Δ Ξ : Ctx} : Prog C Γ Δ → Prog C Δ Ξ → Prog C Γ Ξ
  | .nil, tail => tail
  | .cons s rest, tail => .cons s (concat rest tail)

theorem seq_assoc {Γ Δ Ξ Ω : Ctx} (first : TStep C Γ Δ)
    (second : TStep C Δ Ξ) (third : TStep C Ξ Ω) (σ : State C Γ) :
    TRun.seq (TRun.seq first second) third σ =
      TRun.seq first (TRun.seq second third) σ := by
  cases ha : first σ with
  | error e => simp only [TRun.seq,ha]
  | ok a =>
    cases hb : second a.st with
    | error e => simp only [TRun.seq,ha,hb,Except.map]
    | ok b =>
      cases hc : third b.st with
      | error e => simp only [TRun.seq,ha,hb,hc,Except.map]
      | ok c => simp only [TRun.seq,ha,hb,hc,Except.map]

theorem seq_nil {Γ Δ : Ctx} (step : TStep C Γ Δ) (σ : State C Γ) :
    TRun.seq step TRun.nil σ = step σ := by
  cases h : step σ with
  | error e => simp only [TRun.seq,h]
  | ok out => simp only [TRun.seq,h,TRun.nil,Except.map]

theorem concat_runR : {Γ Δ Ξ : Ctx} → (before : Prog C Γ Δ) → (after : Prog C Δ Ξ) →
    (concat before after).runR = TRun.seq before.runR after.runR
  | _,_,_,.nil,after => by
    funext σ
    change after.runR σ = TRun.seq TRun.nil after.runR σ
    simp only [TRun.seq,TRun.nil]
    cases h : after.runR σ <;> rfl
  | _,_,_,.cons s rest,after => by
    funext σ
    change TRun.seq s.runR (concat rest after).runR σ =
      TRun.seq (TRun.seq s.runR rest.runR) after.runR σ
    rw [concat_runR rest after]
    exact (seq_assoc s.runR rest.runR after.runR σ).symm

variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- An actual world entry whose typed body is a caller prefix and internal call. -/
def entry {Γ Δ ps rs Γf : Ctx} (before : Prog C [] Γ) (name : Name)
    (args : Args C Γ ps) (ret : CallRet Γ rs Δ) (body : Prog C (rs ++ ps) Γf)
    {α : Type} (decode : State C Δ → TRes α) (payable : Bool := false) : Entry C α :=
  ⟨Δ,concat before (.cons (.call name args ret body) .nil),decode,payable⟩

/-- General runtime-frame interface derived from ACTUAL world execution. Every
argument/local/result type is retained, including default-entry memory allocation.
The world endpoint is the actual exported body state and exact settlement. -/
theorem callFrame_success {k : K} {α : Type} {Γ Δ ps rs Γf : Ctx}
    (w next : World contracts) (self : Handle k) (ctx : Context)
    (before : Prog (contracts k) [] Γ) (name : Name)
    (args : Args (contracts k) Γ ps) (ret : CallRet Γ rs Δ)
    (body : Prog (contracts k) (rs ++ ps) Γf)
    (decode : State (contracts k) Δ → TRes α) (payable : Bool)
    (final : State (contracts k) Δ)
    (ran : w.callFrame self (entry before name args ret body decode payable) ctx = .ok (next,final)) :
    ∃ (stored : Storage (contracts k)) (initial : State (contracts k) [])
      (caller : Out (contracts k) initial.H Γ),
      w.storage? self = some stored ∧
      w.enter self.address ctx stored payable = .ok initial ∧
      before.runR initial = .ok caller ∧
      ∃ arguments : TEnv (contracts k) caller.st.H ps,
        args.evalT caller.st = .ok arguments ∧
        ∃ out : Out (contracts k) (ret.enterT (caller.st.withEnv arguments)).st.H Γf,
          body.runR (ret.enterT (caller.st.withEnv arguments)).st = .ok out ∧
          (RuntimeCalls.returned ret body.ext caller.st arguments out).st = final ∧
          w.finish self.address final = .ok next ∧
          ∀ other : Address, other ≠ self.address → next.accounts other = w.accounts other := by
  obtain ⟨stored,initial,whole,hs,he,hr,hf,eq⟩ := World.callFrame_ok ran
  change (concat before (.cons (.call name args ret body) .nil)).runR initial = .ok whole at hr
  rw [concat_runR] at hr
  have tail : (Prog.cons (Stmt.call name args ret body) Prog.nil).runR =
      TRun.call args ret body.ext body.runR := by
    funext σ
    exact seq_nil (TRun.call args ret body.ext body.runR) σ
  rw [tail] at hr
  cases hp : before.runR initial with
  | error e => simp only [TRun.seq,hp] at hr; cases hr
  | ok caller =>
    simp only [TRun.seq,hp] at hr
    cases hc : TRun.call args ret body.ext body.runR caller.st with
    | error e => rw [hc] at hr; cases hr
    | ok result =>
      rw [hc] at hr
      have state : result.st = final :=
        (congrArg (fun o => o.st) (Except.ok.inj hr)).trans eq
      obtain ⟨arguments,ha,out,hb,exported⟩ :=
        (RuntimeCalls.success_iff args ret body.ext body.runR caller.st result).mp hc
      refine ⟨stored,initial,caller,hs,he,hp,arguments,ha,out,hb,?_,?_,?_⟩
      · exact (congrArg (fun o => o.st) exported).trans state
      · rw [← eq]
        exact hf
      · intro other different
        exact World.finish_other hf different

/-- Caller-side decoding is a distinct actual stage AFTER a successful frame.
The equation exposes both executions and never assumes a supplied frame state. -/
theorem call_success_iff {k : K} {α : Type} (w next : World contracts)
    (self : Handle k) (method : Entry (contracts k) α) (ctx : Context) (value : α) :
    w.call self method ctx = .ok (next,value) ↔
      ∃ final : State (contracts k) method.locals,
        w.callFrame self method ctx = .ok (next,final) ∧ method.result final = .ok value := by
  constructor
  · intro ran
    unfold World.call at ran
    cases hf : w.callFrame self method ctx with
    | error halt => simp only [hf,error_bind] at ran; cases ran
    | ok frame =>
      rcases frame with ⟨reached,final⟩
      simp only [hf,ok_bind] at ran
      cases hd : method.result final with
      | error halt => simp only [hd,error_bind] at ran; cases ran
      | ok decoded =>
        simp only [hd,ok_bind] at ran
        rcases Prod.mk.inj (Except.ok.inj ran) with ⟨hw,hv⟩
        cases hw
        cases hv
        exact ⟨final,rfl,hd⟩
  · rintro ⟨final,hf,hd⟩
    simp only [World.call,hf,ok_bind,hd]
    rfl

/-- Decode failure propagates outside the successful frame. It does not expose
an error-valued State/world, nor imply rollback of that executed frame. -/
theorem decode_failure {k : K} {α : Type} (w next : World contracts)
    (self : Handle k) (method : Entry (contracts k) α) (ctx : Context)
    (final : State (contracts k) method.locals) (halt : THalt)
    (hf : w.callFrame self method ctx = .ok (next,final))
    (hd : method.result final = .error halt) : w.call self method ctx = .error halt := by
  simp only [World.call,hf,ok_bind,hd,error_bind]

/-- The old world API refuses ALL these nonempty entries in static mode. This
is an explicit boundary, not a replacement for V13's effect-certified execution. -/
theorem static_refused {Γ Δ ps rs Γf : Ctx}
    (w : World contracts) {k : K} (self : Handle k) (ctx : Context)
    (before : Prog (contracts k) [] Γ) (name : Name)
    (args : Args (contracts k) Γ ps) (ret : CallRet Γ rs Δ)
    (body : Prog (contracts k) (rs ++ ps) Γf) {α : Type}
    (decode : State (contracts k) Δ → TRes α) (payable : Bool)
    (static : ctx.isStatic = true) :
    w.callFrame self (entry before name args ret body decode payable) ctx = .error .revert := by
  have nonempty : emptyBody (concat before (.cons (.call name args ret body) .nil)) = false := by
    cases before <;> rfl
  simp only [World.callFrame,entry,nonempty,static,Bool.not_false,Bool.and_true,
    Bool.or_true,↓reduceIte]
end Solidity.Backend.InternalFlow.RuntimeWorld
