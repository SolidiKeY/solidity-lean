import Solidity.Backend.InternalFlow.RuntimeFrameTransport

/-! Successful-output agreement for the existing typed result and execution
operators. These relations define no evaluator and make no failed-state claim. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ResultAgreement
open Evm Evm.Memory

def Agree {α : Type} (left right : TRes α) : Prop :=
 ∀ a b, left=.ok a → right=.ok b → a=b

theorem refl {α : Type} (x : TRes α) : Agree x x := by
 intro a b left right
 exact Except.ok.inj (left.symm.trans right)

theorem error_left {α : Type} (halt : THalt) (right : TRes α) : Agree (.error halt) right := by
 intro a b impossible actual
 cases impossible

theorem error_right {α : Type} (left : TRes α) (halt : THalt) : Agree left (.error halt) := by
 intro a b actual impossible
 cases impossible

theorem map {α β : Type} {left right : TRes α} (h : Agree left right) (f : α → β) :
 Agree (left.map f) (right.map f) := by
 intro a b first second
 cases l : left with
 | error halt => simp only [l,Except.map] at first;cases first
 | ok x =>
   cases r : right with
   | error halt => simp only [r,Except.map] at second;cases second
   | ok y =>
     have same := h x y l r
     subst y
     simp only [l,r,Except.map] at first second
     exact Except.ok.inj (first.symm.trans second)

theorem bind {α β : Type} {left right : TRes α} (h : Agree left right)
 (f g : α → TRes β) (next : ∀ a,Agree (f a) (g a)) :
 Agree (left >>= f) (right >>= g) := by
 intro a b first second
 cases l : left with
 | error halt => simp only [l,error_bind] at first;cases first
 | ok x =>
   cases r : right with
   | error halt => simp only [r,error_bind] at second;cases second
   | ok y =>
     have same := h x y l r
     subst y
     simp only [l,r,ok_bind] at first second
     exact next x a b first second

def Steps {C : Contract} {Γ Δ : Ctx} (left right : TStep C Γ Δ) : Prop :=
 ∀ σ, Agree (left σ) (right σ)

theorem same {C : Contract} {Γ Δ : Ctx} (step : TStep C Γ Δ) : Steps step step :=
 fun σ => refl (step σ)

theorem seq {C : Contract} {Γ Δ Ξ : Ctx} {left right : TStep C Γ Δ}
 {after₁ after₂ : TStep C Δ Ξ} (before : Steps left right) (after : Steps after₁ after₂) :
 Steps (TRun.seq left after₁) (TRun.seq right after₂) := by
 intro σ
 cases l : left σ with
 | error halt =>
   simp only [TRun.seq,l]
   exact error_left halt _
 | ok x =>
   cases r : right σ with
   | error halt =>
     simp only [TRun.seq,r]
     exact error_right _ halt
   | ok y =>
     have same := before σ x y l r
     subst y
     simp only [TRun.seq,l,r]
     exact map (after x.st) (fun tail => (⟨tail.st,x.ext.trans tail.ext⟩ : Solidity.Out C σ.H Ξ))

theorem call {C : Contract} {Γ Δ ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (scope : Ext (rs ++ ps) Γf) {left right : TStep C (rs ++ ps) Γf} (body : Steps left right) :
 Steps (TRun.call args ret scope left) (TRun.call args ret scope right) := by
 intro σ
 exact bind (refl (args.evalT σ)) _ _ (fun arguments =>
   map (body (ret.enterT (σ.withEnv arguments)).st) (exported ret scope σ arguments))

theorem ite {C : Contract} {Γ Γ₁ Γ₂ : Ctx} (condition : Val C Γ .bool)
 (scope₁ : Ext Γ Γ₁) (scope₂ : Ext Γ Γ₂)
 {yes₁ yes₂ : TStep C Γ Γ₁} {no₁ no₂ : TStep C Γ Γ₂}
 (yes : Steps yes₁ yes₂) (no : Steps no₁ no₂) :
 Steps (TRun.ite condition scope₁ yes₁ scope₂ no₁) (TRun.ite condition scope₁ yes₂ scope₂ no₂) := by
 intro σ
 apply bind (refl (condition.evalT σ))
 intro flag
 split
 · exact map (yes σ) (fun out => (⟨out.st.drop scope₁,out.ext⟩ : Solidity.Out C σ.H Γ))
 · exact map (no σ) (fun out => (⟨out.st.drop scope₂,out.ext⟩ : Solidity.Out C σ.H Γ))

end Solidity.Backend.InternalFlow.RuntimeFrame.ResultAgreement
