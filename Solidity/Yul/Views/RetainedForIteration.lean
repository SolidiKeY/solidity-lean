import Solidity.Yul.Views.RetainedBlockObserver

/-! Exact observation contract for actual Source.forIter. General guard/post
capture remains a producer obligation. Concrete zero-horizon and unconditional
break/return instances execute no post expression and assume no completeness. -/
namespace Solidity.Yul.Views

structure ForIterationObserver {E Γ Γ₁ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ)
    (post : Source.ROptExpr E Γ) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) where
  observe : List (EntryReferenceScope E) → Source.Locals E.layout Γ → Source.EMState E [] →
    (Except Source.Halt (Source.Out E.layout Γ Γ) × Source.EMState E []) × List (EntryReferenceScope E)
  source : ∀ prior l s, (observe prior l s).1=(Source.forIter G F n nps ph condition post body l).run s
  prior : ∀ prior l s scope, scope∈prior → scope∈(observe prior l s).2

/-- No actual iteration runs at horizon zero. -/
def zeroForIterationObserver {E Γ Γ₁ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (nps : Nat) (ph : Option (Source.Ph E)) (condition : Source.ROptBool E Γ)
    (post : Source.ROptExpr E Γ) (body : Source.RStmt E R M ⟨true,u⟩ Γ Γ₁) :
    ForIterationObserver G F 0 nps ph condition post body where
  observe := fun prior _ s => ((.error .timeout,s),prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

/-- An absent guard and actual break bypass every possible post expression. -/
def breakForIterationObserver {E Γ R M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (post : Source.ROptExpr E Γ) :
    ForIterationObserver G F (n+2) nps ph .none post (.brk (R:=R) (M:=M) (u:=u)) where
  observe := fun prior l s => ((.ok (.normal l),s),prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

/-- Actual return also bypasses the post and propagates its own locals. -/
def returnForIterationObserver {E Γ M} {u : Bool} (G : Source.Glob E) (F : Source.Fr)
    (n nps : Nat) (ph : Option (Source.Ph E)) (post : Source.ROptExpr E Γ) :
    ForIterationObserver G F (n+2) nps ph .none post (.ret rfl (R:=[]) (M:=M) (k:=⟨true,u⟩)) where
  observe := fun prior l s => ((.ok (.ret l),s),prior)
  source := fun _ _ _ => rfl
  prior := fun _ _ _ _ member => member

end Solidity.Yul.Views
