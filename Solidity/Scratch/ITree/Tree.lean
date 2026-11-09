import Solidity.Calculus.CallerModel

/-!
# Scratch (itree-inspection, Experiment A): a finite interaction tree

A free monad over one event signature: control leaves the contract at a
payment (`transfer`, `send`), the environment answers with what the callee
leaves.  `diverge` and every other halt stay leaves (`COut.halt`).  The
handler `Handle A J` reads a tree as `ExecS J`'s outcomes, the callee's
answers restricted by `A` (`True` for `ExecS`, `CallerModel.Allows` for
`ExecSM`).  Not for merge: `docs/audits/itree-inspection.md`.
-/

namespace Solidity.Scratch.ITree

open Solidity

variable {C : Contract}

/-- What a callee leaves: storage, ledger, balance. -/
abbrev Resume (C : Contract) := Storage C × Ledger × PrimTy.uint.Denote

/-- Which payment hands control out. -/
inductive Kind where
  | transfer
  | send (full : Bool)

/-- Whether the payment calls back under `pay` (`Stmt.forksIn`). -/
def Kind.callsBack (pay : Bool) : Kind → Bool
  | .transfer => pay
  | .send full => pay || full

/-- An event: control leaves in `st` by a payment of kind `kind`. -/
structure Ev (C : Contract) where
  {Γ : Ctx}
  st : State C Γ
  kind : Kind

/-- The answers: a transfer's callee resumes; a send's may also revert. -/
def Ev.Ans (e : Ev C) : Type :=
  match e.kind with
  | .transfer => Resume C
  | .send _ => Option (Resume C)

/-- The answer "the callee left `x`". -/
def Ev.resume (e : Ev C) (x : Resume C) : e.Ans :=
  match e with
  | ⟨_, .transfer⟩ => x
  | ⟨_, .send _⟩ => some x

/-- The deterministic answer: the callee changes nothing. -/
def Ev.same (e : Ev C) : e.Ans := e.resume (e.st.storage, e.st.net, e.st.selfBalance)

/-- Finite interaction trees. -/
inductive Tree (C : Contract) (R : Type) where
  | ret (r : R)
  | vis (e : Ev C) (k : e.Ans → Tree C R)

namespace Tree

variable {R S : Type}

def bind : Tree C R → (R → Tree C S) → Tree C S
  | .ret r, f => f r
  | .vis e k, f => .vis e fun a => (k a).bind f

def map (g : R → S) (t : Tree C R) : Tree C S := t.bind fun r => .ret (g r)

end Tree

/-- What a callee may leave from a state: `CallerModel.Allows M J`, or
`True` for `ExecS`. -/
abbrev Allow (C : Contract) := ∀ {Γ : Ctx}, State C Γ → Storage C → Ledger → PrimTy.uint.Denote → Prop

/-- The havoc handler's allowance (`ExecS`). -/
def anyA : Allow C := fun _ _ _ _ => True

/-- **The handler**: the outcomes a tree may reach when every payment that
calls back (`J.pay`) hands control to a callee leaving what `A` allows and
keeping `J`; `viol` is the outcome "invariant broken on exit". -/
inductive Handle (A : Allow C) (J : StateInv C) {R : Type} (viol : R) : Tree C R → R → Prop where
  | ret {r : R} : Handle A J viol (.ret r) r
  | det {e : Ev C} {k : e.Ans → Tree C R} {o : R} :
      e.kind.callsBack J.pay = false → Handle A J viol (k e.same) o → Handle A J viol (.vis e k) o
  | violated {e : Ev C} {k : e.Ans → Tree C R} :
      e.kind.callsBack J.pay = true → ¬ J.at e.st → Handle A J viol (.vis e k) viol
  | resume {e : Ev C} {k : e.Ans → Tree C R} {st : Storage C} {nt : Ledger}
      {sb : PrimTy.uint.Denote} {o : R} :
      e.kind.callsBack J.pay = true → J.at e.st → J.at (e.st.havoc st nt sb) → A e.st st nt sb →
        Handle A J viol (k (e.resume (st, nt, sb))) o → Handle A J viol (.vis e k) o
  | failed {Γ : Ctx} {σ : State C Γ} {full : Bool} {k : Option (Resume C) → Tree C R} {o : R} :
      (J.pay || full) = true → Handle A J viol (k none) o → Handle A J viol (.vis ⟨σ, .send full⟩ k) o

namespace Handle

variable {A A' : Allow C} {J : StateInv C} {R S : Type} {viol : R} {viol' : S}

/-- **Weakening of the attacker**, once for every tree. -/
theorem mono (hA : ∀ {Γ : Ctx} (σ : State C Γ) st nt sb, A σ st nt sb → A' σ st nt sb)
    {t : Tree C R} {o : R} (h : Handle A J viol t o) : Handle A' J viol t o := by
  induction h with
  | ret => exact .ret
  | det h₁ _ ih => exact .det h₁ ih
  | violated h₁ h₂ => exact .violated h₁ h₂
  | resume h₁ h₂ h₃ h₄ _ ih => exact .resume h₁ h₂ h₃ (hA _ _ _ _ h₄) ih
  | failed h₁ _ ih => exact .failed h₁ ih

/-- **Bind**: a handled bind is a handled tree, then its continuation, when
the continuation keeps a broken invariant. -/
theorem bind_iff {t : Tree C R} {f : R → Tree C S} (hf : f viol = .ret viol') {o : S} :
    Handle A J viol' (t.bind f) o ↔ ∃ r, Handle A J viol t r ∧ Handle A J viol' (f r) o := by
  constructor
  · intro h
    induction t with
    | ret r => exact ⟨r, .ret, h⟩
    | vis e k ih =>
      cases h with
      | det h₁ h₂ => obtain ⟨r, hr, hr'⟩ := ih _ h₂; exact ⟨r, .det h₁ hr, hr'⟩
      | violated h₁ h₂ => exact ⟨viol, .violated h₁ h₂, hf ▸ .ret⟩
      | resume h₁ h₂ h₃ h₄ h₅ =>
        obtain ⟨r, hr, hr'⟩ := ih _ h₅; exact ⟨r, .resume h₁ h₂ h₃ h₄ hr, hr'⟩
      | failed h₁ h₂ => obtain ⟨r, hr, hr'⟩ := ih _ h₂; exact ⟨r, .failed h₁ hr, hr'⟩
  · rintro ⟨r, hr, hr'⟩
    induction hr with
    | ret => exact hr'
    | det h₁ _ ih => exact .det h₁ (ih hr')
    | violated h₁ h₂ =>
      rw [hf] at hr'; cases hr'; exact .violated h₁ h₂
    | resume h₁ h₂ h₃ h₄ _ ih => exact .resume h₁ h₂ h₃ h₄ (ih hr')
    | failed h₁ _ ih => exact .failed h₁ (ih hr')

theorem map_iff {t : Tree C R} {g : R → S} (hg : g viol = viol') {o : S} :
    Handle A J viol' (t.map g) o ↔ ∃ r, Handle A J viol t r ∧ o = g r := by
  rw [Tree.map, bind_iff (by rw [hg])]
  constructor
  · rintro ⟨r, hr, h⟩; cases h; exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, .ret⟩

end Handle

end Solidity.Scratch.ITree
