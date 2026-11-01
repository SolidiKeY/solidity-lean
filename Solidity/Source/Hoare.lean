import Solidity.Source.Machine

/-!
# Hoare triples over the interpreter monad (lane V04b)

`Hoare P m Q X`: from every state satisfying `P`, the computation `m`
either returns `a` in a state satisfying `Q a`, or halts with `h` in a
state satisfying `X h`. The interpreter (`Solidity/Source/Eval.lean`) is a
program in `EM`; preservation of a state invariant is a triple whose
pre- and postconditions include it, and progress is a triple whose halt
condition excludes `stuck` (`NotStuck`).

The rules below cover every combinator the interpreter is built from:
`pure`, `bind`, `halt`, `lift`, the state accessors, `sub` (a computation
over other locals) and `attempt` (catching a halt).
-/

namespace Solidity.Source

open EM

variable {E : Env}

/-- A state of the interpreter monad over locals `Γ`. -/
abbrev EMState (E : Env) (Γ : RCtx) := Locals E.layout Γ × St E

/-- **A Hoare triple** over `EM`. -/
def Hoare {Γ : RCtx} {α : Type} (P : EMState E Γ → Prop) (m : EM E Γ α)
    (Q : α → EMState E Γ → Prop) (X : Halt → EMState E Γ → Prop) : Prop :=
  ∀ x, P x → match m.run x with
    | (.ok a, y) => Q a y
    | (.error h, y) => X h y

/-- A halt that is not `stuck`. -/
def NotStuck : Halt → Prop
  | .stuck _ => False
  | _ => True

namespace Hoare

variable {Γ : RCtx} {α β : Type}

theorem run_bind (m : EM E Γ α) (k : α → EM E Γ β) (x : EMState E Γ) :
    (m >>= k).run x = match m.run x with
      | (.ok a, y) => (k a).run y
      | (.error e, y) => (.error e, y) := by
  rw [ExceptT.run_bind]
  show StateT.bind (ExceptT.run m) _ x = _
  simp only [StateT.bind]
  show (match ExceptT.run m x with | (r, y) => _) = _
  rcases ExceptT.run m x with ⟨r, y⟩
  cases r <;> rfl

theorem pure' {P : EMState E Γ → Prop} {a : α} {Q : α → EMState E Γ → Prop}
    {X : Halt → EMState E Γ → Prop} (h : ∀ x, P x → Q a x) : Hoare P (pure a : EM E Γ α) Q X :=
  fun x hx => h x hx

theorem halt' {P : EMState E Γ → Prop} {e : Halt} {Q : α → EMState E Γ → Prop}
    {X : Halt → EMState E Γ → Prop} (h : ∀ x, P x → X e x) : Hoare P (halt e : EM E Γ α) Q X :=
  fun x hx => h x hx

theorem bind {P : EMState E Γ → Prop} {m : EM E Γ α} {R : α → EMState E Γ → Prop}
    {k : α → EM E Γ β} {Q : β → EMState E Γ → Prop} {X : Halt → EMState E Γ → Prop}
    (hm : Hoare P m R X) (hk : ∀ a, Hoare (R a) (k a) Q X) : Hoare P (m >>= k) Q X := by
  intro x hx
  rw [run_bind]
  have h1 := hm x hx
  rcases hr : m.run x with ⟨r, y⟩
  rw [hr] at h1
  cases r with
  | ok a => exact hk a y h1
  | error e => exact h1

/-- **Consequence**: a stronger precondition, weaker postconditions. -/
theorem conseq {P P' : EMState E Γ → Prop} {m : EM E Γ α} {Q Q' : α → EMState E Γ → Prop}
    {X X' : Halt → EMState E Γ → Prop} (h : Hoare P m Q X) (hp : ∀ x, P' x → P x)
    (hq : ∀ a y, Q a y → Q' a y) (hx : ∀ e y, X e y → X' e y) : Hoare P' m Q' X' := by
  intro x hx'
  have h1 := h x (hp x hx')
  rcases hr : m.run x with ⟨r, y⟩
  rw [hr] at h1
  cases r with
  | ok a => exact hq a y h1
  | error e => exact hx e y h1

/-- A precondition that is false proves any triple. -/
theorem of_false {P : EMState E Γ → Prop} {m : EM E Γ α} {Q : α → EMState E Γ → Prop}
    {X : Halt → EMState E Γ → Prop} (h : ∀ x, ¬ P x) : Hoare P m Q X :=
  fun x hx => absurd hx (h x)

/-- Case analysis on a fact about the initial state. -/
theorem cases_pre {P : EMState E Γ → Prop} {m : EM E Γ α} {Q : α → EMState E Γ → Prop}
    {X : Halt → EMState E Γ → Prop} (c : Prop) (h₁ : Hoare (fun x => P x ∧ c) m Q X)
    (h₂ : Hoare (fun x => P x ∧ ¬ c) m Q X) : Hoare P m Q X := by
  intro x hx
  by_cases hc : c
  · exact h₁ x ⟨hx, hc⟩
  · exact h₂ x ⟨hx, hc⟩

theorem lift' {P : EMState E Γ → Prop} {r : R α} {Q : α → EMState E Γ → Prop}
    {X : Halt → EMState E Γ → Prop}
    (h : ∀ x, P x → match r with | .ok a => Q a x | .error e => X e x) : Hoare P (lift r : EM E Γ α) Q X := by
  intro x hx
  have h1 := h x hx
  cases r with
  | ok a => exact h1
  | error e => exact h1

theorem st' {P : EMState E Γ → Prop} {Q : St E → EMState E Γ → Prop} {X : Halt → EMState E Γ → Prop}
    (h : ∀ x, P x → Q x.2 x) : Hoare P (st : EM E Γ (St E)) Q X :=
  fun x hx => h x hx

theorem locals' {P : EMState E Γ → Prop} {Q : Locals E.layout Γ → EMState E Γ → Prop}
    {X : Halt → EMState E Γ → Prop} (h : ∀ x, P x → Q x.1 x) :
    Hoare P (locals : EM E Γ (Locals E.layout Γ)) Q X :=
  fun x hx => h x hx

theorem setSt' {P : EMState E Γ → Prop} {s : St E} {Q : Unit → EMState E Γ → Prop}
    {X : Halt → EMState E Γ → Prop} (h : ∀ x, P x → Q () (x.1, s)) : Hoare P (setSt s : EM E Γ Unit) Q X :=
  fun x hx => h x hx

theorem modSt' {P : EMState E Γ → Prop} {f : St E → St E} {Q : Unit → EMState E Γ → Prop}
    {X : Halt → EMState E Γ → Prop} (h : ∀ x, P x → Q () (x.1, f x.2)) :
    Hoare P (modSt f : EM E Γ Unit) Q X :=
  fun x hx => h x hx

theorem setLocals' {P : EMState E Γ → Prop} {l : Locals E.layout Γ} {Q : Unit → EMState E Γ → Prop}
    {X : Halt → EMState E Γ → Prop} (h : ∀ x, P x → Q () (l, x.2)) :
    Hoare P (setLocals l : EM E Γ Unit) Q X :=
  fun x hx => h x hx

/-- **`sub`**: the inner computation runs over locals `l'`; the outer
locals are kept, the state passed through. -/
theorem sub' {Γ' : RCtx} {l' : Locals E.layout Γ'} {m : EM E Γ' α} {P : EMState E Γ → Prop}
    {Q : α × Locals E.layout Γ' → EMState E Γ → Prop} {X : Halt → EMState E Γ → Prop}
    (h : ∀ l, Hoare (fun y => y.1 = l' ∧ P (l, y.2)) m (fun a y => Q (a, y.1) (l, y.2))
      (fun e y => X e (l, y.2))) : Hoare P (sub l' m) Q X := by
  intro ⟨l, s⟩ hx
  have h1 := h l (l', s) ⟨rfl, hx⟩
  unfold EM.sub
  rcases hr : m.run (l', s) with ⟨r, ⟨l'', s'⟩⟩
  rw [hr] at h1
  have hr' : m (l', s) = (r, (l'', s')) := hr
  cases r with
  | ok a => simp only [ExceptT.run, ExceptT.mk, hr'] at ⊢; exact h1
  | error e => simp only [ExceptT.run, ExceptT.mk, hr'] at ⊢; exact h1

/-- **`attempt`**: a halt becomes a result. -/
theorem attempt' {P : EMState E Γ → Prop} {m : EM E Γ α} {Q : Except Halt α → EMState E Γ → Prop}
    {X : Halt → EMState E Γ → Prop} (h : Hoare P m (fun a => Q (.ok a)) (fun e => Q (.error e))) :
    Hoare P (attempt m) Q X := by
  intro x hx
  have h1 := h x hx
  show (match (match m.run x with | (r, x') => ((.ok r, x') : Except Halt _ × _)) with
    | (.ok a, y) => Q a y
    | (.error h, y) => X h y)
  rcases hr : m.run x with ⟨r, y⟩
  rw [hr] at h1
  cases r with
  | ok a => exact h1
  | error e => exact h1

/-- An `if` on a proposition of the computation's parameters. -/
theorem dite' {c : Prop} [Decidable c] {P : EMState E Γ → Prop} {m₁ : c → EM E Γ α}
    {m₂ : ¬ c → EM E Γ α} {Q : α → EMState E Γ → Prop} {X : Halt → EMState E Γ → Prop}
    (h₁ : ∀ hc : c, Hoare P (m₁ hc) Q X) (h₂ : ∀ hc : ¬ c, Hoare P (m₂ hc) Q X) :
    Hoare P (if hc : c then m₁ hc else m₂ hc) Q X := by
  by_cases hc : c
  · rw [dif_pos hc]; exact h₁ hc
  · rw [dif_neg hc]; exact h₂ hc

theorem ite' {c : Prop} [Decidable c] {P : EMState E Γ → Prop} {m₁ m₂ : EM E Γ α}
    {Q : α → EMState E Γ → Prop} {X : Halt → EMState E Γ → Prop}
    (h₁ : c → Hoare P m₁ Q X) (h₂ : ¬ c → Hoare P m₂ Q X) : Hoare P (if c then m₁ else m₂) Q X := by
  by_cases hc : c
  · rw [if_pos hc]; exact h₁ hc
  · rw [if_neg hc]; exact h₂ hc

end Hoare

end Solidity.Source
