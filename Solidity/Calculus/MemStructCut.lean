import Solidity.Calculus.MemStructWitness
import Solidity.Calculus.Logic
import Solidity.Calculus.TermEq
import Solidity.Semantics.AllocBytes

/-!
# Fresh struct word observations and realized countermodels

The parent allocation does not create its children. A countermodel therefore
first realizes a typed child heap, adopts it, and only then chooses the
parent object in `allocAll`. The original heap is preserved by `children_keeps`.
-/
namespace Solidity.MemoryWitness
open Semantics (structDef lookupBy)
variable {C : Contract} {Γ : Ctx}

/-- A primitive field observed through the freshly allocated local. -/
def fieldRead {s f : Name} {p : PrimTy}
    (hf : lookupBy f (structDef s) = some (.prim p)) :
    Tm C (.mem (.struct s) :: Γ) (.val p) :=
  .app2 .read (.app0 .memory) (.app1 (.mfield hf) (.pvI .here))

/-- The formula read observes exactly the supplied primitive member. -/
theorem fieldRead_eval {s f : Name} {p : PrimTy} (σ : State C Γ)
    (o : MObj σ.H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p)) :
    (fieldRead hf).eval (σ.allocPush o) = some (MFields.get (structDef s) o hf) := by
  change ((HRef.ofId? (σ.allocPush o).H (.struct s) (σ.alloc o).2.id).map
    (fun r => MAddr.field r hf)).bind (σ.allocPush o).heap.readAddr = _
  rw [HRef.ofId?_self]
  change some (MFields.get _ ((σ.allocPush o).heap.get (σ.alloc o).2) hf) = _
  rw [State.allocPush_get]
  change some (MFields.get _ (MFields.wk _ _ o) hf) = _
  rw [MFields.get_wk]
  rfl

/-- A second word exists at every primitive type. -/
def one : (p : PrimTy) → p.Denote
  | .bool => true
  | .uint => ⟨1, by decide⟩
  | .int => ⟨1, by decide⟩

theorem one_ne_default (p : PrimTy) : one p ≠ PrimTy.dflt p := by
  cases p <;> decide +kernel

/-- Choose a concrete word different from the asserted value. -/
def different (p : PrimTy) (v : p.Denote) : p.Denote :=
  if v = PrimTy.dflt p then one p else PrimTy.dflt p

theorem different_ne (p : PrimTy) (v : p.Denote) : different p v ≠ v := by
  unfold different
  split
  · rename_i h
    rw [h]
    exact one_ne_default p
  · rename_i h
    exact Ne.symm h

/-- Refute a universal fresh-field equation at an explicitly realized child
heap. This returns the state *before* parent allocation, as `allocAll` requires. -/
theorem fieldEq_refutes {s f : Name} {p : PrimTy} (σ : State C Γ)
    (g : Grown σ.H (MObj · (.struct s)))
    (hf : lookupBy f (structDef s) = some (.prim p)) (x : Var) (v : p.Denote) :
    ¬ holds (σ.adopt g).1 (.allocAll x (.struct s)
      (.eq (fieldRead hf) (.app0 (.lit v)))) := by
  intro hall
  let o : MObj (σ.adopt g).1.H (.struct s) :=
    MFields.set (structDef s) g.val hf (different p v)
  have heq : holds ((σ.adopt g).1.allocPush o)
      (.eq (fieldRead hf) (.app0 (.lit v))) := hall o
  have heval : (fieldRead (C := C) hf).eval ((σ.adopt g).1.allocPush o) =
      some (different p v) := by
    rw [fieldRead_eval, MFields.get_set_same]
  have hd : (fieldRead (C := C) hf).denote ((σ.adopt g).1.allocPush o) =
      some (different p v) := Tm.denote_eval _ _ _ heval
  change (fieldRead hf).denote ((σ.adopt g).1.allocPush o) = some v at heq
  rw [hd] at heq
  exact different_ne p v (Option.some.inj heq)

/-- A proved answer or a constructive, heap-changing refutation. -/
inductive Answer (φ : Fml C Γ) where
  | proved (valid : ∀ σ, holds σ φ)
  | refuted (state : State C Γ → State C Γ) (refutes : ∀ σ, ¬ holds (state σ) φ)

/-- Transport an answer along checked syntax equality. -/
def Answer.cast {φ ψ : Fml C Γ} (h : φ = ψ) (a : Answer ψ) : Answer φ := h.symm ▸ a

/-- An equation view carrying its full syntax equality. -/
structure EqView (φ : Fml C Γ) where
  p : PrimTy
  a : Tm C Γ (.val p)
  b : Tm C Γ (.val p)
  eqn : φ = .eq a b

/-- Take apart a formula once, with a motive generalized over its context. -/
def eqView (φ : Fml C Γ) : Option (EqView φ) :=
  @Fml.casesOn C (fun _ φ => Option (EqView φ)) Γ φ
    (@fun _ => none)
    (@fun _ p a b => some ⟨p, a, b, rfl⟩)
    (@fun _ _ => none) (@fun _ _ => none)
    (@fun _ _ _ => none) (@fun _ _ _ => none)
    (@fun _ _ _ _ _ => none) (@fun _ _ _ _ _ _ _ => none)
    (@fun _ _ => none) (@fun _ _ _ _ => none)
    (@fun _ _ _ _ _ => none) (@fun _ _ _ => none)
    (@fun _ _ _ _ => none) (@fun _ _ => none)

/-- A fresh-object binder view carrying its full syntax equality. -/
structure AllocView (φ : Fml C Γ) where
  x : Var
  R : RefTy
  body : Fml C (.mem R :: Γ)
  eqn : φ = .allocAll x R body

/-- The binder view uses the same intrinsic recursor discipline. -/
def allocView (φ : Fml C Γ) : Option (AllocView φ) :=
  @Fml.casesOn C (fun _ φ => Option (AllocView φ)) Γ φ
    (@fun _ => none) (@fun _ _ _ _ => none)
    (@fun _ _ => none) (@fun _ _ => none)
    (@fun _ _ _ => none) (@fun _ _ _ => none)
    (@fun _ _ _ _ _ => none) (@fun _ _ _ _ _ _ _ => none)
    (@fun _ _ => none) (@fun _ _ _ _ => none)
    (@fun _ _ _ _ _ => none) (@fun _ _ _ => none)
    (@fun _ x R body => some ⟨x, R, body, rfl⟩) (@fun _ _ => none)

/-- Read a literal without casting a term or changing its type. -/
def literalOp {s : Srt} (o : Op0 C s) : Option ((p : PrimTy) × p.Denote) :=
  @Op0.casesOn C (fun _ _ => Option ((p : PrimTy) × p.Denote)) s o
    (@fun p v => some ⟨p, v⟩) (fun _ => none) (@fun _ _ _ => none)
    none none none (@fun _ _ _ _ => none) (fun _ => none)

/-- Only a literal at the root is returned, never a literal buried in an operator. -/
def literalTerm {s : Srt} (t : Tm C Γ s) : Option ((p : PrimTy) × p.Denote) :=
  @Tm.casesOn C Γ (fun _ _ => Option ((p : PrimTy) × p.Denote)) s t
    (@fun _ _ => none) (@fun _ _ => none) (fun _ => none)
    (@fun _ _ => none) (fun _ _ => none) (@fun _ o => literalOp o)
    (@fun _ _ _ _ => none) (@fun _ _ _ _ _ _ => none)
    (@fun _ _ _ _ _ _ _ _ => none) (fun _ => none)

/-- Recognize a primitive field equation, constructing a refuting heap.
The guards retain map-free admission and compare the complete typed terms. -/
def fieldEquation (x : Var) (s : Name) (p : PrimTy)
    (a b : Tm C (.mem (.struct s) :: Γ) (.val p)) :
    Option (Answer (.allocAll x (.struct s) (.eq a b))) := do
  if hab : a.beqR b = true then
    return .proved (by intro σ o; change a.denote _ = b.denote _; rw [Tm.eq_of_beqR hab])
  else
    let ⟨q, v⟩ ← literalTerm b
    if hqp : q = p then
      let v : p.Denote := hqp ▸ v
      if hb : b.beqR (.app0 (.lit v)) = true then
        if hm : (Ty.ref (.struct s)).mapFree = true then
          let hfields : ∀ fT ∈ structDef s, fT.2.mapFree = true :=
            mapFree_structDef s (by simpa only [Ty.mapFree, decide_eq_true_eq] using hm)
          (structDef s).findSome? fun fT =>
            if hf : lookupBy fT.1 (structDef s) = some (.prim p) then
              if ha : a.beqR (fieldRead hf) = true then
                some (.refuted (fun σ => (σ.adopt (children σ.heap s hfields)).1) (by
                  rw [Tm.eq_of_beqR ha, Tm.eq_of_beqR hb]
                  exact fun σ => fieldEq_refutes σ (children σ.heap s hfields) hf x v))
              else none
            else none
        else none
      else none
    else none

/-- Apply the field schema to a fresh struct binder. Unsupported bodies
are kept unknown; no target, waiver, or existing memory semantics is changed. -/
def boundAnswer (x : Var) : (R : RefTy) → (body : Fml C (.mem R :: Γ)) →
    Option (Answer (.allocAll x R body))
  | .struct s, body =>
    if (Ty.ref (.struct s)).mapFree then do
      let e ← eqView body
      let a ← fieldEquation x s e.p e.a e.b
      return a.cast (congrArg (Fml.allocAll x (.struct s)) e.eqn)
    else none
  | _, _ => none

/-- Recognize the outer binder and retain its checked syntax equality. -/
def structAnswer (φ : Fml C Γ) : Option (Answer φ) := do
  let v ← allocView φ
  let a ← boundAnswer v.x v.R v.body
  return a.cast v.eqn

#print axioms fieldRead_eval
#print axioms fieldEq_refutes
end Solidity.MemoryWitness
