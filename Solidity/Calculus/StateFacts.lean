import Solidity.Signature
import Solidity.Calculus.ReadWrite

/-!
# Facts about the typed symbols

The shapes of the paths a law's side condition reads (`SegT`), and a member
type's prefix (`Ty.memberTy_snoc_some`).  Of the typed signature
(`Signature.lean`): its symbols are monotone in their arguments (`OLe`,
`Op1.eval_le` …), what a rewrite of an update's right-hand sides reads
(`Calculus/SeqRewrite.lean`).

The facts about the untyped symbols (`Srt.Le`, `Srt.DEquiv`,
`Srt.AgreePart`, `OpN.eval_part`, `State.Keeps`, …) went with those symbols
(W9.8.3c), and the facts about the untyped state the decision procedure
read (`Res.Le`, `Res.OkEq`, `State.HeapEq`, `State.selectRoot`, …) with it
(W10): a typed term reads the typed state, and the facts a law needs are
stated on it where the law is.
-/

namespace Solidity

section
open Semantics

theorem Ty.memberTy_snoc_some {T T' : Ty} {p : List Selector} {s : Selector}
    (h : T.memberTy (p ++ [s]) = some T') : ∃ R', T.memberTy p = some (.ref R') := by
  rw [Ty.memberTy_append] at h
  cases hp : T.memberTy p with
  | none => simp [hp] at h
  | some T'' =>
    cases T'' with
    | prim q => simp [hp, Ty.memberTy, Ty.at_prim] at h
    | ref R' => exact ⟨R', rfl⟩

end

/-! ## From `Solidity.Calculus.TermTaclets` -/

section
open Semantics Theory
variable {C : Contract}

/-- The shape of a path's segment: a member, or an element at a literal
index (`some k`) or at an index the syntax does not decide (`none`: a
local, a length, the slot past the end). -/
inductive SegT where
  | field (f : Name)
  | at (k : Option Int)
  deriving DecidableEq, Repr

/-- The segment has the shape. -/
def SegT.fits : SegT → Selector → Bool
  | .field f, .field g => f == g
  | .at (some k), .at i => k == i
  | .at none, .at _ => true
  | _, _ => false

/-- The path has the shape, segment by segment. -/
def SegT.matches : List SegT → List Selector → Bool
  | [], [] => true
  | x :: a, s :: p => x.fits s && SegT.matches a p
  | _, _ => false

/-- Whether two shapes tell their segments apart: `some true` when the
segments differ in every state (a member against an element, two members
or two literal indices by name or value), `some false` when they are one
segment in every state, `none` when a symbolic index decides nothing. -/
def SegT.apart : SegT → SegT → Option Bool
  | .field f, .field g => some (f != g)
  | .field _, .at _ => some true
  | .at _, .field _ => some true
  | .at (some i), .at (some j) => some (i != j)
  | .at none, .at _ => none
  | .at (some _), .at none => none

/-- The two shapes leave each other: at some position both have a segment
and the segments differ, the ones before being the same — the syntactic
form of the Theory's `diverges`.  A symbolic index decides nothing. -/
def SegT.diverges : List SegT → List SegT → Bool
  | x :: a, y :: b => match x.apart y with
    | some true => true
    | some false => SegT.diverges a b
    | none => false
  | _, _ => false

/-- Two paths that have the shapes `a ++ b` have the shape of their halves. -/
theorem SegT.matches_append : (a b : List SegT) → (p q : List Selector) → SegT.matches a p = true →
    SegT.matches b q = true → SegT.matches (a ++ b) (p ++ q) = true
  | [], _, [], _, _, hb => hb
  | x :: a, b, s :: p, q, ha, hb => by
    simp only [SegT.matches, Bool.and_eq_true] at ha
    simp only [List.cons_append, SegT.matches, ha.1, SegT.matches_append a b p q ha.2 hb,
      Bool.and_self]
  | [], _, _ :: _, _, ha, _ | _ :: _, _, [], _, ha, _ => nomatch ha

/-- `apart` decides the segments as it says. -/
theorem SegT.apart_sound : {x y : SegT} → {d : Bool} → {s t : Selector} → x.apart y = some d →
    x.fits s = true → y.fits t = true → (d = true → s ≠ t) ∧ (d = false → s = t)
  | .field _, .field _, _, .field _, .field _, h, hs, ht => by
    simp only [SegT.fits, beq_iff_eq] at hs ht
    simp only [SegT.apart, Option.some.injEq] at h
    subst hs ht h
    exact ⟨fun hne e => (bne_iff_ne.1 hne) (Selector.field.inj e),
      fun he => by rw [bne_eq_false_iff_eq.1 he]⟩
  | .at (some _), .at (some _), _, .at _, .at _, h, hs, ht => by
    simp only [SegT.fits, beq_iff_eq] at hs ht
    simp only [SegT.apart, Option.some.injEq] at h
    subst hs ht h
    exact ⟨fun hne e => (bne_iff_ne.1 hne) (Selector.at.inj e),
      fun he => by rw [bne_eq_false_iff_eq.1 he]⟩
  | .field _, .at _, _, .field _, .at _, h, _, _ | .at _, .field _, _, .at _, .field _, h, _, _ => by
    simp only [SegT.apart, Option.some.injEq] at h
    subst h
    exact ⟨fun _ e => Selector.noConfusion e, fun h => nomatch h⟩
  | .at none, .at _, _, _, _, h, _, _ | .at (some _), .at none, _, _, _, h, _, _ => by
    simp only [SegT.apart, reduceCtorEq] at h
  | .field _, _, _, .at _, _, _, hs, _ | .at _, _, _, .field _, _, _, hs, _ => by
    simp only [SegT.fits, Bool.false_eq_true] at hs
  | _, .field _, _, _, .at _, _, _, ht | _, .at _, _, _, .field _, _, _, ht => by
    simp only [SegT.fits, Bool.false_eq_true] at ht

/-- Shapes that diverge have paths that diverge. -/
theorem SegT.diverges_sound : (a b : List SegT) → (p q : List Selector) → SegT.diverges a b = true →
    SegT.matches a p = true → SegT.matches b q = true → Theory.diverges p q = true
  | x :: a, y :: b, s :: p, t :: q, hd, ha, hb => by
    simp only [SegT.matches, Bool.and_eq_true] at ha hb
    simp only [SegT.diverges] at hd
    simp only [Theory.diverges]
    cases hx : x.apart y with
    | none => rw [hx] at hd; cases hd
    | some d =>
      rw [hx] at hd
      have hst := SegT.apart_sound hx ha.1 hb.1
      cases d with
      | true => rw [if_neg (hst.1 rfl)]
      | false =>
        rw [if_pos (hst.2 rfl)]
        exact SegT.diverges_sound a b p q hd ha.2 hb.2
  | [], _, _, _, hd, _, _ | _ :: _, [], _, _, hd, _, _ => nomatch hd
  | _ :: _, _ :: _, [], _, _, ha, _ => nomatch ha
  | _ :: _, _ :: _, _ :: _, [], _, _, hb => nomatch hb

end



/-! ## The typed symbols are monotone in their arguments

Where an argument returns, a rewrite of it returns the same value
(`OLe`); a symbol of the typed signature then returns what it returned
(`Op1.eval_le` …), a lazy operand (`&&`, `||`, `c ? a : b`) too. -/

section TypedLe

/-- Where `a` returns a value, `b` returns it too. -/
def OLe {α : Type} (a b : Option α) : Prop := ∀ x, a = some x → b = some x

theorem OLe.refl {α : Type} (a : Option α) : OLe a a := fun _ h => h

theorem OLe.none {α : Type} (b : Option α) : OLe none b := fun _ h => Option.noConfusion h

theorem OLe.trans {α : Type} {a b c : Option α} (h₁ : OLe a b) (h₂ : OLe b c) : OLe a c :=
  fun x h => h₂ x (h₁ x h)

theorem OLe.cases {α : Type} {a b : Option α} (h : OLe a b) : a = Option.none ∨ a = b := by
  cases a with
  | none => exact .inl rfl
  | some x => exact .inr (h x rfl).symm

theorem OLe.bind {α β : Type} {a a' : Option α} {f f' : α → Option β} (ha : OLe a a')
    (hf : ∀ x, OLe (f x) (f' x)) : OLe (a.bind f) (a'.bind f') := fun y h => by
  obtain ⟨x, hx, hy⟩ := Option.bind_eq_some_iff.1 h
  rw [ha x hx, Option.bind_some]
  exact hf x y hy

theorem OLe.map {α β : Type} {a a' : Option α} (f : α → β) (ha : OLe a a') :
    OLe (a.map f) (a'.map f) := fun y h => by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [ha x hx]
  rfl

variable {C : Contract} {g : State C []}

theorem binopT_le (op : BinOp) {p : PrimTy} (hp : op.accepts p = true) (a : p.Denote)
    {y y' : Option p.Denote} (h : OLe y y') : OLe (binopT op hp a y) (binopT op hp a y') := by
  unfold binopT
  split
  · exact OLe.refl _
  · exact OLe.bind h fun _ => OLe.refl _

theorem cond_le {α : Type} (c : Bool) {y y' z z' : Option α} (hy : OLe y y') (hz : OLe z z') :
    OLe (cond c y z) (cond c y' z') := by
  cases c
  · exact hz
  · exact hy

theorem _root_.Solidity.Op1.eval_le {a s : Srt} (o : Op1 C a s) {x x' : Option (a.Den C g.H)}
    (h : OLe x x') : OLe (o.eval g x) (o.eval g x') := by
  rcases h.cases with rfl | rfl
  · rw [Op1.eval_eq_evalM]
    cases o <;> exact OLe.none _
  · exact OLe.refl _

theorem _root_.Solidity.Op2.eval_le {a b s : Srt} (o : Op2 C a b s)
    {x x' : Option (a.Den C g.H)} {y y' : Option (b.Den C g.H)} (hx : OLe x x') (hy : OLe y y') :
    OLe (o.eval g x y) (o.eval g x' y') := by
  rcases hx.cases with rfl | rfl
  · rw [Op2.eval_eq_evalM]
    cases o <;> exact OLe.none _
  · rcases hy.cases with rfl | rfl
    · rw [Op2.eval_eq_evalM]
      cases o with
      | binop op h => exact OLe.bind (OLe.refl _) fun a => binopT_le op h a (OLe.none _)
      | _ => cases x <;> exact OLe.none _
    · exact OLe.refl _

theorem _root_.Solidity.Op3.eval_le {a b c s : Srt} (o : Op3 C a b c s)
    {x x' : Option (a.Den C g.H)} {y y' : Option (b.Den C g.H)} {z z' : Option (c.Den C g.H)}
    (hx : OLe x x') (hy : OLe y y') (hz : OLe z z') :
    OLe (o.eval g x y z) (o.eval g x' y' z') := by
  rcases hx.cases with rfl | rfl
  · rw [Op3.eval_eq_evalM]
    cases o <;> exact OLe.none _
  · rw [Op3.eval_eq_evalM]
    cases o with
    | ite => exact OLe.bind (OLe.refl _) fun c => cond_le c hy hz
    | _ =>
      rcases hy.cases with rfl | rfl
      · cases x <;> exact OLe.none _
      · rcases hz.cases with rfl | rfl
        · cases x <;> cases y <;>
            first
            | exact OLe.none _
            | (show OLe (Storage.push _ _ fun _ => none) _
               rw [Storage.push_none]; exact OLe.none _)
        · exact OLe.refl _

end TypedLe

end Solidity
