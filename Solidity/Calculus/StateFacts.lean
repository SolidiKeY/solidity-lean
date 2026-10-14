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

/-- The shape of a path's segment: a state variable, a member, an array's
index or a mapping's key at a literal (`some`, at its type) or at a term the
syntax does not decide (`none`: a local, a length, the slot past the end),
or an array's length. -/
inductive SegT where
  | root (r : Name)
  | field (f : Name)
  | idx (w : Option ((K : PrimTy) × K.Denote))
  | key (w : Option ((K : PrimTy) × K.Denote))
  | len
  deriving DecidableEq, Repr

/-- The kind of a shape: which label it can fit. -/
def SegT.kind : SegT → Nat
  | .root _ => 0
  | .field _ => 1
  | .idx _ => 2
  | .key _ => 3
  | .len => 4

/-- The kind of a label. -/
def _root_.Solidity.Semantics.Selector.kind : Selector → Nat
  | .root _ => 0
  | .field _ => 1
  | .idx _ => 2
  | .key _ => 3
  | .len => 4

/-- The segment has the shape. -/
def SegT.fits : SegT → Selector → Bool
  | .root r, .root s => r == s
  | .field f, .field g => f == g
  | .idx (some w), .idx j => w == ⟨.uint, j⟩
  | .idx none, .idx _ => true
  | .key (some w), .key k => w == k
  | .key none, .key _ => true
  | .len, .len => true
  | _, _ => false

theorem SegT.fits_kind {x : SegT} {s : Selector} (h : x.fits s = true) : x.kind = s.kind := by
  rcases x with _ | _ | (_ | _) | (_ | _) | _ <;> cases s <;>
    first | rfl | simp only [SegT.fits, Bool.false_eq_true] at h

/-- The path has the shape, segment by segment. -/
def SegT.matches : List SegT → List Selector → Bool
  | [], [] => true
  | x :: a, s :: p => x.fits s && SegT.matches a p
  | _, _ => false

/-- Whether two shapes tell their segments apart: `some true` when the
segments differ in every state (two kinds of segment, two names or two
literal keys), `some false` when they are one segment in every state, `none`
when a symbolic index decides nothing. -/
def SegT.apart (x y : SegT) : Option Bool :=
  if x.kind ≠ y.kind then some true else
  match x, y with
  | .root r, .root s => some (r != s)
  | .field f, .field g => some (f != g)
  | .idx (some v), .idx (some w) => some (v != w)
  | .key (some v), .key (some w) => some (v != w)
  | .len, .len => some false
  | _, _ => none

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
theorem SegT.apart_sound {x y : SegT} {d : Bool} {s t : Selector} (h : x.apart y = some d)
    (hs : x.fits s = true) (ht : y.fits t = true) : (d = true → s ≠ t) ∧ (d = false → s = t) := by
  unfold SegT.apart at h
  split at h
  · rename_i hk
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨fun _ e => hk ?_, fun h => nomatch h⟩
    rw [SegT.fits_kind hs, SegT.fits_kind ht, e]
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      cases s <;> cases t <;> simp_all [SegT.fits]

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
