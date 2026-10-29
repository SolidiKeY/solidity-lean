import Solidity.Calculus.MemFloor
import Solidity.Calculus.AllLeft

/-!
# Scoped instances of a negative memory block

Points and output formulas carry their contexts. Substitution uses the
existing update substitution, which refuses binders, modalities and fresh
allocations in every requested substitution. The low-level empty list has
a vacuous conjunction; the public optional factory refuses empty requests. An unsuccessful point contributes a
vacuous instance, not a default-valued index. This module supplies the
intrinsic instantiation boundary; it does not yet alter `decideMem`.
-/

namespace Solidity.Decide

variable {C : Contract} {Γ Δ : Ctx}

/-- Why a point is retained; this tag grants no semantic permission. -/
inductive MxPointRole where
  | zero | read | length | guard | successor
  deriving DecidableEq, Repr

/-- A scoped uint point with agreement between Theory and evaluation.
Agreement does not assert that the point returns. -/
structure MxPoint (C : Contract) (Γ : Ctx) where
  role : MxPointRole
  tm : Tm C Γ (.val .uint)
  agrees : ∀ σ : State C Γ, tm.denote σ = tm.eval σ

/-- Existing index terms, including checked arithmetic that may halt. -/
def MxPoint.ix (role : MxPointRole) (t : Tm C Γ (.val .uint))
    (ht : t.ixOk = true) : MxPoint C Γ :=
  ⟨role, t, fun σ => Tm.ixOk_denote σ t ht⟩

/-- The fresh array's length remains a typed term in the memory context. -/
def MxPoint.len {q : PrimTy} (i : Idx Γ (.mem (.array (.prim q)))) : MxPoint C Γ :=
  ⟨.length, (MxOrig.len i).tm, fun σ => MxOrig.denote_eq σ (.len i)⟩

/-- Weakening, in particular below a memory binder, cannot capture a
point or turn a failed evaluation into a successful one. -/
def MxPoint.wk (h : Thin Γ Δ) (p : MxPoint C Γ) : MxPoint C Δ where
  role := p.role
  tm := p.tm.wk h
  agrees := fun σ => by
    rw [Tm.denote_wk, Tm.eval_wk]
    exact p.agrees (σ.thin h)

theorem MxPoint.wk_eval (h : Thin Γ Δ) (p : MxPoint C Γ) (σ : State C Δ) :
    (p.wk h).tm.eval σ = p.tm.eval (σ.thin h) := Tm.eval_wk h σ p.tm

theorem MxPoint.underMemory_eval {R : RefTy} (p : MxPoint C Γ) (σ : State C Γ)
    (v : (LTy.mem R).TDenote C σ.H) :
    (p.wk (.drop .refl)).tm.eval (σ.push v) = p.tm.eval σ := by
  rw [MxPoint.wk_eval, mxThin_drop_push]

/-- The checked successor is itself a point. At uint's top it halts;
its definedness guard will make that instance vacuous. -/
def MxPoint.succ (p : MxPoint C Γ) : MxPoint C Γ where
  role := .successor
  tm := .app2 (.binop .add rfl) p.tm (.app0 (.lit (uintOfNat 1)))
  agrees := fun σ => by
    change ((p.tm.denote σ).bind fun v => binopT .add rfl v (some (uintOfNat 1))) = _
    rw [p.agrees]
    rfl

/-- All points stay in the block's parent context. The caller supplies
its scoped exterior read and guard operands; this builder adds zero,
the array length, and checked successors. It is not a completeness claim
for a traversal of arbitrary formulas. -/
def mxBlockPoints {q : PrimTy} (i : Idx Γ (.mem (.array (.prim q))))
    (reads guards : List (MxPoint C Γ)) : List (MxPoint C Γ) :=
  [MxPoint.ix .zero (.app0 (.lit (uintOfNat 0))) rfl, MxPoint.len i] ++
    reads ++ guards ++ guards.map MxPoint.succ

/-- A definedness guard for a point, with the ordinary matching printer. -/
def MxPoint.defined (p : MxPoint C Γ) : Fml C Γ :=
  .eq (.app2 (.binop .eqB rfl) p.tm p.tm) (.app0 (.lit true))

theorem MxPoint.defined_holds (p : MxPoint C Γ) (σ : State C Γ) :
    holds σ p.defined ↔ ∃ v : PrimTy.uint.Denote, p.tm.eval σ = some v := by
  change ((p.tm.denote σ).bind fun v => binopT .eqB rfl v (p.tm.denote σ)) = some true ↔ _
  rw [p.agrees]
  cases he : p.tm.eval σ with
  | none => simp only [Option.bind_none, reduceCtorEq, false_iff, not_exists]
            intro v hv; cases hv
  | some v => rw [Option.bind_some, mxEqB_self]
              exact ⟨fun _ => ⟨v, rfl⟩, fun _ => rfl⟩

/-- Exact substitution across one value binder, conditional only on the
point returning. No equality of failed reads is replaced by defaults. -/
theorem mxInst_holds {x : Var} {φ : Fml C (.val .uint :: Γ)}
    {t : Tm C Γ (.val .uint)} {ψ : Fml C Γ}
    (h : Fml.instTm x .uint φ t = some ψ) (σ : State C Γ)
    {v : PrimTy.uint.Denote} (hv : t.eval σ = some v) :
    holds σ ψ ↔ holds (σ.push (t := .val .uint) v) φ :=
  Fml.substU_holds (Upd.lands_decl (Upd.lands_nil σ) x
    (r := .val t) (v := v) hv) φ h

/-- Term substitution preserves the entire optional evaluation. -/
theorem mxInst_eval {x : Var} {s : Srt} {t : Tm C Γ (.val .uint)}
    {a : Tm C (.val .uint :: Γ) s} {b : Tm C Γ s}
    (h : a.substH (Upd.decl .nil x (.val t)).held true none = some b)
    (σ : State C Γ) {v : PrimTy.uint.Denote} (hv : t.eval σ = some v) :
    b.eval σ = a.eval (σ.push (t := .val .uint) v) :=
  Srt.SameO.eq (Tm.eval_substH
    (Upd.lands_decl (Upd.lands_nil σ) x (r := .val t) (v := v) hv)
    (fun _ hn => Option.noConfusion hn) a h)

/-- The checked finite instances; an unsupported requested substitution
refuses the entire list. An empty list has its vacuous conjunction. Points
that halt are explicitly guarded, never discarded. -/
def mxInstances? (x : Var) (φ : Fml C (.val .uint :: Γ)) :
    List (MxPoint C Γ) → Option (List (Fml C Γ))
  | [] => some []
  | p :: ps => do
    let ψ ← Fml.instTm x .uint φ p.tm
    let rest ← mxInstances? x φ ps
    pure (.imp p.defined ψ :: rest)

/-- Intrinsic first-order instances have exactly their successful point
interpretations. This is stronger than only universal-to-instance soundness. -/
theorem mxInstances_holds (x : Var) (φ : Fml C (.val .uint :: Γ))
    (σ : State C Γ) : ∀ (ps : List (MxPoint C Γ)) {fs : List (Fml C Γ)},
    mxInstances? x φ ps = some fs →
    (holds σ (mxConj fs) ↔ ∀ p ∈ ps, ∀ v : PrimTy.uint.Denote,
      p.tm.eval σ = some v → holds (σ.push (t := .val .uint) v) φ)
  | [], fs, h => by
    cases h
    exact ⟨fun _ _ hp => (nomatch hp), fun _ => trivial⟩
  | p :: ps, fs, h => by
    obtain ⟨ψ, hψ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨rest, hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    change (holds σ p.defined → holds σ ψ) ∧ holds σ (mxConj rest) ↔ _
    rw [mxInstances_holds x φ σ ps hr, p.defined_holds]
    constructor
    · intro h q hq v hv
      rcases List.mem_cons.1 hq with hq | hq
      · subst q
        exact (mxInst_holds hψ σ hv).1 (h.1 ⟨v, hv⟩)
      · exact h.2 q hq v hv
    · intro h
      refine ⟨?_, fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
      intro hp
      obtain ⟨v, hv⟩ := hp
      exact (mxInst_holds hψ σ hv).2 (h p List.mem_cons_self v hv)

/-- The certificate retains its scoped input, points and checked output. -/
structure MxInstPrep (C : Contract) (Γ : Ctx) (x : Var)
    (φ : Fml C (.val .uint :: Γ)) where
  points : List (MxPoint C Γ)
  instances : List (Fml C Γ)
  checked : mxInstances? x φ points = some instances

def MxInstPrep.body {x : Var} {φ : Fml C (.val .uint :: Γ)}
    (p : MxInstPrep C Γ x φ) : Fml C Γ := mxConj p.instances

def mxInstPrep? (x : Var) (φ : Fml C (.val .uint :: Γ)) (ps : List (MxPoint C Γ)) :
    Option (MxInstPrep C Γ x φ) :=
  match ps with
  | [] => none
  | _ :: _ =>
    match h : mxInstances? x φ ps with
    | none => none
    | some fs => some ⟨ps, fs, h⟩

theorem MxInstPrep.holds_iff {x : Var} {φ : Fml C (.val .uint :: Γ)}
    (p : MxInstPrep C Γ x φ) (σ : State C Γ) :
    holds σ p.body ↔ ∀ u ∈ p.points, ∀ v : PrimTy.uint.Denote,
      u.tm.eval σ = some v → holds (σ.push (t := .val .uint) v) φ :=
  mxInstances_holds x φ σ p.points p.checked

theorem MxInstPrep.sound {x : Var} {φ : Fml C (.val .uint :: Γ)}
    (p : MxInstPrep C Γ x φ) (σ : State C Γ)
    (h : holds σ (.all x .uint φ)) : holds σ p.body :=
  (p.holds_iff σ).2 (fun _ _ v _ => h v)

/-- Nested binders are refused rather than substituted with a captured
point. A future extension must supply its own lifting proof. -/
theorem mxInst_nested_refused (x y : Var) (q : PrimTy)
    (φ : Fml C (.val q :: .val .uint :: Γ)) (t : Tm C Γ (.val .uint)) :
    Fml.instTm x .uint (.all y q φ) t = none := rfl

/-- The supported primitive dynamic-array range body, intrinsically
scoped at its parent. Other array identities are not silently merged. -/
def mxRangeInstance {q : PrimTy} (i : Idx Γ (.mem (.array (.prim q))))
    (v : q.Denote) (t : Tm C Γ (.val .uint)) : Fml C Γ :=
  .imp (.eq (.app2 (.binop .gt rfl) (MxOrig.len i).tm t) (.app0 (.lit true)))
    (.eq (.app2 .read (.app0 .memory) (.app2 (.mat .dyn) (.pvI i) t)) (.app0 (.lit v)))

def mxRangeBody {q : PrimTy} (i : Idx Γ (.mem (.array (.prim q))))
    (v : q.Denote) : Fml C (.val .uint :: Γ) :=
  mxRangeInstance (.there i) v (.pvV .here)

/-- The actual first-order substituter computes the intended instance.
The array's de Bruijn index moves down as the uint binder is removed. -/
theorem mxRangeBody_inst (x : Var) {q : PrimTy}
    (i : Idx Γ (.mem (.array (.prim q)))) (v : q.Denote) (t : Tm C Γ (.val .uint)) :
    Fml.instTm x .uint (mxRangeBody i v) t = some (mxRangeInstance i v t) := rfl

/-- Shallow formula views retain the original intrinsic syntax equality. -/
structure MxImpView (φ : Fml C Γ) where
  left : Fml C Γ
  right : Fml C Γ
  eq : φ = .imp left right

def mxImpView (φ : Fml C Γ) : Option (MxImpView φ) := by
  apply @Fml.casesOn C (fun Γ φ => Option (MxImpView φ)) Γ φ
  case imp => exact fun a b => some ⟨a, b, rfl⟩
  all_goals intros; exact none

structure MxEqView (φ : Fml C Γ) where
  p : PrimTy
  left : Tm C Γ (.val p)
  right : Tm C Γ (.val p)
  eq : φ = .eq left right

def mxEqView (φ : Fml C Γ) : Option (MxEqView φ) := by
  apply @Fml.casesOn C (fun Γ φ => Option (MxEqView φ)) Γ φ
  case eq => exact fun {_} {p} a b => some ⟨p, a, b, rfl⟩
  all_goals intros; exact none

/-- The result family inspects the sort, never the indexed term. -/
private def MxLiteralResult {s : Srt} (t : Tm C Γ s) : Type :=
  (match (motive := (s : Srt) → Tm C Γ s → Type) s with
  | .val p => fun t => Option {v : p.Denote // t = Tm.app0 (.lit v)}
  | _ => fun _ => PUnit) t

private def mxLiteralNone {s : Srt} (t : Tm C Γ s) : MxLiteralResult t := by
  cases s <;> first | exact none | exact PUnit.unit

private def mxLiteralOp {s : Srt} (o : Op0 C s) : MxLiteralResult (Tm.app0 (Γ := Γ) o) := by
  apply @Op0.casesOn C (fun s o => MxLiteralResult (Tm.app0 (Γ := Γ) o)) s o
  case lit => exact fun v => some ⟨v, rfl⟩
  all_goals intros; exact mxLiteralNone _

def mxLiteralView {s : Srt} (t : Tm C Γ s) : MxLiteralResult t :=
  @Tm.casesOn C Γ (fun _ t => MxLiteralResult t) s t
    (fun _ => mxLiteralNone _) (fun _ => mxLiteralNone _) (fun _ => mxLiteralNone _)
    (fun _ => mxLiteralNone _) (fun _ _ => mxLiteralNone _) (fun o => mxLiteralOp o)
    (fun _ _ => mxLiteralNone _) (fun _ _ _ => mxLiteralNone _)
    (fun _ _ _ _ => mxLiteralNone _) (fun _ => mxLiteralNone _)

structure MxReadView {p : PrimTy} (t : Tm C Γ (.val p)) where
  addr : Tm C Γ (.addr (.prim p))
  eq : t = .app2 .read (.app0 .memory) addr

private def MxReadResult {s : Srt} (t : Tm C Γ s) : Type :=
  (match (motive := (s : Srt) → Tm C Γ s → Type) s with
  | .val _ => fun t => Option (MxReadView t)
  | _ => fun _ => PUnit) t

private def mxReadNone {s : Srt} (t : Tm C Γ s) : MxReadResult t := by
  cases s <;> first | exact none | exact PUnit.unit

private def mxReadOp {a b s : Srt} (o : Op2 C a b s) :
    (x : Tm C Γ a) → (y : Tm C Γ b) → MxReadResult (Tm.app2 o x y) := by
  apply @Op2.casesOn C (fun a b _ o =>
    (x : Tm C Γ a) → (y : Tm C Γ b) → MxReadResult (Tm.app2 o x y)) a b s o
  case read =>
    exact fun x y => if hx : x.beqR (.app0 .memory) = true then
      some ⟨y, by rw [Tm.eq_of_beqR hx]⟩ else none
  all_goals intros; exact mxReadNone _

def mxReadView {s : Srt} (t : Tm C Γ s) : MxReadResult t :=
  @Tm.casesOn C Γ (fun _ t => MxReadResult t) s t
    (fun _ => mxReadNone _) (fun _ => mxReadNone _) (fun _ => mxReadNone _)
    (fun _ => mxReadNone _) (fun _ _ => mxReadNone _) (fun _ => mxReadNone _)
    (fun _ _ => mxReadNone _) (fun o x y => mxReadOp o x y)
    (fun _ _ _ _ => mxReadNone _) (fun _ => mxReadNone _)

private def MxLocalResult {s : Srt} (t : Tm C Γ s) : Type :=
  (match (motive := (s : Srt) → Tm C Γ s → Type) s with
  | .ident R => fun t => Option {i : Idx Γ (.mem R) // t = Tm.pvI i}
  | _ => fun _ => PUnit) t

private def mxLocalNone {s : Srt} (t : Tm C Γ s) : MxLocalResult t := by
  cases s <;> first | exact none | exact PUnit.unit

private def mxLocalView {s : Srt} (t : Tm C Γ s) : MxLocalResult t :=
  @Tm.casesOn C Γ (fun _ t => MxLocalResult t) s t
    (fun _ => mxLocalNone _) (fun _ => mxLocalNone _) (fun _ => mxLocalNone _)
    (fun i => some ⟨i, rfl⟩) (fun _ _ => mxLocalNone _) (fun _ => mxLocalNone _)
    (fun _ _ => mxLocalNone _) (fun _ _ _ => mxLocalNone _)
    (fun _ _ _ _ => mxLocalNone _) (fun _ => mxLocalNone _)

private def MxAddressResult {s : Srt} (t : Tm C Γ s) : Type :=
  (match (motive := (s : Srt) → Tm C Γ s → Type) s with
  | .addr T => fun t => Option ((R : RefTy) ×
      (r : ArrTy R T × Idx Γ (.mem R) × Tm C Γ (.val .uint)) ×'
      t = Tm.app2 (.mat r.1) (.pvI r.2.1) r.2.2)
  | _ => fun _ => PUnit) t

private def mxAddressNone {s : Srt} (t : Tm C Γ s) : MxAddressResult t := by
  cases s <;> first | exact none | exact PUnit.unit

private def mxAddressOp {a b s : Srt} (o : Op2 C a b s) :
    (x : Tm C Γ a) → (y : Tm C Γ b) → MxAddressResult (Tm.app2 o x y) := by
  apply @Op2.casesOn C (fun a b _ o =>
    (x : Tm C Γ a) → (y : Tm C Γ b) → MxAddressResult (Tm.app2 o x y)) a b s o
  case mat =>
    exact fun a x e => (mxLocalView x).map fun ⟨i, hi⟩ => ⟨_, (a, i, e), by rw [hi]⟩
  all_goals intros; exact mxAddressNone _

/-- Element-address recognition with both term and operator indices generalized. -/
def mxAddressView {s : Srt} (t : Tm C Γ s) : MxAddressResult t :=
  @Tm.casesOn C Γ (fun _ t => MxAddressResult t) s t
    (fun _ => mxAddressNone _) (fun _ => mxAddressNone _) (fun _ => mxAddressNone _)
    (fun _ => mxAddressNone _) (fun _ _ => mxAddressNone _) (fun _ => mxAddressNone _)
    (fun _ _ => mxAddressNone _) (fun o x y => mxAddressOp o x y)
    (fun _ _ _ _ => mxAddressNone _) (fun _ => mxAddressNone _)

/-- Remove one context entry with a motive generalized over both indices. -/
def mxIdxTail {Γ : Ctx} {t : LTy} (i : Idx Γ t) :
    (match (motive := (Γ : Ctx) → Idx Γ t → Type) Γ with
    | _ :: Δ => fun i => Option {j : Idx Δ t // i = Idx.there j}
    | [] => fun _ => PUnit) i :=
  @Idx.casesOn (fun Γ t i => (match (motive := (Γ : Ctx) → Idx Γ t → Type) Γ with
    | _ :: Δ => fun i => Option {j : Idx Δ t // i = Idx.there j}
    | [] => fun _ => PUnit) i) Γ t i
    none (fun i => some ⟨i, rfl⟩)

/-- Exact guard recognition; both terms are checked at their intrinsic
sort, so another array length or another index is refused. -/
def mxRangeGuard? {q : PrimTy} (i : Idx Γ (.mem (.array (.prim q))))
    (g : Fml C (.val .uint :: Γ)) :
    Option (PLift (g = .eq (.app2 (.binop .gt rfl) (MxOrig.len (.there i)).tm (.pvV .here))
      (.app0 (.lit true)))) := do
  let ⟨p, a, b, hg⟩ ← mxEqView g
  if hp : p = .bool then
    if ha : (hp ▸ a).beqR (.app2 (.binop .gt rfl) (MxOrig.len (.there i)).tm (.pvV .here)) = true then
      if hb : (hp ▸ b).beqR (.app0 (.lit (p := .bool) true)) = true then
        some ⟨by
          cases hp
          exact hg.trans (congr (congrArg Fml.eq (Tm.eq_of_beqR ha)) (Tm.eq_of_beqR hb))⟩
      else none
    else none
  else none

/-- A successfully recognized range body, with its actual context and a
proof of the original syntax. No named example is inspected. -/
structure MxRangeView (C : Contract) (Γ : Ctx) (φ : Fml C (.val .uint :: Γ)) where
  q : PrimTy
  array : Idx Γ (.mem (.array (.prim q)))
  value : q.Denote
  eq : φ = mxRangeBody array value

/-- Only a length-guarded primitive read at the removed uint local is
accepted. Nested binders, reference members, fixed arrays and unrelated
array identities fail closed. -/
def mxRangeBody? (φ : Fml C (.val .uint :: Γ)) : Option (MxRangeView C Γ φ) := do
  let ⟨g, c, hφ⟩ ← mxImpView φ
  let ⟨q, lhs, rhs, hc⟩ ← mxEqView c
  let ⟨v, hv⟩ ← mxLiteralView rhs
  let ⟨addr, hread⟩ ← mxReadView lhs
  let ⟨R, (a, i, e), haddr⟩ ← mxAddressView addr
  if hR : R = .array (.prim q) then
    let parentI : Idx (.val .uint :: Γ) (.mem (.array (.prim q))) := hR ▸ i
    let ⟨j, hi⟩ ← mxIdxTail parentI
    if he : e.beqR (.pvV .here) = true then
      (mxRangeGuard? j g).map fun hg =>
        ⟨q, j, v, by
          cases hR
          have ha : a = .dyn := by cases a; rfl
          change i = .there j at hi
          rw [hφ, hc, hread, hv, haddr, ha, hi, Tm.eq_of_beqR he, hg.down]
          rfl⟩
    else none
  else none

/-- The checked output for a recognized range body. The same typed points
are used in the output and in its interpretation certificate. -/
def mxRangeInstances {q : PrimTy} (i : Idx Γ (.mem (.array (.prim q))))
    (v : q.Denote) (ps : List (MxPoint C Γ)) : List (Fml C Γ) :=
  ps.map fun p => .imp p.defined (mxRangeInstance i v p.tm)

theorem mxRangeInstances_checked (x : Var) {q : PrimTy}
    (i : Idx Γ (.mem (.array (.prim q)))) (v : q.Denote) :
    ∀ ps : List (MxPoint C Γ),
      mxInstances? x (mxRangeBody i v) ps = some (mxRangeInstances i v ps)
  | [] => rfl
  | p :: ps => by
    simp only [mxInstances?, mxRangeBody_inst,
      mxRangeInstances_checked x i v ps, mxRangeInstances, List.map_cons]
    rfl

def MxRangeView.prepare {φ : Fml C (.val .uint :: Γ)} (b : MxRangeView C Γ φ)
    (x : Var) (reads guards : List (MxPoint C Γ)) : MxInstPrep C Γ x φ where
  points := mxBlockPoints b.array reads guards
  instances := mxRangeInstances b.array b.value (mxBlockPoints b.array reads guards)
  checked := by
    cases b with
    | mk q i v he =>
      cases he
      exact mxRangeInstances_checked x i v _

/-- An instance at a successful literal reads the actual freshly allocated
object. Both its live length and its optional slot are retained. -/
theorem mxRangeInstance_holds (σ : State C Γ) {q : PrimTy}
    (o : MObj σ.H (.array (.prim q))) (v : q.Denote) (u : PrimTy.uint.Denote) :
    holds (σ.allocPush o) (mxRangeInstance .here v (.app0 (.lit u))) ↔
      (u.1 < ((MObj.elems .dyn o).length : Int) →
        (MObj.elems .dyn o)[u.1.toNat]? = some v) := by
  have hl := mxLenNew_eval σ o
  have hr := mxReadNew_eval σ o .dyn (.app0 (.lit u)) rfl rfl
  have hld : (MxOrig.len (C := C) (Γ := .mem (.array (.prim q)) :: Γ) .here).tm.denote
      (σ.allocPush o) = some (lenU (MObj.elems .dyn o).length (by
        rw [MObj.elems_dyn]; exact o.2)) := by
    rw [MxOrig.denote_eq]
    exact hl
  have hrd : (MxOrig.elem (C := C) (Γ := .mem (.array (.prim q)) :: Γ) .here .dyn
      (.app0 (.lit u)) rfl).tm.denote (σ.allocPush o) = (MObj.elems .dyn o)[u.1.toNat]? := by
    rw [MxOrig.denote_eq]
    simpa only [Tm.wk_app0, Tm.eval, Op0.eval, Option.bind_some] using hr
  change (((MxOrig.len .here).tm.denote (σ.allocPush o)).bind
      (fun n => binopT .gt rfl n (some u)) = some true →
    (MxOrig.elem .here .dyn (.app0 (.lit u)) rfl).tm.denote (σ.allocPush o) = some v) ↔ _
  rw [hld, hrd]
  change (some (decide (((MObj.elems .dyn o).length : Int) > u.1)) = some true → _) ↔ _
  simp only [Option.some.injEq, decide_eq_true_eq]

/-- The intrinsic universal body at an actual fresh allocation is exactly
the optional-slot property used by `mxFloorRebuild_negative_iff`. -/
theorem mxRangeBlock_holds (σ : State C Γ) {q : PrimTy}
    (o : MObj σ.H (.array (.prim q))) (x : Var) (v : q.Denote) :
    holds (σ.allocPush o) (.all x .uint (mxRangeBody .here v)) ↔
      ∀ k : Nat, k < (MObj.elems .dyn o).length →
        (MObj.elems .dyn o)[k]? = some v := by
  have hu : holds (σ.allocPush o) (.all x .uint (mxRangeBody .here v)) ↔
      ∀ u : PrimTy.uint.Denote, u.1 < ((MObj.elems .dyn o).length : Int) →
        (MObj.elems .dyn o)[u.1.toNat]? = some v := by
    constructor
    · intro h u
      exact (mxRangeInstance_holds σ o v u).1
        ((mxInst_holds (mxRangeBody_inst x .here v (.app0 (.lit u))) (σ.allocPush o) rfl).2 (h u))
    · intro h u
      exact (mxInst_holds (mxRangeBody_inst x .here v (.app0 (.lit u))) (σ.allocPush o) rfl).1
        ((mxRangeInstance_holds σ o v u).2 (h u))
  rw [hu]
  constructor
  · intro h k hk
    have hl : (MObj.elems .dyn o).length < 2 ^ 256 := by
      rw [MObj.elems_dyn]
      exact o.2
    have hb : k < 2 ^ 256 := by omega
    have hv := h (uintOfNat k)
    rw [uintOfNat_val hb] at hv
    exact hv (by omega)
  · intro h u hu
    have h0 := mxUint_nonneg u
    exact h u.1.toNat (by omega)

/-- A single bound value has the same range/read interpretation as its
checked intrinsic instance; no binder is swapped across the array. -/
theorem mxRangeBody_holds (σ : State C Γ) {q : PrimTy}
    (o : MObj σ.H (.array (.prim q))) (x : Var) (v : q.Denote) (u : PrimTy.uint.Denote) :
    holds ((σ.allocPush o).push (t := .val .uint) u) (mxRangeBody .here v) ↔
      (u.1 < ((MObj.elems .dyn o).length : Int) →
        (MObj.elems .dyn o)[u.1.toNat]? = some v) :=
  (mxInst_holds (mxRangeBody_inst x .here v (.app0 (.lit u))) (σ.allocPush o) rfl).symm.trans
    (mxRangeInstance_holds σ o v u)

/-- A prepared intrinsic body at a real fresh allocation, not a lowered
storage or ledger interpretation. -/
theorem MxInstPrep.range_holds (σ : State C Γ) {q : PrimTy}
    (o : MObj σ.H (.array (.prim q))) (x : Var) (v : q.Denote)
    (p : MxInstPrep C (.mem (.array (.prim q)) :: Γ) x (mxRangeBody .here v)) :
    holds (σ.allocPush o) p.body ↔
      ∀ pt ∈ p.points, ∀ u : PrimTy.uint.Denote, pt.tm.eval (σ.allocPush o) = some u →
        u.1 < ((MObj.elems .dyn o).length : Int) →
          (MObj.elems .dyn o)[u.1.toNat]? = some v := by
  rw [p.holds_iff]
  simp only [mxRangeBody_holds σ o x v]

/-- Rebuilding the newly allocated object's contents preserves every local
identity in the actual extended heap typing, including its own fresh id. -/
theorem mxFloorRebuild_alloc_local (σ : State C Γ) {q : PrimTy}
    (o : MObj σ.H (.array (.prim q))) (B : List Int) {t : LTy}
    (i : Idx (.mem (.array (.prim q)) :: Γ) t) :
    (σ.allocPush (mxFloorRebuild .dyn (by trivial) o B)).getV i =
      (σ.allocPush o).getV i := rfl

/-- Hence equality/alias observations of memory locals are unchanged by
this one fresh-object reconstruction. This grants no given-heap reduction. -/
theorem mxFloorRebuild_alloc_alias (σ : State C Γ) {q : PrimTy}
    (o : MObj σ.H (.array (.prim q))) (B : List Int) {R : RefTy}
    (i j : Idx (.mem (.array (.prim q)) :: Γ) (.mem R)) :
    ((σ.allocPush (mxFloorRebuild .dyn (by trivial) o B)).getV i =
      (σ.allocPush (mxFloorRebuild .dyn (by trivial) o B)).getV j) ↔
    ((σ.allocPush o).getV i = (σ.allocPush o).getV j) := by
  rw [mxFloorRebuild_alloc_local, mxFloorRebuild_alloc_local]

/-- A checked intrinsic preparation realizes the original range block in
the reconstructed fresh allocation when its retained natural breakpoints
are covered by successful scoped points. This explicitly exposes the
coverage obligation a whole-leaf collector must discharge. -/
theorem MxInstPrep.range_reconstruct (σ : State C Γ) {q : PrimTy}
    (o : MObj σ.H (.array (.prim q))) (x : Var) (v : q.Denote)
    (p : MxInstPrep C (.mem (.array (.prim q)) :: Γ) x (mxRangeBody .here v))
    (B : List Int) (hn : ((MObj.elems .dyn o).length : Int) ∈ B)
    (hc : ∀ k : Nat, k = 0 ∨ (k : Int) ∈ B → k < (MObj.elems .dyn o).length →
      ∃ pt ∈ p.points, ∃ u : PrimTy.uint.Denote,
        pt.tm.eval (σ.allocPush o) = some u ∧ u.1.toNat = k)
    (h : holds (σ.allocPush o) p.body) :
    holds (σ.allocPush (mxFloorRebuild .dyn (by trivial) o B))
      (.all x .uint (mxRangeBody .here v)) := by
  rw [mxRangeBlock_holds]
  apply mxFloorRebuild_block .dyn (by trivial) o B hn (fun w => w = some v)
  intro k hk hlen
  obtain ⟨pt, hpt, u, hu, hku⟩ := hc k hk hlen
  have hp := (p.range_holds σ o x v).1 h pt hpt u hu
  have h0 := mxUint_nonneg u
  rw [hku] at hp
  exact hp (by omega)

#print axioms mxFloorRebuild_alloc_alias
#print axioms MxInstPrep.range_reconstruct

/-- Only successfully evaluated uint points enter the numeric floor set. -/
def mxPointValues (σ : State C Γ) (ps : List (MxPoint C Γ)) : List Int :=
  ps.filterMap fun p => (p.tm.eval σ).map Subtype.val

theorem mxPointValues_mem (σ : State C Γ) (ps : List (MxPoint C Γ)) {k : Int}
    (hk : k ∈ mxPointValues σ ps) :
    ∃ p ∈ ps, ∃ u : PrimTy.uint.Denote, p.tm.eval σ = some u ∧ u.1 = k := by
  obtain ⟨p, hp, hv⟩ := List.mem_filterMap.1 hk
  obtain ⟨u, hu, he⟩ := Option.map_eq_some_iff.1 hv
  exact ⟨p, hp, u, hu, he⟩

/-- Zero and length are explicit breakpoints, even when no array read
returns. Other points enter only through actual successful evaluation. -/
def mxRangeBreaks (σ : State C Γ) {q : PrimTy} (o : MObj σ.H (.array (.prim q)))
    (ps : List (MxPoint C (.mem (.array (.prim q)) :: Γ))) : List Int :=
  ((MObj.elems .dyn o).length : Int) :: 0 :: mxPointValues (σ.allocPush o) ps

/-- Numeric coverage follows from the actual typed point list plus its
zero instance. Length need not be a live instance: it is exactly the
first excluded read, including at length zero. -/
theorem MxInstPrep.range_reconstruct_points (σ : State C Γ) {q : PrimTy}
    (o : MObj σ.H (.array (.prim q))) (x : Var) (v : q.Denote)
    (p : MxInstPrep C (.mem (.array (.prim q)) :: Γ) x (mxRangeBody .here v))
    (hz : ∃ pt ∈ p.points, pt.tm.eval (σ.allocPush o) = some (uintOfNat 0))
    (h : holds (σ.allocPush o) p.body) :
    holds (σ.allocPush (mxFloorRebuild .dyn (by trivial) o (mxRangeBreaks σ o p.points)))
      (.all x .uint (mxRangeBody .here v)) := by
  apply p.range_reconstruct σ o x v _ List.mem_cons_self ?_ h
  intro k hk hlen
  have zero : ∃ pt ∈ p.points, ∃ u : PrimTy.uint.Denote,
      pt.tm.eval (σ.allocPush o) = some u ∧ u.1.toNat = 0 := by
    obtain ⟨pt, hpt, hp⟩ := hz
    exact ⟨pt, hpt, uintOfNat 0, hp, rfl⟩
  rcases hk with hk | hk
  · subst k
    exact zero
  · rcases List.mem_cons.1 hk with hk | hk
    · omega
    · rcases List.mem_cons.1 hk with hk | hk
      · have he : k = 0 := by omega
        subst k
        exact zero
      · obtain ⟨pt, hpt, u, hu, he⟩ := mxPointValues_mem (σ.allocPush o) p.points hk
        exact ⟨pt, hpt, u, hu, by omega⟩

#print axioms MxInstPrep.range_reconstruct_points

/-- The earlier object reduction now has an intrinsic range-block boundary
at actual allocation. The consequent is still specified by its observations;
this theorem does not recognize or rewrite an arbitrary enclosing formula. -/
theorem mxRangeBlock_negative_iff (σ : State C Γ) {q : PrimTy} (x : Var) (v : q.Denote)
    (points : MObj σ.H (.array (.prim q)) → List Int) (reads : List Nat)
    (hn : ∀ o, ((MObj.elems .dyn o).length : Int) ∈ points o)
    (hr : ∀ o k, k ∈ reads → (k : Int) ∈ points o)
    (Q : Nat → List (Option q.Denote) → Prop) :
    (∀ o : MObj σ.H (.array (.prim q)),
      holds (σ.allocPush o) (.all x .uint (mxRangeBody .here v)) →
      Q (MObj.elems .dyn o).length (reads.map fun k => (MObj.elems .dyn o)[k]?)) ↔
    (∀ o : MObj σ.H (.array (.prim q)),
      (∀ k : Nat, k = 0 ∨ (k : Int) ∈ points o →
        k < (MObj.elems .dyn o).length → (MObj.elems .dyn o)[k]? = some v) →
      Q (MObj.elems .dyn o).length (reads.map fun k => (MObj.elems .dyn o)[k]?)) := by
  simp only [mxRangeBlock_holds]
  exact mxFloorRebuild_negative_iff .dyn (by trivial) points reads hn hr
    (fun _ w => w = some v) Q

#print axioms mxRangeBody_inst
#print axioms mxRangeBlock_holds
#print axioms mxRangeBlock_negative_iff

#print axioms mxInst_holds
#print axioms mxInst_eval
#print axioms MxInstPrep.holds_iff
#print axioms MxPoint.underMemory_eval

end Solidity.Decide
