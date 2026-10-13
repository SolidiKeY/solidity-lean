import Solidity.Calculus.Logic

/-!
# Terms compared: in the Theory and by their syntax

Two scoped value terms equal in the Theory in every state (`Tm.Theq`, what a
law of the Theory says of the terms that denote its sides, the rewrites'
premise: `Proves.rewrite`, `Calculus/SeqRewrite.lean`), and the
sort-generic functions a rewrite or a closer compares terms with: structural
equality across sorts (`Tm.beqR`), the locals a value term built from
literals and operators reads (`Tm.litVarsS`).  Split from
`Calculus/TermLib.lean` at W9.8.3c, so that the sequent's rewrite does not
wait on the term taclets.

**Typed symbols** (W9.8.3c).  A symbol carries the types its sort indices
name and the proofs its typed constructor takes (`C.rootType r = some T`, …),
so two symbols are compared by their constructor, their data and those
types (`Op1.hbeq` …); the proofs are irrelevant, an `IndexTy`/`ArrTy` is
fixed by its indices (`IndexTy.eq`, `ArrTy.eq`).

**Sort-generic recursion.**  A recursive function on `Tm` is generic in the
sort: on one fixed sort it compiles by well-founded recursion and stops
reducing by `rfl` and `decide`.  The ones a kernel check evaluates
(`Tm.litVarsS`, `Tm.beqR`) are written by the recursor, each with its
`match` form as the compiled twin (`…M`) and a link theorem (`…_eq_…M`), as
Gate G0 asks (`Calculus/DecideScoped.lean`).
-/

namespace Solidity

open Theory Theory.StValue
open Solidity (Srt Op0 Op1 Op2 Op3)

variable {C : Contract}

/-! ## Terms equal in the Theory -/

section Theq

variable {Γ : Ctx} {p : PrimTy}

/-- The two terms have the same Theory value in every state: what a law of
the Theory says about the terms that denote its sides. -/
def Tm.Theq (t t' : Tm C Γ (.val p)) : Prop :=
  ∀ σ : State C Γ, Theory.StValue.Equiv (t.denote σ) (t'.denote σ)

theorem Tm.Theq.refl (t : Tm C Γ (.val p)) : Tm.Theq t t := fun _ => StValue.Equiv.refl _

theorem Tm.Theq.symm {t t' : Tm C Γ (.val p)} (h : Tm.Theq t t') : Tm.Theq t' t :=
  fun σ => (h σ).symm

theorem Tm.Theq.trans {t₁ t₂ t₃ : Tm C Γ (.val p)} (h₁ : Tm.Theq t₁ t₂) (h₂ : Tm.Theq t₂ t₃) :
    Tm.Theq t₁ t₃ :=
  fun σ => (h₁ σ).trans (h₂ σ)

/-- Terms whose Theory values are equal are equal in the Theory. -/
theorem Tm.Theq.of_eq {t t' : Tm C Γ (.val p)} (h : ∀ σ : State C Γ, t.denote σ = t'.denote σ) :
    Tm.Theq t t' :=
  fun σ => h σ ▸ StValue.Equiv.refl _

instance : Trans (@Tm.Theq C Γ p) (@Tm.Theq C Γ p) (@Tm.Theq C Γ p) := ⟨Tm.Theq.trans⟩

end Theq

/-! ## Symbols compared -/

/-- An array's kind is fixed by its type. -/
theorem ArrTy.eq {R : RefTy} {E : Ty} : (a b : ArrTy R E) → a = b
  | .dyn, .dyn | .fixed, .fixed => rfl

/-- How a reference type is indexed is fixed by its types. -/
theorem IndexTy.eq {R : RefTy} {k : PrimTy} {V : Ty} (a b : IndexTy R k V) : a = b := by
  cases a with
  | map => cases b with
    | map => rfl
    | arr a => cases a
  | arr a => cases b with
    | map => cases a
    | arr b => rw [ArrTy.eq a b]

deriving instance DecidableEq for Op0

/-- A unary symbol's constructor, data and types, its proofs dropped. -/
inductive Op1Code where
  | unop (op : UnOp) (p : PrimTy) | net | delValue (p : PrimTy) | field (s f : Name) (T : Ty)
  | next (E : Ty) | sval (p : PrimTy) | newArr (R : RefTy) | alloc (R : RefTy)
  | mfield (s f : Name) (T : Ty) | addM (R : RefTy) | mval (p : PrimTy) | ref (R : RefTy) | wt
  | select (s r : Name) | selectIn (s s' f : Name) | fieldIn (s s' f : Name) (T : Ty) | toInt
  deriving DecidableEq

/-- A binary symbol's constructor, data and types, its proofs dropped. -/
inductive Op2Code where
  | binop (op : BinOp) (p : PrimTy) | find (p : PrimTy) | len (E : Ty) | read (p : PrimTy)
  | mlen (E : Ty) | at (R : RefTy) (k : PrimTy) (V : Ty) | nextIn (E : Ty) | delAt (T : Ty)
  | pushSlot (E : Ty) | pop (E : Ty) | shrink (E : Ty) | extend (E : Ty) | sfind (T : Ty)
  | copyMem (R : RefTy) | iread (R : RefTy) | copy (R : RefTy) | mat (R : RefTy) (E : Ty)
  | copySt (T : Ty) | findIn (s : Name) (p : PrimTy) | delAtIn (s : Name) (T : Ty)
  | sfindIn (s : Name) (T : Ty) | zbin (op : BinOp) | zcmp (op : BinOp)
  deriving DecidableEq

/-- A ternary symbol's constructor and types, its proofs dropped. -/
inductive Op3Code where
  | ite (p : PrimTy) | save (T : Ty) | push (E : Ty) | atIn (R : RefTy) (k : PrimTy) (V : Ty)
  | write (T : Ty) | saveIn (s : Name) (T : Ty)
  deriving DecidableEq

/-- A unary symbol's code. -/
def Op1.code {a s : Srt} : Op1 C a s → Op1Code
  | @Op1.unop _ op p _ => .unop op p
  | .net => .net
  | @Op1.delValue _ p => .delValue p
  | @Op1.field _ s f T _ => .field s f T
  | @Op1.next _ E => .next E
  | @Op1.sval _ p => .sval p
  | @Op1.newArr _ R _ => .newArr R
  | .alloc R _ => .alloc R
  | @Op1.mfield _ s f T _ => .mfield s f T
  | .addM R _ => .addM R
  | @Op1.mval _ p => .mval p
  | @Op1.ref _ R => .ref R
  | .wt => .wt
  | @Op1.select _ s r _ => .select s r
  | @Op1.selectIn _ s s₂ f _ => .selectIn s s₂ f
  | @Op1.fieldIn _ s s₂ f T _ => .fieldIn s s₂ f T
  | .toInt => .toInt

/-- A binary symbol's code. -/
def Op2.code {a b s : Srt} : Op2 C a b s → Op2Code
  | @Op2.binop _ op p _ => .binop op p
  | @Op2.find _ p => .find p
  | @Op2.len _ E => .len E
  | @Op2.read _ p => .read p
  | @Op2.mlen _ E => .mlen E
  | @Op2.at _ R k V _ => .at R k V
  | @Op2.nextIn _ E => .nextIn E
  | @Op2.delAt _ T => .delAt T
  | @Op2.pushSlot _ E => .pushSlot E
  | @Op2.pop _ E => .pop E
  | @Op2.shrink _ E => .shrink E
  | @Op2.extend _ E => .extend E
  | @Op2.sfind _ T => .sfind T
  | @Op2.copyMem _ R => .copyMem R
  | @Op2.iread _ R => .iread R
  | @Op2.copy _ R _ => .copy R
  | @Op2.mat _ R E _ => .mat R E
  | @Op2.copySt _ T _ => .copySt T
  | @Op2.findIn _ s p => .findIn s p
  | @Op2.delAtIn _ s T => .delAtIn s T
  | @Op2.sfindIn _ s T => .sfindIn s T
  | .zbin op _ => .zbin op
  | .zcmp op _ => .zcmp op

/-- A ternary symbol's code. -/
def Op3.code {a b c s : Srt} : Op3 C a b c s → Op3Code
  | @Op3.ite _ p => .ite p
  | @Op3.save _ T => .save T
  | @Op3.push _ E => .push E
  | @Op3.atIn _ R k V _ => .atIn R k V
  | @Op3.write _ T => .write T
  | @Op3.saveIn _ s T => .saveIn s T

/-- Two unary symbols are one: constructor, data and types. -/
def Op1.hbeq {a s a' s' : Srt} (o : Op1 C a s) (o' : Op1 C a' s') : Bool := o.code == o'.code

/-- Two binary symbols are one: constructor, data and types. -/
def Op2.hbeq {a b s a' b' s' : Srt} (o : Op2 C a b s) (o' : Op2 C a' b' s') : Bool :=
  o.code == o'.code

/-- Two ternary symbols are one: constructor and types. -/
def Op3.hbeq {a b c s a' b' c' s' : Srt} (o : Op3 C a b c s) (o' : Op3 C a' b' c' s') : Bool :=
  o.code == o'.code

theorem Op1.eq_of_code {a s a' s' : Srt} {o : Op1 C a s} {o' : Op1 C a' s'}
    (h : o.code = o'.code) :
    (⟨(a, s), o⟩ : (q : Srt × Srt) × Op1 C q.1 q.2) = ⟨(a', s'), o'⟩ := by
  cases o <;> cases o' <;> cases h <;> rfl

theorem Op2.eq_of_code {a b s a' b' s' : Srt} {o : Op2 C a b s} {o' : Op2 C a' b' s'}
    (h : o.code = o'.code) :
    (⟨(a, b, s), o⟩ : (q : Srt × Srt × Srt) × Op2 C q.1 q.2.1 q.2.2) = ⟨(a', b', s'), o'⟩ := by
  cases o <;> cases o' <;> cases h <;>
    first
    | rfl
    | exact congrArg (Sigma.mk _) (congrArg Op2.at (IndexTy.eq _ _))
    | exact congrArg (Sigma.mk _) (congrArg Op2.mat (ArrTy.eq _ _))

theorem Op3.eq_of_code {a b c s a' b' c' s' : Srt} {o : Op3 C a b c s}
    {o' : Op3 C a' b' c' s'} (h : o.code = o'.code) :
    (⟨(a, b, c, s), o⟩ : (q : Srt × Srt × Srt × Srt) × Op3 C q.1 q.2.1 q.2.2.1 q.2.2.2) =
      ⟨(a', b', c', s'), o'⟩ := by
  cases o <;> cases o' <;> cases h <;>
    first
    | rfl
    | exact congrArg (Sigma.mk _) (congrArg Op3.atIn (IndexTy.eq _ _))

theorem Op1.eq_of_hbeq {a s a' s' : Srt} {o : Op1 C a s} {o' : Op1 C a' s'}
    (h : o.hbeq o' = true) :
    (⟨(a, s), o⟩ : (q : Srt × Srt) × Op1 C q.1 q.2) = ⟨(a', s'), o'⟩ :=
  Op1.eq_of_code (beq_iff_eq.1 h)

theorem Op2.eq_of_hbeq {a b s a' b' s' : Srt} {o : Op2 C a b s} {o' : Op2 C a' b' s'}
    (h : o.hbeq o' = true) :
    (⟨(a, b, s), o⟩ : (q : Srt × Srt × Srt) × Op2 C q.1 q.2.1 q.2.2) = ⟨(a', b', s'), o'⟩ :=
  Op2.eq_of_code (beq_iff_eq.1 h)

theorem Op3.eq_of_hbeq {a b c s a' b' c' s' : Srt} {o : Op3 C a b c s}
    {o' : Op3 C a' b' c' s'} (h : o.hbeq o' = true) :
    (⟨(a, b, c, s), o⟩ : (q : Srt × Srt × Srt × Srt) × Op3 C q.1 q.2.1 q.2.2.1 q.2.2.2) =
      ⟨(a', b', c', s'), o'⟩ :=
  Op3.eq_of_code (beq_iff_eq.1 h)

theorem Op1.hbeq_self {a s : Srt} (o : Op1 C a s) : o.hbeq o = true := beq_self_eq_true _

theorem Op2.hbeq_self {a b s : Srt} (o : Op2 C a b s) : o.hbeq o = true := beq_self_eq_true _

theorem Op3.hbeq_self {a b c s : Srt} (o : Op3 C a b c s) : o.hbeq o = true :=
  beq_self_eq_true _

/-! ## Sort-generic term functions -/

section Generic

variable {Γ : Ctx}

/-- A local of the context, at its type. -/
abbrev AnyIdx (Γ : Ctx) : Type := (t : LTy) × Idx Γ t

/-- Two lists of locals joined, where both exist. -/
def joinVars {α : Type} : Option (List α) → Option (List α) → Option (List α)
  | some u, some v => some (u ++ v)
  | _, _ => none

/-- `Tm.litVarsS`' compiled twin. -/
def Tm.litVarsSM : {s : Srt} → Tm C Γ s → Option (List (AnyIdx Γ))
  | _, .pvV i => some [⟨_, i⟩]
  | _, .app0 (.lit _) => some []
  | _, .app1 (.unop _ _) a => a.litVarsSM
  | _, .app2 (.binop _ _) a b => joinVars a.litVarsSM b.litVarsSM
  | _, _ => none

/-- **The locals a value term reads when it is built from literals and value
operators alone**, by position; `none` when it reads
anything else.  By the recursor. -/
@[implemented_by Tm.litVarsSM]
def Tm.litVarsS {s : Srt} (t : Tm C Γ s) : Option (List (AnyIdx Γ)) :=
  Tm.rec (motive := fun _ _ => Option (List (AnyIdx Γ)))
    (fun i => some [⟨_, i⟩]) (fun _ => none) (fun _ => none) (fun _ => none)
    (fun _ _ _ => none)
    (@fun s o => match s, o with
      | _, .lit _ => some []
      | _, _ => none)
    (@fun a s o _ ih => match a, s, o with
      | _, _, .unop _ _ => ih
      | _, _, _ => none)
    (@fun a b s o _ _ iha ihb => match a, b, s, o with
      | _, _, _, .binop _ _ => joinVars iha ihb
      | _, _, _, _ => none)
    (fun _ _ _ _ _ _ _ => none) (fun _ => none) t

theorem Tm.litVarsS_eq_litVarsSM {s : Srt} (t : Tm C Γ s) : t.litVarsS = t.litVarsSM := by
  induction t with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ | app3 _ _ _ _ | pvZ _ => rfl
  | app0 o => cases o <;> rfl
  | app1 o x ih => cases o <;> first | rfl | exact ih
  | app2 o x y ihx ihy =>
    cases o <;> first
      | rfl
      | (show joinVars x.litVarsS y.litVarsS = joinVars x.litVarsSM y.litVarsSM
         rw [ihx, ihy])

/-- Two values of a family at two indices are one: the indices are equal,
and so are the values once they are. -/
def hbeqAt {ι : Type} [DecidableEq ι] (F : ι → Type) [∀ i, DecidableEq (F i)] {i j : ι}
    (x : F i) (y : F j) : Bool :=
  if h : i = j then decide (h ▸ x = y) else false

theorem eq_of_hbeqAt {ι : Type} [DecidableEq ι] {F : ι → Type} [∀ i, DecidableEq (F i)]
    {i j : ι} {x : F i} {y : F j} (h : hbeqAt F x y = true) : (⟨i, x⟩ : Sigma F) = ⟨j, y⟩ := by
  unfold hbeqAt at h
  split at h
  · rename_i e
    subst e
    exact congrArg (Sigma.mk i) (of_decide_eq_true h)
  · cases h

theorem hbeqAt_self {ι : Type} [DecidableEq ι] {F : ι → Type} [∀ i, DecidableEq (F i)] {i : ι}
    (x : F i) : hbeqAt F x x = true := by
  simp only [hbeqAt, ↓reduceDIte, decide_true]

/-- Two positions of one context are one local, their types compared too. -/
def Idx.hbeq {t t' : LTy} (i : Idx Γ t) (j : Idx Γ t') : Bool := hbeqAt (Idx Γ) i j

/-- Two constants are one, their sorts compared too. -/
def Op0.hbeq {s s' : Srt} (o : Op0 C s) (o' : Op0 C s') : Bool := hbeqAt (Op0 C) o o'

/-- `Tm.beqR`'s compiled twin. -/
def Tm.beqM : {s s' : Srt} → Tm C Γ s → Tm C Γ s' → Bool
  | _, _, .pvV i, t' => match t' with
    | .pvV j => Idx.hbeq i j
    | _ => false
  | _, _, .pvP i, t' => match t' with
    | .pvP j => Idx.hbeq i j
    | _ => false
  | _, _, .pvS i, t' => match t' with
    | .pvS j => Idx.hbeq i j
    | _ => false
  | _, _, .pvI i, t' => match t' with
    | .pvI j => Idx.hbeq i j
    | _ => false
  | _, _, .netOf i a, t' => match t' with
    | .netOf j a' => Idx.hbeq i j && a.beqM a'
    | _ => false
  | _, _, .app0 o, t' => match t' with
    | .app0 o' => Op0.hbeq o o'
    | _ => false
  | _, _, .app1 o x, t' => match t' with
    | .app1 o' x' => Op1.hbeq o o' && x.beqM x'
    | _ => false
  | _, _, .app2 o x y, t' => match t' with
    | .app2 o' x' y' => Op2.hbeq o o' && x.beqM x' && y.beqM y'
    | _ => false
  | _, _, .app3 o x y z, t' => match t' with
    | .app3 o' x' y' z' => Op3.hbeq o o' && x.beqM x' && y.beqM y' && z.beqM z'
    | _ => false
  | _, _, .pvZ i, t' => match t' with
    | .pvZ j => Idx.hbeq i j
    | _ => false

/-- **Structural equality of two terms**, their sorts compared too, by the
recursor. -/
@[implemented_by Tm.beqM]
def Tm.beqR {s s' : Srt} (t : Tm C Γ s) (t' : Tm C Γ s') : Bool :=
  Tm.rec (motive := fun _ _ => {s' : Srt} → Tm C Γ s' → Bool)
    (@fun _ i _ t' => match t' with
      | .pvV j => Idx.hbeq i j
      | _ => false)
    (@fun _ i _ t' => match t' with
      | .pvP j => Idx.hbeq i j
      | _ => false)
    (@fun i _ t' => match t' with
      | .pvS j => Idx.hbeq i j
      | _ => false)
    (@fun _ i _ t' => match t' with
      | .pvI j => Idx.hbeq i j
      | _ => false)
    (@fun i _ ih _ t' => match t' with
      | .netOf j a' => Idx.hbeq i j && ih a'
      | _ => false)
    (@fun _ o _ t' => match t' with
      | .app0 o' => Op0.hbeq o o'
      | _ => false)
    (@fun _ _ o _ ih _ t' => match t' with
      | .app1 o' x' => Op1.hbeq o o' && ih x'
      | _ => false)
    (@fun _ _ _ o _ _ ihx ihy _ t' => match t' with
      | .app2 o' x' y' => Op2.hbeq o o' && ihx x' && ihy y'
      | _ => false)
    (@fun _ _ _ _ o _ _ _ ihx ihy ihz _ t' => match t' with
      | .app3 o' x' y' z' => Op3.hbeq o o' && ihx x' && ihy y' && ihz z'
      | _ => false)
    (@fun i _ t' => match t' with
      | .pvZ j => Idx.hbeq i j
      | _ => false) t t'

theorem Tm.beqR_eq_beqM {s s' : Srt} (t : Tm C Γ s) (t' : Tm C Γ s') : t.beqR t' = t.beqM t' := by
  induction t generalizing s' with
  | pvV _ | pvP _ | pvS _ | pvI _ | app0 _ | pvZ _ => cases t' <;> rfl
  | netOf i a ih => cases t' <;> first | rfl | (simp only [Tm.beqM, ← ih]; rfl)
  | app1 o x ih => cases t' <;> first | rfl | (simp only [Tm.beqM, ← ih]; rfl)
  | app2 o x y ihx ihy => cases t' <;> first | rfl | (simp only [Tm.beqM, ← ihx, ← ihy]; rfl)
  | app3 o x y z ihx ihy ihz =>
    cases t' <;> first | rfl | (simp only [Tm.beqM, ← ihx, ← ihy, ← ihz]; rfl)

/-- What `beqM` accepts is one term, its sort and all. -/
theorem Tm.eq_of_beqM {s s' : Srt} (t : Tm C Γ s) (t' : Tm C Γ s') (h : t.beqM t' = true) :
    (⟨s, t⟩ : (s : Srt) × Tm C Γ s) = ⟨s', t'⟩ := by
  induction t generalizing s' with
  | pvV i | pvP i | pvS i | pvI i | app0 i | pvZ i =>
    cases t' <;> simp only [Tm.beqM, Bool.false_eq_true] at h
    cases eq_of_hbeqAt h
    rfl
  | netOf i a ih =>
    cases t' <;> simp only [Tm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases eq_of_hbeqAt h1
    cases ih _ h2
    rfl
  | app1 o x ih =>
    cases t' <;> simp only [Tm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases ih _ h2
    cases Op1.eq_of_hbeq h1
    rfl
  | app2 o x y ihx ihy =>
    cases t' <;> simp only [Tm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases ihx _ h2
    cases ihy _ h3
    cases Op2.eq_of_hbeq h1
    rfl
  | app3 o x y z ihx ihy ihz =>
    cases t' <;> simp only [Tm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases ihx _ h2
    cases ihy _ h3
    cases ihz _ h4
    cases Op3.eq_of_hbeq h1
    rfl

theorem Tm.beqM_self {s : Srt} (t : Tm C Γ s) : t.beqM t = true := by
  induction t with
  | pvV i | pvP i | pvS i | pvI i | app0 i | pvZ i =>
    simp only [Tm.beqM, Idx.hbeq, Op0.hbeq, hbeqAt_self]
  | netOf i a ih => simp only [Tm.beqM, Idx.hbeq, hbeqAt_self, ih, Bool.and_self]
  | app1 o x ih => simp only [Tm.beqM, Op1.hbeq_self, ih, Bool.and_self]
  | app2 o x y ihx ihy => simp only [Tm.beqM, Op2.hbeq_self, ihx, ihy, Bool.and_self]
  | app3 o x y z ihx ihy ihz =>
    simp only [Tm.beqM, Op3.hbeq_self, ihx, ihy, ihz, Bool.and_self]

/-- **`beqR` is equality**: what it accepts is one term. -/
theorem Tm.eq_of_beqR {s : Srt} {t t' : Tm C Γ s} (h : t.beqR t' = true) : t = t' :=
  eq_of_heq (Sigma.mk.inj (Tm.eq_of_beqM t t' ((Tm.beqR_eq_beqM t t').symm.trans h))).2

/-- What `beqR` accepts across two sorts is one sort and one term. -/
theorem Tm.sigma_eq_of_beqR {s s' : Srt} {t : Tm C Γ s} {t' : Tm C Γ s'} (h : t.beqR t' = true) :
    (⟨s, t⟩ : (s : Srt) × Tm C Γ s) = ⟨s', t'⟩ :=
  Tm.eq_of_beqM t t' ((Tm.beqR_eq_beqM t t').symm.trans h)

theorem Tm.beqR_self {s : Srt} (t : Tm C Γ s) : t.beqR t = true :=
  (Tm.beqR_eq_beqM t t).trans (Tm.beqM_self t)

theorem Tm.beqR_iff {s : Srt} {t t' : Tm C Γ s} : t.beqR t' = true ↔ t = t' :=
  ⟨Tm.eq_of_beqR, fun h => h ▸ Tm.beqR_self t⟩

end Generic

/-! ## Pins -/

/-- The recursors reduce in the kernel. -/
example : (Tm.app2 (.binop .add (p := .uint) rfl) (.pvV (.here (Γ := []))) (.app0 (.lit ⟨1, rfl⟩)) :
    Tm StandardExample [.val .uint] (.val .uint)).litVarsS = some [⟨_, .here⟩] := rfl

example : (Tm.app2 .find (.app0 .storage) Tm.aliceAge : Tm StandardExample [] (.val .uint)).beqR
    (Tm.app2 .find (.app0 .storage) Tm.aliceAge : Tm StandardExample [] (.val .uint)) = true := by
  decide +kernel

end Solidity
