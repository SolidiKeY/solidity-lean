import Solidity.Calculus.DecideLang
import Solidity.Calculus.TermEq

/-!
# Deciding the storage goals: `sol_decide`

`sol_close` (`Calculus/Close.lean`) is a tactic: it proves what its `simp`
set and the facts the formula states reach, and a goal it leaves open may be
valid.  Two storage keys the formula does not separate are the typical case:
`[ balances[k] = 5; balances[j] = 5; ] balances[k] == 5` is valid, since
either write leaves `5`, but no fact says `k = j` or `k ≠ j`.  This module is
mini-solkey's Chapter 15 (`Ch15_Decide`) for the storage fragment: the
search replaced by a function, and a proof that the function loses nothing.

* `Fml.toLS` (`Calculus/DecideScoped.lean`) pushes the updates `sol_symex`
  leaves into the formula, its locals by position (mini-solkey's
  `Fml.applyUpds`): a term of the reduction is the scoped term with its
  locals, `storage` and `memory` replaced by what the updates bound them to.
* `LFml.elim` (here) turns every read of a write into a case tree over key
  equalities whose leaves observe the starting storage only (`LTm.obsW`,
  `obsL`, `obsH`).  It is the typed Theory read symbolically
  (`Theory/Typed/Obs.lean`): a storage is its observations, a write is a
  `save` of what the location holds with the operation made on it, and a
  read compares its path with the written one (`relSegs`, the symbolic
  `Path.strip?`): below it, the read is the operation's own reading of the
  rest (`delRS`, `ovRS`, `pushRd`, … the symbolic `TVal.delR`, `ovR`,
  `pushA`, …); apart from it, the old read.  The elimination keeps what a
  term reads, as an equality (`LTm.elim_eval`).
* `sol_decide` (`Calculus/DecideComplete.lean`) reduces the goal by both,
  computes the reduction, and decides it over the observations.

A term the elimination has no reading for (a memory read, a path it cannot
follow) is kept as it is (`ElimM.ofOrig`): still exact, only left to the
closer.

The functions the kernel evaluates (`relSegs`, the readers, `LTm.elim`) are
written with the recursors (Gate G0, conditions 1 and 2), each with a
`match` twin for compiled code; the twins of the readers are closures, so a
reader computes only what a leaf asks for.
-/

namespace Solidity

namespace Decide

open Semantics

variable {C : Contract}

/-! ## Terms compared -/

section Beq

/-- `LTm.beqR`'s compiled twin. -/
def LTm.beqM : {s s' : Srt} → LTm C s → LTm C s' → Bool
  | _, _, @LTm.var _ p k, t' => match t' with
    | @LTm.var _ p' k' => p == p' && k == k'
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
  | _, _, @LTm.index _ R k V _ q i, t' => match t' with
    | @LTm.index _ R' k' V' _ q' i' => decide (R = R' ∧ k = k' ∧ V = V') && q.beqM q' && i.beqM i'
    | _ => false
  | _, _, .obsW q, t' => match t' with
    | .obsW q' => q.beqM q'
    | _ => false
  | _, _, .obsL q, t' => match t' with
    | .obsL q' => q.beqM q'
    | _ => false
  | _, _, .obsH q, t' => match t' with
    | .obsH q' => q.beqM q'
    | _ => false
  | _, _, .seq d a, t' => match t' with
    | .seq d' a' => d.beqM d' && a.beqM a'
    | _ => false
  | _, _, .orElse a b, t' => match t' with
    | .orElse a' b' => a.beqM a' && b.beqM b'
    | _ => false
  | _, _, .kite a b t e, t' => match t' with
    | .kite a' b' t'' e' => a.beqM a' && b.beqM b' && t.beqM t'' && e.beqM e'
    | _ => false
  | s, _, .err, t' => match t' with
    | @LTm.err _ s' => s == s'
    | _ => false

/-- **Structural equality of two terms**, their sorts compared too, by the
recursor. -/
@[implemented_by LTm.beqM]
def LTm.beqR {s s' : Srt} (t : LTm C s) (t' : LTm C s') : Bool :=
  @LTm.rec C (fun _ _ => {s' : Srt} → LTm C s' → Bool)
    (@fun p k _ t' => match t' with
      | @LTm.var _ p' k' => p == p' && k == k'
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
    (@fun R k V _ _ _ ihq ihi _ t' => match t' with
      | @LTm.index _ R' k' V' _ q' i' => decide (R = R' ∧ k = k' ∧ V = V') && ihq q' && ihi i'
      | _ => false)
    (@fun _ _ ih _ t' => match t' with
      | .obsW q' => ih q'
      | _ => false)
    (@fun _ _ ih _ t' => match t' with
      | .obsL q' => ih q'
      | _ => false)
    (@fun _ _ ih _ t' => match t' with
      | .obsH q' => ih q'
      | _ => false)
    (@fun _ _ _ _ ihd iha _ t' => match t' with
      | .seq d' a' => ihd d' && iha a'
      | _ => false)
    (@fun _ _ _ iha ihb _ t' => match t' with
      | .orElse a' b' => iha a' && ihb b'
      | _ => false)
    (@fun _ _ _ _ _ _ iha ihb iht ihe _ t' => match t' with
      | .kite a' b' t'' e' => iha a' && ihb b' && iht t'' && ihe e'
      | _ => false)
    (@fun s _ t' => match t' with
      | @LTm.err _ s' => s == s'
      | _ => false) s t s' t'

theorem LTm.beqR_eq_beqM {s s' : Srt} (t : LTm C s) (t' : LTm C s') : t.beqR t' = t.beqM t' := by
  induction t generalizing s' with
  | var | app0 | err => cases t' <;> rfl
  | app1 o x ih => cases t' <;> first | rfl | (simp only [LTm.beqM, ← ih]; rfl)
  | app2 o x y ihx ihy => cases t' <;> first | rfl | (simp only [LTm.beqM, ← ihx, ← ihy]; rfl)
  | app3 o x y z ihx ihy ihz =>
    cases t' <;> first | rfl | (simp only [LTm.beqM, ← ihx, ← ihy, ← ihz]; rfl)
  | index it q i ihq ihi => cases t' <;> first | rfl | (simp only [LTm.beqM, ← ihq, ← ihi]; rfl)
  | obsW q ih | obsL q ih | obsH q ih => cases t' <;> first | rfl | (simp only [LTm.beqM, ← ih]; rfl)
  | seq d a ihd iha => cases t' <;> first | rfl | (simp only [LTm.beqM, ← ihd, ← iha]; rfl)
  | orElse a b iha ihb => cases t' <;> first | rfl | (simp only [LTm.beqM, ← iha, ← ihb]; rfl)
  | kite a b t e iha ihb iht ihe =>
    cases t' <;> first | rfl | (simp only [LTm.beqM, ← iha, ← ihb, ← iht, ← ihe]; rfl)

/-- What `beqM` accepts is one term, its sort and all. -/
theorem LTm.eq_of_beqM {s s' : Srt} (t : LTm C s) (t' : LTm C s') (h : t.beqM t' = true) :
    (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨s', t'⟩ := by
  induction t generalizing s' with
  | var k =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | app0 o =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true] at h
    cases eq_of_hbeqAt h
    rfl
  | err =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, beq_iff_eq] at h
    cases h
    rfl
  | app1 o x ih =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases ih _ h2
    cases Op1.eq_of_hbeq h1
    rfl
  | app2 o x y ihx ihy =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases ihx _ h2
    cases ihy _ h3
    cases Op2.eq_of_hbeq h1
    rfl
  | app3 o x y z ihx ihy ihz =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases ihx _ h2
    cases ihy _ h3
    cases ihz _ h4
    cases Op3.eq_of_hbeq h1
    rfl
  | index it q i ihq ihi =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl, rfl⟩, h2⟩, h3⟩ := h
    cases ihq _ h2
    cases ihi _ h3
    rename_i it'
    cases IndexTy.eq it it'
    rfl
  | obsW q ih | obsL q ih | obsH q ih =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true] at h
    cases ih _ h
    rfl
  | seq d a ihd iha =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    cases ihd _ h.1
    cases iha _ h.2
    rfl
  | orElse a b iha ihb =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    cases iha _ h.1
    cases ihb _ h.2
    rfl
  | kite a b t e iha ihb iht ihe =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases iha _ h1
    cases ihb _ h2
    cases iht _ h3
    cases ihe _ h4
    rfl

/-- What `beqR` accepts across two sorts is one sort and one term. -/
theorem LTm.sigma_eq_of_beqR {s s' : Srt} {t : LTm C s} {t' : LTm C s'} (h : t.beqR t' = true) :
    (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨s', t'⟩ :=
  LTm.eq_of_beqM t t' ((LTm.beqR_eq_beqM t t').symm.trans h)

/-- **`beqR` is equality**: what it accepts is one term. -/
theorem LTm.eq_of_beqR {s : Srt} {t t' : LTm C s} (h : t.beqR t' = true) : t = t' :=
  eq_of_heq (Sigma.mk.inj (LTm.sigma_eq_of_beqR h)).2

end Beq

/-! ## Literals, and symbols folded on them -/

/-- A literal, read at its own type. -/
def LTm.litV? {p : PrimTy} (t : LTm C (.val p)) : Option p.Denote :=
  match t with
  | .app0 (.lit v) => some v
  | _ => none

theorem LTm.eq_of_litV? {p : PrimTy} {t : LTm C (.val p)} {v : p.Denote} (h : t.litV? = some v) :
    t = .lit v := by
  unfold LTm.litV? at h
  split at h
  · cases h; rfl
  · cases h

/-- `a ⊖`, folded on a literal. -/
def fold1 {a s : Srt} (o : Op1 C a s) (x : LTm C a) : LTm C s :=
  match o, x with
  | .unop op h, x =>
    match x.litV? with
    | some v =>
      match op.evalT h v with
      | some r => .lit r
      | none => .err
    | none => .app1 (.unop op h) x
  | o, x => .app1 o x

/-- An exponent past `256`: a power is not folded on it (`Int.pow`
recurses once per unit of it, heeding no heartbeats). -/
def expBig : {p : PrimTy} → p.Denote → Bool
  | .uint, v => decide (256 < v.1)
  | .int, v => decide (256 < v.1)
  | .bool, _ => false

/-- `a ⊕ b`, folded on literals: `&&`/`||` on a literal left operand,
any operator on two. -/
def fold2 {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) : LTm C s :=
  match o, x, y with
  | .binop op h, x, y =>
    match x.litV? with
    | some u =>
      match op.shortT u with
      | some r => .lit r
      | none =>
        match y.litV? with
        | some v =>
          if (op == .pow || op == .powW) && expBig v then .app2 (.binop op h) x y
          else
            match op.evalT h u v with
            | some r => .lit r
            | none => .err
        | none => .app2 (.binop op h) x y
    | none => .app2 (.binop op h) x y
  | o, x, y => .app2 o x y



/-- Native modular arithmetic folds only when all three operands are literals. -/
def foldModular (op : ModOp) (x y k : LTm C (.val .uint)) : LTm C (.val .uint) :=
  match x.litV?, y.litV?, k.litV? with
  | some a, some b, some m =>
    match op.evalT a b m with
    | some r => .lit r
    | none => .err
  | _, _, _ => .app3 (.modular op) x y k

section FoldEval

variable (g : State C []) (ν : AEnv)

/-- Folding a native modular call preserves failure and the complete typed result. -/
theorem foldModular_eval (op : ModOp) (x y k : LTm C (.val .uint)) :
    (foldModular op x y k).eval g ν = (LTm.app3 (.modular op) x y k).eval g ν := by
  unfold foldModular
  split
  · rename_i a b m ha hb hm
    obtain rfl := LTm.eq_of_litV? ha
    obtain rfl := LTm.eq_of_litV? hb
    obtain rfl := LTm.eq_of_litV? hm
    cases h : op.evalT a b m with
    | none =>
      show none = op.evalT a b m
      exact h.symm
    | some v =>
      show some v = op.evalT a b m
      exact h.symm
  · rfl

theorem fold1_eval {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    (fold1 o x).eval g ν = (LTm.app1 o x).eval g ν := by
  cases o <;> try rfl
  rename_i op p h
  simp only [fold1]
  split
  · rename_i v hv
    obtain rfl := LTm.eq_of_litV? hv
    split <;> rename_i r hr
    · show some r = (some v).bind (op.evalT h)
      rw [Option.bind_some, hr]
    · show none = (some v).bind (op.evalT h)
      rw [Option.bind_some, hr]
  · rfl

theorem fold2_eval {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    (fold2 o x y).eval g ν = (LTm.app2 o x y).eval g ν := by
  cases o <;> try rfl
  rename_i op p h
  simp only [fold2]
  split
  · rename_i u hu
    obtain rfl := LTm.eq_of_litV? hu
    show _ = binopT op h u _
    unfold binopT
    split
    · rename_i r hr
      rw [hr]; rfl
    · rename_i hr
      rw [hr]
      split
      · rename_i v hv
        obtain rfl := LTm.eq_of_litV? hv
        show _ = (some v).bind (op.evalT h u)
        split
        · show binopT op h u (some v) = _
          unfold binopT
          rw [hr]
        · rw [Option.bind_some]
          split <;> rename_i r' hr' <;> rw [hr'] <;> rfl
      · show binopT op h u _ = _
        unfold binopT
        rw [hr]
  · rfl

end FoldEval

/-! ## Symbolic paths

A storage path the elimination reads, root first: a root and its segments,
each key a term (`TSegs`, the symbolic `Path`). -/

/-- The segments of a path from a `T` to a `U`, keys as terms: the
symbolic `Path`. -/
inductive TSegs (C : Contract) : Ty → Ty → Type where
  | nil {T : Ty} : TSegs C T T
  | field {s f : Name} {T U : Ty} (h : lookupBy f (structDef s) = some T) (rest : TSegs C T U) :
      TSegs C (.ref (.struct s)) U
  | at {E U : Ty} (i : LTm C (.val .uint)) (rest : TSegs C E U) : TSegs C (.ref (.array E)) U
  | atF {E U : Ty} {n : Nat} (i : LTm C (.val .uint)) (rest : TSegs C E U) :
      TSegs C (.ref (.fixed E n)) U
  | key {k : PrimTy} {V U : Ty} (i : LTm C (.val k)) (rest : TSegs C V U) :
      TSegs C (.ref (.mapping k V)) U

namespace TSegs

/-- `append` by `match`, its compiled form. -/
def appendM : {S U W : Ty} → TSegs C S U → TSegs C U W → TSegs C S W
  | _, _, _, .nil, q => q
  | _, _, _, .field h p, q => .field h (p.appendM q)
  | _, _, _, .at i p, q => .at i (p.appendM q)
  | _, _, _, .atF i p, q => .atF i (p.appendM q)
  | _, _, _, .key i p, q => .key i (p.appendM q)

/-- Segments followed by more. -/
@[implemented_by appendM]
def append {S U W : Ty} (p : TSegs C S U) (q : TSegs C U W) : TSegs C S W :=
  @TSegs.rec C (fun _ U _ => TSegs C U W → TSegs C _ W) (fun q => q)
    (fun h _ ih q => .field h (ih q)) (fun i _ ih q => .at i (ih q))
    (fun i _ ih q => .atF i (ih q)) (fun i _ ih q => .key i (ih q)) S U p q

theorem append_eq_appendM {S U W : Ty} (p : TSegs C S U) (q : TSegs C U W) :
    p.append q = p.appendM q := by
  induction p with
  | nil => rfl
  | field _ _ ih => exact congrArg _ (ih _)
  | atF _ _ ih => exact congrArg _ (ih _)
  | key _ _ ih => exact congrArg _ (ih _)
  | «at» _ _ ih => exact congrArg _ (ih _)

/-- `toLTm` by `match`, its compiled form. -/
def toLTmM : {S T : Ty} → TSegs C S T → LTm C (.path S) → LTm C (.path T)
  | _, _, .nil, acc => acc
  | _, _, .field h p, acc => p.toLTmM (.app1 (.field h) acc)
  | _, _, .at i p, acc => p.toLTmM (.index (.arr .dyn) acc i)
  | _, _, .atF i p, acc => p.toLTmM (.index (.arr .fixed) acc i)
  | _, _, .key i p, acc => p.toLTmM (.index .map acc i)

/-- The path term the segments make below `acc`: a member by `field`, an
index by the unchecked `LTm.index`. -/
@[implemented_by toLTmM]
def toLTm {S T : Ty} (p : TSegs C S T) : LTm C (.path S) → LTm C (.path T) :=
  @TSegs.rec C (fun S T _ => LTm C (.path S) → LTm C (.path T)) (fun acc => acc)
    (fun h _ ih acc => ih (.app1 (.field h) acc))
    (fun i _ ih acc => ih (.index (.arr .dyn) acc i))
    (fun i _ ih acc => ih (.index (.arr .fixed) acc i))
    (fun i _ ih acc => ih (.index .map acc i)) S T p

theorem toLTm_eq_toLTmM {S T : Ty} (p : TSegs C S T) : p.toLTm = p.toLTmM := by
  funext acc
  induction p with
  | nil => rfl
  | field h p ih | «at» i p ih | atF i p ih | key i p ih => simp only [TSegs.toLTmM, ← ih]; rfl

/-- One index step, by how the type is indexed. -/
def ofIndex {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) :
    LTm C (.val k) → TSegs C (.ref R) V :=
  @IndexTy.casesOn (fun R k V _ => LTm C (.val k) → TSegs C (.ref R) V) R k V it
    (fun {_} {_} i => .key i .nil)
    (fun {_} {_} a => @ArrTy.casesOn (fun R E _ => LTm C (.val .uint) → TSegs C (.ref R) E) _ _ a
      (fun {_} i => .at i .nil) (fun {_} {_} i => .atF i .nil))

/-- The path the segments name, their keys read in `g` and `ν`. -/
noncomputable def eval (g : State C []) (ν : AEnv) {T U : Ty} (p : TSegs C T U) :
    Option (Path T U) :=
  @TSegs.rec C (fun T U _ => Option (Path T U)) (some .nil)
    (fun h _ ih => ih.map (.field h))
    (fun i _ ih => (i.eval g ν : Option PrimTy.uint.Denote).bind fun k => ih.map (.at k))
    (fun i _ ih => (i.eval g ν : Option PrimTy.uint.Denote).bind fun k => ih.map (.atF k))
    (fun {k} {_} {_} i _ ih => (i.eval g ν : Option k.Denote).bind fun j =>
      ih.map (.key j))
    T U p

end TSegs

/-- A symbolic storage path: a root and the segments below it. -/
structure SPath (C : Contract) (T : Ty) where
  r : Name
  {R : Ty}
  hr : C.rootType r = some R
  segs : TSegs C R T

namespace SPath

/-- The path one or more segments further. -/
def snoc {T U : Ty} (P : SPath C T) (s : TSegs C T U) : SPath C U := ⟨P.r, P.hr, P.segs.append s⟩

/-- The path as a term. -/
def toLTm {T : Ty} (P : SPath C T) : LTm C (.path T) := P.segs.toLTm (.app0 (.root P.r P.hr))

/-- The reference the path names, its keys read in `g` and `ν`. -/
noncomputable def eval (g : State C []) (ν : AEnv) {T : Ty} (P : SPath C T) : Option (SRef C T) :=
  (P.segs.eval g ν).map fun p => ⟨P.r, P.hr, p⟩

end SPath

/-! ## Comparing a write with a read

`relSegs P Q` is the symbolic `Path.strip? P Q`: the rest of `Q` past `P`
where `Q` goes through `P`, `none` where it does not (it is above `P`, or
apart), as a case tree over the keys the terms alone do not settle. -/

/-- A value that depends on key equalities. -/
inductive CTree (C : Contract) (α : Type) where
  | leaf (a : α)
  | node {p : PrimTy} (a b : LTm C (.val p)) (t e : CTree C α)

/-- A tree of terms as one term, its tests `kite`s. -/
def CTree.toTerm {α : Type} {q : PrimTy} (f : α → LTm C (.val q)) : CTree C α → LTm C (.val q)
  | .leaf a => f a
  | .node a b t e => .kite a b (t.toTerm f) (e.toTerm f)

/-- What a key term is, to the comparison: a local, a literal (as the
integer it is hashed as), a value of the transaction, or something else. -/
inductive KV where
  | var (k : Nat)
  | lit (v : Int)
  | env (k : EnvKey)
  | other

/-- The key view of a term, by `casesOn`. -/
def LTm.keyView {s : Srt} (t : LTm C s) : KV :=
  @LTm.casesOn C (fun _ _ => KV) s t
    (fun k => .var k)
    (fun o => @Op0.casesOn C (fun _ _ => KV) _ o (fun v => .lit (PrimTy.key v)) (fun k => .env k)
      (fun _ _ _ => .other) .other .other .other (fun _ _ _ _ => .other) (fun _ => .other))
    (fun _ _ => .other) (fun _ _ _ => .other) (fun _ _ _ _ => .other) (fun _ _ _ => .other)
    (fun _ => .other) (fun _ => .other) (fun _ => .other) (fun _ _ => .other)
    (fun _ _ => .other) (fun _ _ _ _ => .other) .other

/-- Two keys the terms alone compare: the same local or value of the
transaction is the same key, two literals are compared. -/
def keyCmp {p : PrimTy} (a b : LTm C (.val p)) : Option Bool :=
  match a.keyView, b.keyView with
  | .var x, .var y => if x = y then some true else none
  | .env x, .env y => if x = y then some true else none
  | .lit x, .lit y => some (decide (x = y))
  | _, _ => none

/-- A test on two keys, settled where the terms settle it. -/
def keyTree {α : Type} {p : PrimTy} (a b : LTm C (.val p)) (t e : CTree C α) : CTree C α :=
  match keyCmp a b with
  | some true => t
  | some false => e
  | none => .node a b t e

theorem field_ty_eq {s s' f f' : Name} {T T' : Ty} (h : lookupBy f (structDef s) = some T)
    (h' : lookupBy f' (structDef s') = some T') (e : Ty.ref (.struct s') = .ref (.struct s))
    (ef : f = f') : T' = T := by
  injection e with e; injection e with e; subst e; subst ef
  exact Option.some.inj (h'.symm.trans h)

theorem array_inj {E E' : Ty} (h : Ty.ref (.array E') = .ref (.array E)) : E' = E := by
  injection h with h; injection h

theorem fixed_inj {E E' : Ty} {n n' : Nat} (h : Ty.ref (.fixed E' n') = .ref (.fixed E n)) :
    E' = E := by
  injection h with h; injection h

theorem mapping_inj {k k' : PrimTy} {V V' : Ty}
    (h : Ty.ref (.mapping k' V') = .ref (.mapping k V)) : k' = k ∧ V' = V := by
  injection h with h; injection h with h₁ h₂; exact ⟨h₁, h₂⟩

/-- `relSegs` by `match`, its compiled form. -/
def relSegsM : {S T : Ty} → TSegs C S T → {U : Ty} → TSegs C S U →
    CTree C (Option (TSegs C T U))
  | _, _, .nil, _, q => .leaf (some q)
  | _, _, @TSegs.field _ _ f _ _ h p, _, @TSegs.field _ _ f' _ _ h' q =>
    if e : f = f' then relSegsM p (field_ty_eq h h' rfl e ▸ q) else .leaf none
  | _, _, .at i p, _, .at j q => keyTree i j (relSegsM p q) (.leaf none)
  | _, _, .atF i p, _, .atF j q => keyTree i j (relSegsM p q) (.leaf none)
  | _, _, .key i p, _, .key j q => keyTree i j (relSegsM p q) (.leaf none)
  | _, _, _, _, _ => .leaf none

/-- **How a read `Q` stands to a write `P`** (`Path.strip?`, symbolic): by
the recursor on `P`, `casesOn` on `Q` with its type generalised and its
equation passed in (Gate G0). -/
@[implemented_by relSegsM]
def relSegs {S T : Ty} (p : TSegs C S T) : {U : Ty} → TSegs C S U →
    CTree C (Option (TSegs C T U)) :=
  @TSegs.rec C (fun S T _ => {U : Ty} → TSegs C S U → CTree C (Option (TSegs C T U)))
    (fun q => .leaf (some q))
    (fun {s} {f} {_} {T} h _ ih {U} q =>
      @TSegs.casesOn C (fun S' U' _ => S' = .ref (.struct s) → CTree C (Option (TSegs C T U')))
        _ U q
        (fun _ => .leaf none)
        (fun {_} {f'} {_} {_} h' rest e =>
          if ef : f = f' then ih (field_ty_eq h h' e ef ▸ rest) else .leaf none)
        (fun _ _ _ => .leaf none) (fun _ _ _ => .leaf none) (fun _ _ _ => .leaf none) rfl)
    (fun {E} {T} i _ ih {U} q =>
      @TSegs.casesOn C (fun S' U' _ => S' = .ref (.array E) → CTree C (Option (TSegs C T U')))
        _ U q
        (fun _ => .leaf none) (fun _ _ _ => .leaf none)
        (fun {_} {_} j rest e => keyTree i j (ih (array_inj e ▸ rest)) (.leaf none))
        (fun _ _ _ => .leaf none) (fun _ _ _ => .leaf none) rfl)
    (fun {E} {T} {n} i _ ih {U} q =>
      @TSegs.casesOn C (fun S' U' _ => S' = .ref (.fixed E n) → CTree C (Option (TSegs C T U')))
        _ U q
        (fun _ => .leaf none) (fun _ _ _ => .leaf none) (fun _ _ _ => .leaf none)
        (fun {_} {_} {_} j rest e => keyTree i j (ih (fixed_inj e ▸ rest)) (.leaf none))
        (fun _ _ _ => .leaf none) rfl)
    (fun {k} {V} {T} i _ ih {U} q =>
      @TSegs.casesOn C
        (fun S' U' _ => S' = .ref (.mapping k V) → CTree C (Option (TSegs C T U')))
        _ U q
        (fun _ => .leaf none) (fun _ _ _ => .leaf none) (fun _ _ _ => .leaf none)
        (fun _ _ _ => .leaf none)
        (fun {_} {_} {_} j rest e =>
          keyTree i ((mapping_inj e).1 ▸ j) (ih ((mapping_inj e).2 ▸ rest)) (.leaf none))
        rfl)
    S T p

theorem relSegs_eq_relSegsM {S T : Ty} (p : TSegs C S T) {U : Ty} (q : TSegs C S U) :
    relSegs p q = relSegsM p q := by
  induction p generalizing U with
  | nil => rfl
  | field h p ih => cases q <;> (first | rfl | (simp only [relSegsM, ← ih]; rfl))
  | «at» i p ih | atF i p ih | key i p ih => cases q <;> (first | rfl | (simp only [relSegsM, ← ih]; rfl))

theorem root_inj {r r' : Name} {R R' : Ty} (h : r = r') (hr : C.rootType r = some R)
    (hr' : C.rootType r' = some R') : R' = R := by
  subst h; exact Option.some.inj (hr'.symm.trans hr)

/-! ## Readers

A value is read by its three observations (`CK`): the word at a primitive
location, the live length of an array, whether a location is there; each a
term of the reduction (`CK.out`).  A reader at a type (`VRd`) reads them at
segments below it, a storage reader (`SRd`) at symbolic paths. -/

/-- The observation a read asks for, at the type of the location. -/
inductive CK : Ty → Type where
  | word (P : PrimTy) : CK (.prim P)
  | len (E : Ty) : CK (.ref (.array E))
  | has (V : Ty) : CK V

/-- The type of what an observation reads. -/
def CK.out {V : Ty} (c : CK V) : PrimTy :=
  @CK.casesOn (fun _ _ => PrimTy) V c (fun P => P) (fun _ => .uint) (fun _ => .bool)

/-- A reader below a value of type `T`. -/
abbrev VRd (C : Contract) (T : Ty) := {V : Ty} → (c : CK V) → TSegs C T V → LTm C (.val c.out)

/-- A reader of a storage. -/
abbrev SRd (C : Contract) := {V : Ty} → (c : CK V) → SPath C V → LTm C (.val c.out)

/-- The reader below `s`. -/
def VRd.find {T U : Ty} (x : VRd C T) (s : TSegs C T U) : VRd C U := fun c r => x c (s.append r)

/-- The storage reader at `P`. -/
def SRd.at {T : Ty} (S : SRd C) (P : SPath C T) : VRd C T := fun c r => S c (P.snoc r)

/-- `a < b` on `uint`s, two literals compared. -/
def LTm.lt (a b : LTm C (.val .uint)) : LTm C (.val .bool) :=
  match a.keyView, b.keyView with
  | .lit x, .lit y => .lit (p := .bool) (decide (x < y))
  | _, _ => .app2 (.binop .lt rfl) a b

/-- `a < n` for a size `n` (every `uint` is below a size past the bound). -/
def LTm.ltNat (a : LTm C (.val .uint)) (n : Nat) : LTm C (.val .bool) :=
  if n < 2 ^ 256 then .lt a (.nat n) else .tt

/-- `a + 1` on `uint`s. -/
def LTm.succ (a : LTm C (.val .uint)) : LTm C (.val .uint) := .app2 (.binop .add rfl) a (.nat 1)

/-- `a - 1` on `uint`s. -/
def LTm.pred (a : LTm C (.val .uint)) : LTm C (.val .uint) := .app2 (.binop .sub rfl) a (.nat 1)

/-- The term is the literal `true`, at any primitive type. -/
def LTm.isTrue {p : PrimTy} (t : LTm C (.val p)) : Bool :=
  match p, t with
  | .bool, t => t.isTT
  | _, _ => false

/-- `a + 1` on `uint`s, a literal added where it is one. -/
def LTm.succK (a : LTm C (.val .uint)) : LTm C (.val .uint) :=
  match a.keyView with
  | .lit n => if 0 ≤ n ∧ n + 1 < 2 ^ 256 then .nat (n + 1).toNat else .succ a
  | _ => .succ a

/-- `a - 1` on `uint`s, a literal subtracted where it is one. -/
def LTm.predK (a : LTm C (.val .uint)) : LTm C (.val .uint) :=
  match a.keyView with
  | .lit n => if 1 ≤ n ∧ n < 2 ^ 256 then .nat (n - 1).toNat else .pred a
  | _ => .pred a

/-- `kite a b t e`, settled where the terms compare (`keyCmp`). -/
def LTm.kiteK {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (t e : LTm C s) : LTm C s :=
  match keyCmp a b with
  | some true => t
  | some false => e
  | none => .kite a b t e

/-- `c ? a : b`. -/
def LTm.cond {p : PrimTy} (c : LTm C (.val .bool)) (a b : LTm C (.val p)) : LTm C (.val p) :=
  if c.isTT then a
  else if c.isFF then b
  else if a.beqR b then seqL c a
  else if a.beqR c && b.isTrue then seqL c b
  else .app3 .ite c a b

/-- What nothing shows: the default word, length `0`, not there. -/
def CK.absent {V : Ty} (c : CK V) : LTm C (.val c.out) :=
  @CK.casesOn (fun V c => LTm C (.val c.out)) V c (fun P => .lit (PrimTy.dflt P))
    (fun _ => .nat 0) (fun _ => .lit (p := .bool) false)

/-- What a location deleted shows (`Comp.reset`): the default word, length
`0`, there where it was (`has`). -/
def CK.reset {V : Ty} (c : CK V) (has : LTm C (.val .bool)) : LTm C (.val c.out) :=
  @CK.casesOn (fun V c => LTm C (.val c.out)) V c (fun P => .lit (PrimTy.dflt P))
    (fun _ => .nat 0) (fun _ => has)

/-- At an array with a new length: the length `len'`, there where it was. -/
def CK.setLen {V : Ty} (c : CK V) (len' : LTm C (.val .uint)) (has : LTm C (.val .bool)) :
    LTm C (.val c.out) :=
  @CK.casesOn (fun V c => LTm C (.val c.out)) V c (fun P => .lit (PrimTy.dflt P))
    (fun _ => len') (fun _ => has)

/-! ### The operations, read below the location they act on -/

/-- `delRS` by `match`, its compiled form. -/
def delRSM {U V : Ty} (x : VRd C U) (r : TSegs C U V) (c : CK V) : LTm C (.val c.out) :=
  match U, V, r with
  | _, _, .nil => c.reset (x (.has _) .nil)
  | _, _, .field h r => delRSM (x.find (.field h .nil)) r c
  | _, _, .at i r => .cond (.lt i (x (.len _) .nil)) (delRSM (x.find (.at i .nil)) r c) (x c (.at i r))
  | _, _, .atF i r => delRSM (x.find (.atF i .nil)) r c
  | _, _, .key i r => x c (.key i r)

/-- **A delete, read** (`TVal.delR`): reset below the location, a mapping's
entries and an array's slots past its live end kept. -/
@[implemented_by delRSM]
def delRS {U V : Ty} (x : VRd C U) (r : TSegs C U V) (c : CK V) : LTm C (.val c.out) :=
  @TSegs.rec C (fun U V _ => VRd C U → (c : CK V) → LTm C (.val c.out))
    (fun x c => c.reset (x (.has _) .nil))
    (fun h _ ih x c => ih (x.find (.field h .nil)) c)
    (fun i r ih x c => .cond (.lt i (x (.len _) .nil)) (ih (x.find (.at i .nil)) c) (x c (.at i r)))
    (fun i _ ih x c => ih (x.find (.atF i .nil)) c)
    (fun i r _ x c => x c (.key i r))
    U V r x c

theorem delRS_eq_delRSM {U V : Ty} (x : VRd C U) (r : TSegs C U V) (c : CK V) :
    delRS x r c = delRSM x r c := by
  induction r with
  | nil | key => rfl
  | field h r ih | «at» i r ih | atF i r ih => simp only [delRSM, ← ih]; rfl

/-- `stripRS` by `match`, its compiled form. -/
def stripRSM {U V : Ty} (x : VRd C U) (r : TSegs C U V) (c : CK V) : LTm C (.val c.out) :=
  match U, V, r with
  | _, _, .nil => x c .nil
  | _, _, .field h r => stripRSM (x.find (.field h .nil)) r c
  | _, _, .at i r => .cond (.lt i (x (.len _) .nil)) (stripRSM (x.find (.at i .nil)) r c) c.absent
  | _, _, .atF i r => stripRSM (x.find (.atF i .nil)) r c
  | _, _, .key i r => x c (.key i r)

/-- **A value as written to fresh slots, read** (`TVal.stripR`): nothing
past an array's live end. -/
@[implemented_by stripRSM]
def stripRS {U V : Ty} (x : VRd C U) (r : TSegs C U V) (c : CK V) : LTm C (.val c.out) :=
  @TSegs.rec C (fun U V _ => VRd C U → (c : CK V) → LTm C (.val c.out))
    (fun x c => x c .nil)
    (fun h _ ih x c => ih (x.find (.field h .nil)) c)
    (fun i _ ih x c => .cond (.lt i (x (.len _) .nil)) (ih (x.find (.at i .nil)) c) c.absent)
    (fun i _ ih x c => ih (x.find (.atF i .nil)) c)
    (fun i r _ x c => x c (.key i r))
    U V r x c

theorem stripRS_eq_stripRSM {U V : Ty} (x : VRd C U) (r : TSegs C U V) (c : CK V) :
    stripRS x r c = stripRSM x r c := by
  induction r with
  | nil | key => rfl
  | field h r ih | «at» i r ih | atF i r ih => simp only [stripRSM, ← ih]; rfl

/-- `ovRS` by `match`, its compiled form. -/
def ovRSM {U V : Ty} (o n : VRd C U) (r : TSegs C U V) (c : CK V) : LTm C (.val c.out) :=
  match U, V, r with
  | _, _, .nil => n c .nil
  | _, _, .field h r => ovRSM (o.find (.field h .nil)) (n.find (.field h .nil)) r c
  | _, _, .at i r =>
    .cond (n (.has _) .nil)
      (.cond (.lt i (n (.len _) .nil))
        (ovRSM (o.find (.at i .nil)) (n.find (.at i .nil)) r c)
        (.cond (.lt i (o (.len _) .nil)) (delRSM (o.find (.at i .nil)) r c) (o c (.at i r))))
      c.absent
  | _, _, .atF i r => ovRSM (o.find (.atF i .nil)) (n.find (.atF i .nil)) r c
  | _, _, .key i r =>
    .cond (n (.has _) .nil) (.cond (o (.has _) .nil) (o c (.key i r)) (n c (.key i r))) c.absent

/-- **A copy of `n` laid over `o`, read** (`TVal.ovR`): member by member,
element by element over the old slots, the old elements past the new
length deleted, a mapping kept. -/
@[implemented_by ovRSM]
def ovRS {U V : Ty} (o n : VRd C U) (r : TSegs C U V) (c : CK V) : LTm C (.val c.out) :=
  @TSegs.rec C (fun U V _ => VRd C U → VRd C U → (c : CK V) → LTm C (.val c.out))
    (fun _ n c => n c .nil)
    (fun h _ ih o n c => ih (o.find (.field h .nil)) (n.find (.field h .nil)) c)
    (fun i r ih o n c =>
      .cond (n (.has _) .nil)
        (.cond (.lt i (n (.len _) .nil))
          (ih (o.find (.at i .nil)) (n.find (.at i .nil)) c)
          (.cond (.lt i (o (.len _) .nil)) (delRS (o.find (.at i .nil)) r c) (o c (.at i r))))
        c.absent)
    (fun i _ ih o n c => ih (o.find (.atF i .nil)) (n.find (.atF i .nil)) c)
    (fun i r _ o n c =>
      .cond (n (.has _) .nil) (.cond (o (.has _) .nil) (o c (.key i r)) (n c (.key i r))) c.absent)
    U V r o n c

theorem ovRS_eq_ovRSM {U V : Ty} (o n : VRd C U) (r : TSegs C U V) (c : CK V) :
    ovRS o n r c = ovRSM o n r c := by
  induction r with
  | nil | key => rfl
  | field h r ih | atF i r ih => simp only [ovRSM, ← ih]; rfl
  | «at» i r ih => simp only [ovRSM, ← ih, ← delRS_eq_delRSM]; rfl

/-- `arrRd` by `match`, its compiled form. -/
def arrRdM {E : Ty} (len' : LTm C (.val .uint)) (has : LTm C (.val .bool))
    (below : LTm C (.val .uint) → VRd C E) : VRd C (.ref (.array E)) :=
  fun {V} c r => match V, r with
    | _, .nil => c.setLen len' has
    | _, .at i r => below i c r

/-- **A reader at an array**: at the array itself, its length `len'` and
`has`; below an index `i`, `below i`. -/
@[implemented_by arrRdM]
def arrRd {E : Ty} (len' : LTm C (.val .uint)) (has : LTm C (.val .bool))
    (below : LTm C (.val .uint) → VRd C E) : VRd C (.ref (.array E)) :=
  fun {V} c r =>
    @TSegs.casesOn C (fun T V _ => T = .ref (.array E) → (c : CK V) → LTm C (.val c.out))
      _ V r
      (fun _ c => c.setLen len' has)
      (fun _ _ _ _ => .err)
      (fun {_} {_} i rest e c => below i c (array_inj e ▸ rest))
      (fun _ _ _ _ => .err) (fun _ _ _ _ => .err) rfl c

theorem arrRd_eq_arrRdM {E : Ty} (len' : LTm C (.val .uint)) (has : LTm C (.val .bool))
    (below : LTm C (.val .uint) → VRd C E) {V : Ty} (c : CK V) (r : TSegs C (.ref (.array E)) V) :
    arrRd len' has below c r = arrRdM len' has below c r := by
  cases r <;> rfl

/-- **A push of `x`, read** (`TVal.pushA`): the length one more, `x` at the
old length `L`, the old elements elsewhere. -/
def pushRd {E : Ty} (a : VRd C (.ref (.array E))) (x : VRd C E) (L : LTm C (.val .uint)) :
    VRd C (.ref (.array E)) :=
  arrRd (.succK L) (a (.has _) .nil) fun i {_} c r => .kiteK i L (x c r) (a c (.at i r))

/-- An array with its length set to `L'`, its slots as they are
(`TVal.setLen`). -/
def setLenRd {E : Ty} (a : VRd C (.ref (.array E))) (L' : LTm C (.val .uint)) :
    VRd C (.ref (.array E)) :=
  arrRd L' (a (.has _) .nil) fun i {_} c r => a c (.at i r)

/-- `TSegs.dfltHas` by `match`, its compiled form. -/
def dfltHasM {U V : Ty} : TSegs C U V → LTm C (.val .bool)
  | .nil => .tt
  | .field _ r => dfltHasM r
  | .at _ _ => .lit (p := .bool) false
  | .atF (n := n) i r => .cond (.ltNat i n) (dfltHasM r) (.lit (p := .bool) false)
  | .key _ r => dfltHasM r

/-- Whether a default value has a location below it: not below a dynamic
array's index (it is empty), below a fixed one's where in range. -/
@[implemented_by dfltHasM]
def dfltHas {U V : Ty} (r : TSegs C U V) : LTm C (.val .bool) :=
  @TSegs.rec C (fun _ _ _ => LTm C (.val .bool)) .tt (fun _ _ ih => ih)
    (fun _ _ _ => .lit (p := .bool) false)
    (fun {_} {_} {n} i _ ih => .cond (.ltNat i n) ih (.lit (p := .bool) false))
    (fun _ _ ih => ih) U V r

theorem dfltHas_eq_dfltHasM {U V : Ty} (r : TSegs C U V) : dfltHas r = dfltHasM r := by
  induction r with
  | nil | «at» => rfl
  | field h r ih | key i r ih | atF i r ih => simp only [dfltHasM, ← ih]; rfl

/-- **A default value, read** (`(SVal.dflt E).obs`): the default word,
length `0`, there as `dfltHas` says. -/
def dfltRd (E : Ty) : VRd C E := fun c r => c.reset (dfltHas r)

/-- Fresh allocation read lazily: the written size, initialized defaults in
range, and typed absence past the end. This folds `memoryArrayFreshAlloc`,
`readOnWrite`, `readOnAddM` and the memory initialization rules. -/
def newArrArrayRd (E : Ty) (n : LTm C (.val .uint)) : VRd C (.ref (.array E)) :=
  arrRd n .tt fun i {_} c r => .cond (.lt i n) (dfltRd E c r) c.absent

def newArrRd : (R : RefTy) → R.newArrOk = true → LTm C (.val .uint) → VRd C (.ref R)
  | .array E, _, n => newArrArrayRd E n
  | .struct _, h, _ | .fixed .., h, _ | .mapping .., h, _ => nomatch h

/-- A converted fixed-array element: copied below the source length,
default padding within the target, absent past its end. -/
def fixedCopyChildRd {E : Ty} {n : Nat} {R : RefTy} (shape : FixedCopy E n R)
    (a : VRd C (.ref (.fixed E n))) (i : LTm C (.val .uint)) : VRd C E := fun c r =>
  .cond (.ltNat i shape.targetLength)
    (.cond (.ltNat i n) (stripRS (a.find (.atF i .nil)) r c)
      (stripRS (dfltRd E) r c)) c.absent

/-- The lazy selector clauses of a typed fixed-array copy source. -/
def fixedArrRd {E : Ty} (n : Nat) (has : LTm C (.val .bool))
    (below : LTm C (.val .uint) → VRd C E) : VRd C (.ref (.fixed E n)) :=
  fun {V} c r => match V, r with
    | _, .nil => c.reset has
    | _, .atF i r => below i c r

/-- The lazy selector clauses of a typed fixed-array copy source. -/
def fixedCopyRd {E : Ty} {n : Nat} : {R : RefTy} → FixedCopy E n R →
    VRd C (.ref (.fixed E n)) → VRd C (.ref R)
  | _, .dynamic hb, a => arrRd (.nat n) .tt (fixedCopyChildRd (.dynamic hb) a)
  | _, .fixed m hm, a => fixedArrRd m .tt (fixedCopyChildRd (.fixed m hm) a)

/-- **One more live element, read** (`TVal.extendA`): a word's slot reset,
a missing slot at its default, a slot past the end as it is. -/
def extendRd {E : Ty} (a : VRd C (.ref (.array E))) (L : LTm C (.val .uint)) :
    VRd C (.ref (.array E)) :=
  if E.isPrimitive then pushRd a (dfltRd E) L
  else fun c r =>
    .cond (a (.has _) (.at L .nil)) (setLenRd a (.succK L) c r) (pushRd a (dfltRd E) L c r)

/-- **A pop, read** (`TVal.popA`, the array not empty): the length one
less, the last element deleted unless `keep`. -/
def popRd (keep : Bool) {E : Ty} (a : VRd C (.ref (.array E))) (L : LTm C (.val .uint)) :
    VRd C (.ref (.array E)) :=
  if keep then setLenRd a (.predK L)
  else arrRd (.predK L) (a (.has _) .nil) fun i {_} c r =>
    .kiteK i (.predK L) (delRS (a.find (.at (.predK L) .nil)) r c) (a c (.at i r))

/-- `svalRd` by `match`, its compiled form. -/
def svalRdM {p : PrimTy} (w : LTm C (.val p)) : VRd C (.prim p) :=
  fun {V} c r => match V, r, c with
    | _, .nil, .word _ => w
    | _, .nil, .has _ => .tt

/-- **A word as a stored value, read**: the word at it, there. -/
@[implemented_by svalRdM]
def svalRd {p : PrimTy} (w : LTm C (.val p)) : VRd C (.prim p) :=
  fun {V} c r =>
    @TSegs.casesOn C (fun T V _ => T = .prim p → (c : CK V) → LTm C (.val c.out)) _ V r
      (fun {T} e c => @CK.casesOn (fun V c => V = T → LTm C (.val c.out)) _ c
        (fun P e' => (show P = p by injection e'.trans e) ▸ w)
        (fun _ _ => .err) (fun _ _ => .tt) rfl)
      (fun _ _ _ _ => .err) (fun _ _ _ _ => .err) (fun _ _ _ _ => .err) (fun _ _ _ _ => .err) rfl c

theorem svalRd_eq_svalRdM {p : PrimTy} (w : LTm C (.val p)) {V : Ty} (c : CK V)
    (r : TSegs C (.prim p) V) : svalRd w c r = svalRdM w c r := by
  cases r <;> cases c <;> rfl

/-! ## A memory object as a stored value (`copyMem`) -/

/-- Where a reader of a memory object stands: an address at a word, the
identity of an object at a reference. -/
def MLoc (C : Contract) : Ty → Type
  | .prim P => LTm C (.addr (.prim P))
  | .ref R => LTm C (.ident R)

/-- The location at an address: the address at a word, the identity read
there at a reference. -/
def MLoc.ofAddr (M : LTm C .mem) : (T : Ty) → LTm C (.addr T) → MLoc C T
  | .prim _, a => a
  | .ref _, a => (.app2 .iread M a : LTm C (.ident _))

/-- At the end of the segments: the word read, the array's length, whether
every index on the way was within its array (`h`). -/
def memRdNil (M : LTm C .mem) {V : Ty} (loc : MLoc C V) (h : LTm C (.val .bool)) (c : CK V) :
    LTm C (.val c.out) :=
  @CK.casesOn (fun V c => MLoc C V → LTm C (.val c.out)) V c
    (fun P loc => .kite h .tt (.app2 .read M (loc : LTm C (.addr (.prim P))))
      (.lit (PrimTy.dflt P)))
    (fun E loc => .kite h .tt (.app2 .mlen M (loc : LTm C (.ident (.array E)))) (.nat 0))
    (fun _ _ => h) loc

/-- `memRd` by `match`, its compiled form. -/
def memRdM (M : LTm C .mem) : {T V : Ty} → TSegs C T V → MLoc C T → LTm C (.val .bool) →
    (c : CK V) → LTm C (.val c.out)
  | _, _, .nil, loc, h, c => memRdNil M loc h c
  | _, _, .field (T := T) hf rest, loc, h, c =>
    memRdM M rest (MLoc.ofAddr M T (.app1 (.mfield hf) (loc : LTm C (.ident (.struct _))))) h c
  | _, _, .at (E := E) i rest, loc, h, c =>
    memRdM M rest (MLoc.ofAddr M E (.app2 (.mat .dyn) (loc : LTm C (.ident (.array E))) i))
      (.kite h .tt (.lt i (.app2 .mlen M (loc : LTm C (.ident (.array E))))) (.lit false)) c
  | _, _, .atF (E := E) (n := n) i rest, loc, h, c =>
    memRdM M rest (MLoc.ofAddr M E (.app2 (.mat .fixed) (loc : LTm C (.ident (.fixed E n))) i))
      (.kite h .tt (LTm.ltNat i n) (.lit false)) c
  | _, _, .key (V := V) _ rest, _, h, c => memRdM M rest (MLoc.ofAddr M V .err) h c

/-- **A memory object read as the stored value it copies to**
(`selectOnCopyMem`): down the segments from `loc` in the memory `M`, a
member's address, an element's within its array's length, an object's
identity read there; at the end the word, the length, whether every index
was within. -/
@[implemented_by memRdM]
def memRd (M : LTm C .mem) {T V : Ty} (r : TSegs C T V) : MLoc C T → LTm C (.val .bool) →
    (c : CK V) → LTm C (.val c.out) :=
  @TSegs.rec C (fun T V _ => MLoc C T → LTm C (.val .bool) → (c : CK V) → LTm C (.val c.out))
    (fun loc h c => memRdNil M loc h c)
    (fun {_} {_} {T} {_} hf _ ih loc h c =>
      ih (MLoc.ofAddr M T (.app1 (.mfield hf) (loc : LTm C (.ident (.struct _))))) h c)
    (fun {E} {_} i _ ih loc h c =>
      ih (MLoc.ofAddr M E (.app2 (.mat .dyn) (loc : LTm C (.ident (.array E))) i))
        (.kite h .tt (.lt i (.app2 .mlen M (loc : LTm C (.ident (.array E))))) (.lit false)) c)
    (fun {E} {_} {n} i _ ih loc h c =>
      ih (MLoc.ofAddr M E (.app2 (.mat .fixed) (loc : LTm C (.ident (.fixed E n))) i))
        (.kite h .tt (LTm.ltNat i n) (.lit false)) c)
    (fun {_} {V} {_} _ _ ih _ h c => ih (MLoc.ofAddr M V .err) h c) T V r

theorem memRd_eq_memRdM (M : LTm C .mem) {T V : Ty} (r : TSegs C T V) :
    memRd M r = memRdM M r := by
  funext loc h c
  induction r generalizing h with
  | nil => rfl
  | field hf r ih | «at» i r ih | atF i r ih | key i r ih => simp only [memRdM, ← ih]; rfl

/-- The reader of `copyMem(M, t)`. -/
def copyMemRd {R : RefTy} (M : LTm C .mem) (t : LTm C (.ident R)) : VRd C (.ref R) :=
  fun c r => memRd M r (t : MLoc C (.ref R)) .tt c

/-! ## Storages, eliminated

A storage term is eliminated to what makes it return (`ok`) and its
reader; the original term is kept for what has no reading. -/

/-- A storage, eliminated: its guard, its reader, the term itself. -/
structure SFun (C : Contract) where
  ok : LTm C (.val .bool)
  rd : SRd C
  orig : LTm C .st

/-- A fixed-size array's index, a literal below its size `n`. -/
def TSegs.litBelow (i : LTm C (.val .uint)) (n : Nat) : Bool :=
  match i.litV? with
  | some v => decide ((v : PrimTy.uint.Denote).1.toNat < n)
  | none => false

/-! ### Where a typed storage has a location

A typed storage has its contract's shape (solkey's `wf*` and
`selectOnShape*` taclets, subsumed by `Storage C`): below a location, a
member, a mapping's key and a fixed-size array's index in range are always
there. -/

/-- A location one path further has a location where its base has one, when
every value has the path: a struct its members, a mapping its keys. -/
theorem has_append (st : Storage C) {U W : Ty} (r : SRef C U) (p : Path U W)
    (hp : ∀ v : SVal U, (v.findM p).isSome = true) :
    st.obs.has (.ref (r.append p)) = st.obs.has (.ref r) := by
  rw [Storage.obs_has_ref, Storage.obs_has_ref, SVal.obs_has, SVal.obs_has]
  show ((st.get r.hroot).findM (r.path.append p)).isSome = _
  rw [SVal.findM_append]
  cases (st.get r.hroot).findM r.path with
  | none => rfl
  | some v => exact hp v

theorem has_root (st : Storage C) (r : Name) {T : Ty} (h : C.rootType r = some T) :
    st.obs.has (.ref (SRef.ofRoot r h)) = true := by
  rw [Storage.obs_has_ref, SVal.obs_has]
  show ((st.get h).findM .nil).isSome = true
  rw [SVal.findM_nil']; rfl

theorem findM_field {s f : Name} {T : Ty} (h : Semantics.lookupBy f (Semantics.structDef s) = some T)
    (v : SVal (.ref (.struct s))) : (v.findM (.field h .nil)).isSome = true := by
  cases v
  simp only [SVal.findM, SVal.findM_nil', Option.isSome_some]

theorem findM_key {K : PrimTy} {V : Ty} (k : K.Denote) (v : SVal (.ref (.mapping K V))) :
    (v.findM (.key k .nil)).isSome = true := by
  cases v
  simp only [SVal.findM]
  split <;> rfl

theorem findM_atF {E : Ty} {n : Nat} (k : PrimTy.uint.Denote)
    (hk : (k : PrimTy.uint.Denote).1.toNat < n) (v : SVal (.ref (.fixed E n))) :
    (v.findM (.atF k .nil)).isSome = true := by
  cases v with
  | fixed e =>
    show (match e.toList[(k : PrimTy.uint.Denote).1.toNat]? with
      | some x => x.findM .nil
      | none => none).isSome = true
    rw [List.getElem?_eq_getElem (by rw [SVec.length_toList]; exact hk)]
    show (SVal.findM _ .nil).isSome = true
    rw [SVal.findM_nil']; rfl

/-- `TSegs.hasFrom`'s compiled twin. -/
def TSegs.hasFromM : {S T : Ty} → TSegs C S T → LTm C (.path S) → LTm C (.val .bool) →
    LTm C (.val .bool)
  | _, _, .nil, _, acc => acc
  | _, _, .field h p, base, acc => p.hasFromM (.app1 (.field h) base) acc
  | _, _, .at i p, base, _ =>
    p.hasFromM (.index (.arr .dyn) base i) (.obsH (.index (.arr .dyn) base i))
  | _, _, @TSegs.atF _ _ _ n i p, base, acc =>
    p.hasFromM (.index (.arr .fixed) base i)
      (if TSegs.litBelow i n then acc else .obsH (.index (.arr .fixed) base i))
  | _, _, .key i p, base, acc => p.hasFromM (.index .map base i) acc

/-- **`has` at the segments `p` below `base`** on a typed storage, `acc`
`has` at `base`: past the last segment a location need not be below (a
dynamic index, a fixed one not known in range), `has` there; past the
others (a member, a key, a fixed index in range), `acc` unchanged.  By the
recursor. -/
@[implemented_by TSegs.hasFromM]
def TSegs.hasFrom {S T : Ty} (p : TSegs C S T) :
    LTm C (.path S) → LTm C (.val .bool) → LTm C (.val .bool) :=
  @TSegs.rec C (fun S _ _ => LTm C (.path S) → LTm C (.val .bool) → LTm C (.val .bool))
    (fun _ acc => acc)
    (fun h _ ih base acc => ih (.app1 (.field h) base) acc)
    (fun i _ ih base _ => ih (.index (.arr .dyn) base i) (.obsH (.index (.arr .dyn) base i)))
    (@fun _ _ n i _ ih base acc => ih (.index (.arr .fixed) base i)
      (if TSegs.litBelow i n then acc else .obsH (.index (.arr .fixed) base i)))
    (fun i _ ih base acc => ih (.index .map base i) acc) S T p

theorem TSegs.hasFrom_eq_hasFromM {S T : Ty} (p : TSegs C S T) : p.hasFrom = p.hasFromM := by
  funext base acc
  induction p generalizing acc with
  | nil => rfl
  | field h p ih | «at» i p ih | atF i p ih | key i p ih =>
    simp only [TSegs.hasFromM, ← ih]; rfl

/-- The starting storage's observation `c` at a path; `has` read from the
last segment a location need not be below (`TSegs.hasFrom`). -/
def initRd : SRd C := fun {V} c P =>
  @CK.casesOn (fun V c => LTm C (.path V) → LTm C (.val c.out)) V c
    (fun _ q => .obsW q) (fun _ q => .obsL q)
    (fun _ _ => P.segs.hasFrom (.app0 (.root P.r P.hr)) .tt) P.toLTm

/-- The starting storage. -/
def SFun.init : SFun C := ⟨.tt, initRd, .app0 .storage⟩

/-- A reader of a storage term read as it is (`find`, `len`, `sfind` on
it), the absent case defaulted. -/
def fbRd (s : LTm C .st) : SRd C := fun {V} c P =>
  @CK.casesOn (fun V c => LTm C (.path V) → LTm C (.val c.out)) V c
    (fun P q => .orElse (.app2 .find s q) (.lit (PrimTy.dflt P)))
    (fun _ q => .orElse (.app2 .len s q) (.nat 0))
    (fun _ q => .orElse (.seq (.app2 .sfind s q) .tt) (.lit (p := .bool) false)) P.toLTm

/-- A storage term with no reading of its own: read as it is. -/
def SFun.ofOrig (s : LTm C .st) : SFun C := ⟨seqL s .tt, fbRd s, s⟩

/-- `writeAt` by `match`, its compiled form. -/
def writeAtM {T : Ty} (S : SRd C) (P : SPath C T) (newR : VRd C T) : SRd C := fun c Q =>
  if h : P.r = Q.r then
    (relSegsM P.segs (root_inj h P.hr Q.hr ▸ Q.segs)).toTerm fun
      | some rest => newR c rest
      | none => S c Q
  else S c Q

/-- **A storage with a new value at `P`, read** (`Obs.save`): at or below
`P` the new value's reading of the rest, the old reading elsewhere. -/
@[implemented_by writeAtM]
def writeAt {T : Ty} (S : SRd C) (P : SPath C T) (newR : VRd C T) : SRd C := fun c Q =>
  if h : P.r = Q.r then
    (relSegs P.segs (root_inj h P.hr Q.hr ▸ Q.segs)).toTerm fun
      | some rest => newR c rest
      | none => S c Q
  else S c Q

theorem writeAt_eq_writeAtM {T : Ty} (S : SRd C) (P : SPath C T) (newR : VRd C T)
    {V : Ty} (c : CK V) (Q : SPath C V) : writeAt S P newR c Q = writeAtM S P newR c Q := by
  simp only [writeAt, writeAtM, relSegs_eq_relSegsM]

/-- The largest length a push leaves: `2^256 - 1`. -/
def maxLen : LTm C (.val .uint) := .nat (2 ^ 256 - 1)

namespace SFun

/-- `save(s, P, v)`: a value laid over what is at `P` (a word replaces it). -/
def save {T : Ty} (S : SFun C) (Pg : LTm C (.val .bool)) (P : SPath C T) (Vok : LTm C (.val .bool))
    (V : VRd C T) (orig : LTm C .st) : SFun C :=
  ⟨seqL S.ok (seqL Pg (seqL Vok (LTm.assert (S.rd (.has _) P)))),
    writeAt S.rd P fun c r => ovRS (SRd.at S.rd P) V r c, orig⟩

/-- `delAt(s, P)`. -/
def delAt {T : Ty} (S : SFun C) (Pg : LTm C (.val .bool)) (P : SPath C T) (orig : LTm C .st) :
    SFun C :=
  ⟨seqL S.ok (seqL Pg (LTm.assert (S.rd (.has _) P))),
    writeAt S.rd P fun c r => delRS (SRd.at S.rd P) r c, orig⟩

/-- `push(s, P, v)`: the stored value stripped, appended. -/
def push {E : Ty} (S : SFun C) (Pg : LTm C (.val .bool)) (P : SPath C (.ref (.array E)))
    (Vok : LTm C (.val .bool)) (V : VRd C E) (orig : LTm C .st) : SFun C :=
  let L := S.rd (.len _) P
  ⟨seqL S.ok (seqL Pg (seqL Vok (seqL (LTm.assert (S.rd (.has _) P)) (LTm.assert (.lt L maxLen))))),
    writeAt S.rd P (pushRd (SRd.at S.rd P) (fun c r => stripRS V r c) L), orig⟩

/-- `extend(s, P)`, `pushSlot(s, P)`: one more live element, its slot as it is. -/
def extend {E : Ty} (S : SFun C) (Pg : LTm C (.val .bool)) (P : SPath C (.ref (.array E)))
    (orig : LTm C .st) : SFun C :=
  let L := S.rd (.len _) P
  ⟨seqL S.ok (seqL Pg (seqL (LTm.assert (S.rd (.has _) P)) (LTm.assert (.lt L maxLen)))),
    writeAt S.rd P (extendRd (SRd.at S.rd P) L), orig⟩

/-- `pop(s, P)` (`keep` false), `shrink(s, P)` (`keep` true). -/
def pop (keep : Bool) {E : Ty} (S : SFun C) (Pg : LTm C (.val .bool))
    (P : SPath C (.ref (.array E))) (orig : LTm C .st) : SFun C :=
  let L := S.rd (.len _) P
  ⟨seqL S.ok (seqL Pg (seqL (LTm.assert (S.rd (.has _) P)) (LTm.assert (.lt (.nat 0) L)))),
    writeAt S.rd P (popRd keep (SRd.at S.rd P) L), orig⟩

end SFun

/-! ## The elimination -/

/-- What a term of each sort is eliminated to: a storage its guard and
reader (`SFun`), a path its guard and symbolic path, a stored value its
guard and reader, `none` where there is none; a term of any other sort a
term. -/
def ElimM (C : Contract) : Srt → Type
  | .st => SFun C
  | .path T => Option (LTm C (.val .bool) × SPath C T)
  | .sv T => Option (LTm C (.val .bool) × VRd C T)
  | .val p => LTm C (.val p)
  | .ident R => LTm C (.ident R)
  | .addr T => LTm C (.addr T)
  | .mem => LTm C .mem
  | .mv T => LTm C (.mv T)
  | .sts s => LTm C (.sts s)
  | .spath s T => LTm C (.spath s T)
  | .kint => LTm C .kint

namespace ElimM

/-- A term with no reading of its own: kept as it is. -/
def ofOrig : (s : Srt) → LTm C s → ElimM C s
  | .st, t => SFun.ofOrig t
  | .path _, _ => none
  | .sv _, _ => none
  | .val _, t => t
  | .ident _, t => t
  | .addr _, t => t
  | .mem, t => t
  | .mv _, t => t
  | .sts _, t => t
  | .spath _ _, t => t
  | .kint, t => t

/-- What returns exactly where the term does. -/
def guard : (s : Srt) → ElimM C s → LTm C s → LTm C (.val .bool)
  | .st, e, _ => SFun.ok e
  | .path _, e, t => match (e : Option (LTm C (.val .bool) × SPath C _)) with
    | some (g, _) => g
    | none => seqL t .tt
  | .sv _, e, t => match (e : Option (LTm C (.val .bool) × VRd C _)) with
    | some (g, _) => g
    | none => seqL t .tt
  | .val _, e, _ => seqL (e : LTm C (.val _)) .tt
  | .ident _, e, _ => seqL (e : LTm C (.ident _)) .tt
  | .addr _, e, _ => seqL (e : LTm C (.addr _)) .tt
  | .mem, e, _ => seqL (e : LTm C .mem) .tt
  | .mv _, e, _ => seqL (e : LTm C (.mv _)) .tt
  | .sts _, e, _ => seqL (e : LTm C (.sts _)) .tt
  | .spath _ _, e, _ => seqL (e : LTm C (.spath _ _)) .tt
  | .kint, e, _ => seqL (e : LTm C .kint) .tt

/-- An eliminated term guarded by `g` (`seq g t`); `orig` is `seq d t`. -/
def guarded : (s : Srt) → LTm C (.val .bool) → ElimM C s → LTm C s → ElimM C s
  | .st, g, e, o => (⟨seqL g (SFun.ok e), SFun.rd e, o⟩ : SFun C)
  | .path _, g, e, _ => (e : Option (LTm C (.val .bool) × SPath C _)).map fun x => (seqL g x.1, x.2)
  | .sv _, g, e, _ => (e : Option (LTm C (.val .bool) × VRd C _)).map fun x => (seqL g x.1, x.2)
  | .val _, g, e, _ => (seqL g (e : LTm C (.val _)) : LTm C (.val _))
  | .ident _, g, e, _ => (seqL g (e : LTm C (.ident _)) : LTm C (.ident _))
  | .addr _, g, e, _ => (seqL g (e : LTm C (.addr _)) : LTm C (.addr _))
  | .mem, g, e, _ => (seqL g (e : LTm C .mem) : LTm C .mem)
  | .mv _, g, e, _ => (seqL g (e : LTm C (.mv _)) : LTm C (.mv _))
  | .sts _, g, e, _ => (seqL g (e : LTm C (.sts _)) : LTm C (.sts _))
  | .spath _ _, g, e, _ => (seqL g (e : LTm C (.spath _ _)) : LTm C (.spath _ _))
  | .kint, g, e, _ => (seqL g (e : LTm C .kint) : LTm C .kint)

/-- `a`, or `b` where `a` halts: eliminated at a word, kept otherwise. -/
def orElse : (s : Srt) → ElimM C s → ElimM C s → LTm C s → ElimM C s
  | .val _, a, b, _ => (.orElse (a : LTm C (.val _)) b : LTm C (.val _))
  | s, _, _, o => ofOrig s o

/-- A key test: eliminated at a word, kept otherwise. -/
def kite {p : PrimTy} (a b : LTm C (.val p)) : (s : Srt) → ElimM C s → ElimM C s → LTm C s →
    ElimM C s
  | .val _, t, e, _ => (.kite a b (t : LTm C (.val _)) e : LTm C (.val _))
  | s, _, _, o => ofOrig s o

end ElimM

/-- A path one index further, the index read as a key. -/
def pathIdx {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (q : Option (LTm C (.val .bool) × SPath C (.ref R))) (i : LTm C (.val k)) :
    Option (LTm C (.val .bool) × SPath C V) :=
  q.map fun x => (seqL x.1 (seqL i .tt), x.2.snoc (TSegs.ofIndex it i))

/-- `checkIndex`'s bound on an index `i` at `Q` in the storage read by `rd`:
every key of a mapping, an index below an array's length. -/
def boundG {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (rd : SRd C)
    (Q : SPath C (.ref R)) (i : LTm C (.val k)) : LTm C (.val .bool) :=
  @IndexTy.casesOn (fun R k V _ => SPath C (.ref R) → LTm C (.val k) → LTm C (.val .bool))
    R k V it (fun _ _ => .tt)
    (fun {_} {_} a => @ArrTy.casesOn
      (fun R E _ => SPath C (.ref R) → LTm C (.val .uint) → LTm C (.val .bool)) _ _ a
      (fun {_} Q i => LTm.assert (.lt i (rd (.len _) Q))) (fun {_} {n} _ i => LTm.assert (.ltNat i n))) Q i

/-- `q[i]` checked against the storage `S` (`atIn`, `at`). -/
def pathAtIn {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (S : SFun C)
    (q : Option (LTm C (.val .bool) × SPath C (.ref R))) (i : LTm C (.val k)) :
    Option (LTm C (.val .bool) × SPath C V) :=
  q.map fun x => (seqL S.ok (seqL x.1 (seqL i (seqL (LTm.assert (S.rd (.has _) x.2))
    (boundG it S.rd x.2 i)))), x.2.snoc (TSegs.ofIndex it i))

/-- `q[q.length]` in the storage `S` (`nextIn`, `next`). -/
def pathNext {E : Ty} (S : SFun C) (q : Option (LTm C (.val .bool) × SPath C (.ref (.array E)))) :
    Option (LTm C (.val .bool) × SPath C E) :=
  q.map fun x => (seqL S.ok (seqL x.1 (LTm.assert (S.rd (.has _) x.2))),
    x.2.snoc (.at (S.rd (.len _) x.2) .nil))

/-- A constant, eliminated. -/
def _root_.Solidity.Op0.elim {s : Srt} (o : Op0 C s) : ElimM C s :=
  @Op0.casesOn C (fun s _ => ElimM C s) s o
    (fun {p} v => (.app0 (.lit v) : LTm C (.val p)))
    (fun k => (.app0 (.env k) : LTm C (.val .uint)))
    (fun r {_} h => some (.tt, ⟨r, h, .nil⟩))
    SFun.init
    (.app0 .memory : LTm C .mem)
    (SFun.ofOrig (.app0 .mtSt))
    (fun s f {_} h => (.app0 (.member s f h) : LTm C (.spath _ _)))
    (fun n => (.app0 (.zlit n) : LTm C .kint))

/-- A unary symbol, eliminated: `x` the argument, `ex` its elimination. -/
def _root_.Solidity.Op1.elim {a s : Srt} (o : Op1 C a s) : LTm C a → ElimM C a → ElimM C s :=
  @Op1.casesOn C (fun a s _ => LTm C a → ElimM C a → ElimM C s) a s o
    (fun op {_} h _ ex => (.app1 (.unop op h) (ex : LTm C (.val _)) : LTm C (.val _)))
    (fun _ ex => (.app1 .net (ex : LTm C (.val .uint)) : LTm C .kint))
    (fun {_} _ ex => (.app1 .delValue (ex : LTm C (.val _)) : LTm C (.val _)))
    (fun {_} {_} {_} h _ ex => (ex : Option (LTm C (.val .bool) × SPath C _)).map fun x =>
      (x.1, x.2.snoc (.field h .nil)))
    (fun {_} _ ex => pathNext SFun.init ex)
    (fun {_} _ ex => some (seqL (ex : LTm C (.val _)) .tt, svalRd ex))
    (fun {R} h _ ex => some (seqL ex .tt, newArrRd R h ex))
    (fun R h x _ => (.app1 (.alloc R h) x : LTm C (.ident _)))
    (fun {_} {_} {_} h x _ => (.app1 (.mfield h) x : LTm C (.addr _)))
    (fun R h x _ => (.app1 (.addM R h) x : LTm C .mem))
    (fun {_} x _ => (.app1 .mval x : LTm C (.mv _)))
    (fun {_} x _ => (.app1 .ref x : LTm C (.mv _)))
    (fun x _ => (.app1 .wt x : LTm C (.val .bool)))
    (fun {_} r h x _ => (.app1 (.select r h) x : LTm C (.sts _)))
    (fun {_} {_} {_} h x _ => (.app1 (.selectIn h) x : LTm C (.sts _)))
    (fun {_} {_} {_} {_} h x _ => (.app1 (.fieldIn h) x : LTm C (.spath _ _)))
    (fun _ ex => (.app1 .toInt (ex : LTm C (.val .uint)) : LTm C .kint))
    (fun {_} {_} {_} shape _ ex => ex.map fun (gd, rd) => (gd, fixedCopyRd shape rd))

/-- A binary symbol, eliminated. -/
def _root_.Solidity.Op2.elim {a b s : Srt} (o : Op2 C a b s) : LTm C a → LTm C b → ElimM C a → ElimM C b →
    ElimM C s :=
  @Op2.casesOn C (fun a b s _ => LTm C a → LTm C b → ElimM C a → ElimM C b → ElimM C s) a b s o
    (fun op {_} h _ _ ex ey =>
      (.app2 (.binop op h) (ex : LTm C (.val _)) (ey : LTm C (.val _)) : LTm C (.val _)))
    (fun {_} x y ex ey => match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (g, Q) => (seqL (SFun.ok ex) (seqL g (.cond (SFun.rd ex (.has _) Q)
          (SFun.rd ex (.word _) Q) .err)) : LTm C (.val _))
      | none => (.app2 .find x y : LTm C (.val _)))
    (fun {_} x y ex ey => match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (g, Q) => (seqL (SFun.ok ex) (seqL g (.cond (SFun.rd ex (.has _) Q)
          (SFun.rd ex (.len _) Q) .err)) : LTm C (.val .uint))
      | none => (.app2 .len x y : LTm C (.val .uint)))
    (fun {_} x y _ _ => (.app2 .read x y : LTm C (.val _)))
    (fun {_} x y _ _ => (.app2 .mlen x y : LTm C (.val .uint)))
    (fun {_} {_} {_} it _ _ ex ey => pathAtIn it SFun.init ex ey)
    (fun {_} _ _ ex ey => pathNext ex ey)
    (fun {_} x y ex ey => match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (g, Q) => SFun.delAt ex g Q (.app2 .delAt x y)
      | none => SFun.ofOrig (.app2 .delAt x y))
    (fun {_} x y ex ey => match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (g, Q) => SFun.extend ex g Q (.app2 .pushSlot x y)
      | none => SFun.ofOrig (.app2 .pushSlot x y))
    (fun {_} x y ex ey => match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (g, Q) => SFun.pop false ex g Q (.app2 .pop x y)
      | none => SFun.ofOrig (.app2 .pop x y))
    (fun {_} x y ex ey => match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (g, Q) => SFun.pop true ex g Q (.app2 .shrink x y)
      | none => SFun.ofOrig (.app2 .shrink x y))
    (fun {_} x y ex ey => match (ey : Option (LTm C (.val .bool) × SPath C _)) with
      | some (g, Q) => SFun.extend ex g Q (.app2 .extend x y)
      | none => SFun.ofOrig (.app2 .extend x y))
    (fun {_} _ _ ex ey => (ey : Option (LTm C (.val .bool) × SPath C _)).map fun x =>
      (seqL (SFun.ok ex) (seqL x.1 (LTm.assert (SFun.rd ex (.has _) x.2))), SRd.at (SFun.rd ex) x.2))
    (fun {_} _ _ ex ey => some (seqL (.app2 .copyMem (ex : LTm C .mem) (ey : LTm C (.ident _))) .tt,
      copyMemRd ex ey))
    (fun {_} x y _ _ => (.app2 .iread x y : LTm C (.ident _)))
    (fun {_} h x y _ _ => (.app2 (.copy h) x y : LTm C (.ident _)))
    (fun {_} {_} a x y _ _ => (.app2 (.mat a) x y : LTm C (.addr _)))
    (fun {_} h x y _ _ => (.app2 (.copySt h) x y : LTm C .mem))
    (fun {_} {_} x y _ _ => (.app2 .findIn x y : LTm C (.val _)))
    (fun {_} {_} x y _ _ => (.app2 .delAtIn x y : LTm C (.sts _)))
    (fun {_} {_} _ _ _ _ => none)
    (fun op h _ _ ex ey => (.app2 (.zbin op h) (ex : LTm C .kint) (ey : LTm C .kint) : LTm C .kint))
    (fun op h _ _ ex ey =>
      (.app2 (.zcmp op h) (ex : LTm C .kint) (ey : LTm C .kint) : LTm C (.val .bool)))

/-- A ternary symbol, eliminated. -/
def _root_.Solidity.Op3.elim {a b c s : Srt} (o : Op3 C a b c s) : LTm C a → LTm C b → LTm C c → ElimM C a →
    ElimM C b → ElimM C c → ElimM C s :=
  @Op3.casesOn C (fun a b c s _ => LTm C a → LTm C b → LTm C c → ElimM C a → ElimM C b →
      ElimM C c → ElimM C s) a b c s o
    (fun {_} _ _ _ ex ey ez => (.app3 .ite (ex : LTm C (.val .bool)) (ey : LTm C (.val _))
      (ez : LTm C (.val _)) : LTm C (.val _)))
    (fun {_} x y z ex ey ez =>
      match (ey : Option (LTm C (.val .bool) × SPath C _)),
        (ez : Option (LTm C (.val .bool) × VRd C _)) with
      | some (g, Q), some (gv, V) => SFun.save ex g Q gv V (.app3 .save x y z)
      | _, _ => SFun.ofOrig (.app3 .save x y z))
    (fun {_} x y z ex ey ez =>
      match (ey : Option (LTm C (.val .bool) × SPath C _)),
        (ez : Option (LTm C (.val .bool) × VRd C _)) with
      | some (g, Q), some (gv, V) => SFun.push ex g Q gv V (.app3 .push x y z)
      | _, _ => SFun.ofOrig (.app3 .push x y z))
    (fun {_} {_} {_} it _ _ _ ex ey ez => pathAtIn it ex ey ez)
    (fun {_} x y z _ _ _ => (.app3 .write x y z : LTm C .mem))
    (fun {_} {_} x y z _ _ _ => (.app3 .saveIn x y z : LTm C (.sts _)))
    (fun op _ _ _ ex ey ez => foldModular op ex ey ez)

/-- `LTm.elim` by `match`, its compiled form. -/
def LTm.elimM : {s : Srt} → LTm C s → ElimM C s
  | _, .var k => (.var k : LTm C (.val _))
  | _, .app0 o => o.elim
  | _, .app1 o x => o.elim x x.elimM
  | _, .app2 o x y => o.elim x y x.elimM y.elimM
  | _, .app3 o x y z => o.elim x y z x.elimM y.elimM z.elimM
  | _, .index it q i => pathIdx it q.elimM i.elimM
  | _, .obsW q => ElimM.ofOrig _ (.obsW q)
  | _, .obsL q => ElimM.ofOrig _ (.obsL q)
  | _, .obsH q => ElimM.ofOrig _ (.obsH q)
  | s, .seq (s' := s') d a => ElimM.guarded s (ElimM.guard s' d.elimM d) a.elimM (.seq d a)
  | s, .orElse a b => ElimM.orElse s a.elimM b.elimM (.orElse a b)
  | s, .kite a b t e => ElimM.kite a.elimM b.elimM s t.elimM e.elimM (.kite a b t e)
  | s, .err => ElimM.ofOrig s .err

/-- **The elimination** of a term: every read of a write a reading of the
starting storage, by the recursor (Gate G0). -/
@[implemented_by LTm.elimM]
def LTm.elim {s : Srt} (t : LTm C s) : ElimM C s :=
  @LTm.rec C (fun s _ => ElimM C s)
    (fun {_} k => (.var k : LTm C (.val _)))
    (fun o => o.elim)
    (fun o x ex => o.elim x ex)
    (fun o x y ex ey => o.elim x y ex ey)
    (fun o x y z ex ey ez => o.elim x y z ex ey ez)
    (fun it _ _ eq ei => pathIdx it eq ei)
    (fun q _ => ElimM.ofOrig _ (.obsW q))
    (fun q _ => ElimM.ofOrig _ (.obsL q))
    (fun q _ => ElimM.ofOrig _ (.obsH q))
    (fun {s'} {s} d a ed ea => ElimM.guarded s (ElimM.guard s' ed d) ea (.seq d a))
    (fun {s} a b ea eb => ElimM.orElse s ea eb (.orElse a b))
    (fun {_} {s} a b t e ea eb et ee => ElimM.kite ea eb s et ee (.kite a b t e))
    (fun {s} => ElimM.ofOrig s .err)
    s t

theorem LTm.elim_eq_elimM {s : Srt} (t : LTm C s) : t.elim = t.elimM := by
  induction t with
  | var | app0 | obsW | obsL | obsH | err => rfl
  | app1 o x ih => simp only [LTm.elimM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.elimM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.elimM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.elimM, ← ihq, ← ihi]; rfl
  | seq d a ihd iha => simp only [LTm.elimM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.elimM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.elimM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- A formula, eliminated: each equation's two sides. -/
def LFml.elim : LFml C → LFml C
  | .tt => .tt
  | .eq a b => .eq (a.elim : LTm C (.val _)) (b.elim : LTm C (.val _))
  | .not φ => .not φ.elim
  | .and φ ψ => .and φ.elim ψ.elim
  | .imp φ ψ => .imp φ.elim ψ.elim
  | .all k p φ => .all k p φ.elim

end Decide

end Solidity
