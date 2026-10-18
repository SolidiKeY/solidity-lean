import Solidity.Calculus.AliasConstraints
import Solidity.Calculus.PathGuards

/-!
# Source terms flattened into typed read occurrences

Primitive observations become fresh typed atoms, guarded by the original
path's key computations. Occurrences are collected in dependency order.
Their interpretation hypothesis relates only successful paths to actual
storage reads; failed keys retain failed term evaluation. The equivalence
is local to that interpretation, before arithmetic/model reconstruction.
-/

namespace Solidity.Decide

open Semantics ReadRealization

variable {C : Contract}

structure ReadOccurrence (C : Contract) where
  prim : PrimTy
  path : SPath C (.prim prim)
  guard : SPath.Guard path
  slot : Nat

def ReadOccurrence.symbolic (r : ReadOccurrence C) : SymbolicRead C :=
  ⟨r.prim, r.path, .var r.slot⟩

/-- An inactive occurrence imposes no read value; a successful path must
read the exact value assigned to its typed atom. -/
def ReadOccurrence.Interpreted (g : State C []) (ν : AEnv) (r : ReadOccurrence C) : Prop :=
  ∀ q : SRef C (.prim r.prim), r.path.eval g ν = some q →
    ν.get r.prim r.slot = g.storage.obs.word (.ref q)

def ReadOccurrence.All (g : State C []) (ν : AEnv) (rs : List (ReadOccurrence C)) : Prop :=
  ∀ r ∈ rs, r.Interpreted g ν

theorem ReadOccurrence.All.append_iff (g : State C []) (ν : AEnv)
    (a b : List (ReadOccurrence C)) :
    ReadOccurrence.All g ν (a ++ b) ↔ ReadOccurrence.All g ν a ∧ ReadOccurrence.All g ν b := by
  constructor
  · intro h
    exact ⟨fun r hr => h r (List.mem_append_left _ hr),
      fun r hr => h r (List.mem_append_right _ hr)⟩
  · rintro ⟨ha, hb⟩ r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ha r hr
    · exact hb r hr

structure Flattened {s : Srt} (t : LTm C s) (start : Nat) where
  term : LTm C s
  reads : List (ReadOccurrence C)
  correct : ∀ (g : State C []) (ν : AEnv), ReadOccurrence.All g ν reads →
    term.eval g ν = t.eval g ν

namespace Flattened

def next {s : Srt} {t : LTm C s} {start : Nat} (a : Flattened t start) : Nat := start + a.reads.length

def pure {s : Srt} (t : LTm C s) (start : Nat) : Flattened t start :=
  ⟨t, [], fun _ _ _ => rfl⟩

def app1 {s u : Srt} (op : Op1 C s u) {t : LTm C s} {start : Nat}
    (a : Flattened t start) : Flattened (.app1 op t) start :=
  ⟨.app1 op a.term, a.reads, by
    intro g ν h
    rw [LTm.eval_app1, LTm.eval_app1, a.correct g ν h]⟩

def app2 {s u v : Srt} (op : Op2 C s u v) {t : LTm C s} {w : LTm C u} {start : Nat}
    (a : Flattened t start) (b : Flattened w a.next) : Flattened (.app2 op t w) start :=
  ⟨.app2 op a.term b.term, a.reads ++ b.reads, by
    intro g ν h
    obtain ⟨ha, hb⟩ := (ReadOccurrence.All.append_iff g ν _ _).mp h
    rw [LTm.eval_app2, LTm.eval_app2, a.correct g ν ha, b.correct g ν hb]⟩

def index {R : RefTy} {p : PrimTy} {T : Ty} (it : IndexTy R p T)
    {t : LTm C (.path (.ref R))} {k : LTm C (.val p)} {start : Nat}
    (a : Flattened t start) (b : Flattened k a.next) : Flattened (.index it t k) start :=
  ⟨.index it a.term b.term, a.reads ++ b.reads, by
    intro g ν h
    obtain ⟨ha, hb⟩ := (ReadOccurrence.All.append_iff g ν _ _).mp h
    rw [LTm.eval_index, LTm.eval_index, a.correct g ν ha, b.correct g ν hb]⟩

def seq {s u : Srt} {t : LTm C s} {w : LTm C u} {start : Nat}
    (a : Flattened t start) (b : Flattened w a.next) : Flattened (.seq t w) start :=
  ⟨.seq a.term b.term, a.reads ++ b.reads, by
    intro g ν h
    obtain ⟨ha, hb⟩ := (ReadOccurrence.All.append_iff g ν _ _).mp h
    rw [LTm.eval_seq, LTm.eval_seq, a.correct g ν ha, b.correct g ν hb]⟩

def orElse {s : Srt} {t w : LTm C s} {start : Nat}
    (a : Flattened t start) (b : Flattened w a.next) : Flattened (.orElse t w) start :=
  ⟨.orElse a.term b.term, a.reads ++ b.reads, by
    intro g ν h
    obtain ⟨ha, hb⟩ := (ReadOccurrence.All.append_iff g ν _ _).mp h
    rw [LTm.eval_orElse, LTm.eval_orElse, a.correct g ν ha, b.correct g ν hb]⟩

def kite {p : PrimTy} {s : Srt} {x y : LTm C (.val p)} {t e : LTm C s} {start : Nat}
    (a : Flattened x start) (b : Flattened y a.next)
    (thn : Flattened t b.next) (els : Flattened e thn.next) : Flattened (.kite x y t e) start :=
  ⟨.kite a.term b.term thn.term els.term, a.reads ++ (b.reads ++ (thn.reads ++ els.reads)), by
    intro g ν h
    obtain ⟨ha, h⟩ := (ReadOccurrence.All.append_iff g ν _ _).mp h
    obtain ⟨hb, h⟩ := (ReadOccurrence.All.append_iff g ν _ _).mp h
    obtain ⟨ht, he⟩ := (ReadOccurrence.All.append_iff g ν _ _).mp h
    rw [LTm.eval_kite, LTm.eval_kite, a.correct g ν ha, b.correct g ν hb,
      thn.correct g ν ht, els.correct g ν he]⟩

def word {p : PrimTy} {t : LTm C (.path (.prim p))} {start : Nat}
    (a : Flattened t start) (view : SPath.View a.term) (guard : SPath.Guard view.path) :
    Flattened (.obsW t) start :=
  ⟨.seq guard.test (.var a.next), a.reads ++ [⟨p, view.path, guard, a.next⟩], by
    intro g ν h
    obtain ⟨ha, hr⟩ := (ReadOccurrence.All.append_iff g ν _ _).mp h
    have hv := hr _ List.mem_cons_self
    rw [LTm.eval_seq, guard.correct g ν, LTm.eval_obsW,
      ← a.correct g ν ha, ← view.correct g ν]
    cases hp : view.path.eval g ν with
    | none => rfl
    | some r =>
      change some (ν.get p a.next) = some (g.storage.obs.word (.ref r))
      exact congrArg some (hv r hp)⟩

end Flattened

/-- One beyond every existing atom position, at all primitive types. -/
def LTm.atomBound : {s : Srt} → LTm C s → Nat
  | _, .var k => k + 1
  | _, .app0 _ | _, .err => 0
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => a.atomBound
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => max a.atomBound b.atomBound
  | _, .app3 _ a b c => max a.atomBound (max b.atomBound c.atomBound)
  | _, .kite a b t e => max a.atomBound (max b.atomBound (max t.atomBound e.atomBound))

/-- Agreement below a fresh-atom boundary, at every primitive type. -/
def AEnv.AgreesBelow (n : Nat) (ν μ : AEnv) : Prop :=
  ∀ (p : PrimTy) (k : Nat), k < n → ν.get p k = μ.get p k

theorem AEnv.AgreesBelow.mono {n m : Nat} {ν μ : AEnv} (h : ν.AgreesBelow n μ)
    (hm : m ≤ n) : ν.AgreesBelow m μ :=
  fun p k hk => h p k (Nat.lt_of_lt_of_le hk hm)

/-- Changing fresh atoms cannot change any existing source computation. -/
theorem LTm.eval_agree_below (g : State C []) {s : Srt} (t : LTm C s) {ν μ : AEnv}
    (h : ν.AgreesBelow t.atomBound μ) : t.eval g ν = t.eval g μ := by
  induction t with
  | var k => exact congrArg some (h _ k (Nat.lt_succ_self k))
  | app0 o | err => rfl
  | app1 o a ih => rw [eval_app1, eval_app1, ih h]
  | app2 o a b iha ihb =>
    rw [eval_app2, eval_app2, iha (h.mono (Nat.le_max_left _ _)), ihb (h.mono (Nat.le_max_right _ _))]
  | app3 o a b c iha ihb ihc =>
    rw [eval_app3, eval_app3, iha (h.mono (Nat.le_max_left _ _)),
      ihb (h.mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))),
      ihc (h.mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))]
  | index it a b iha ihb =>
    rw [eval_index, eval_index, iha (h.mono (Nat.le_max_left _ _)), ihb (h.mono (Nat.le_max_right _ _))]
  | obsW a ih => rw [eval_obsW, eval_obsW, ih h]
  | obsL a ih => rw [eval_obsL, eval_obsL, ih h]
  | obsH a ih => rw [eval_obsH, eval_obsH, ih h]
  | seq a b iha ihb =>
    rw [eval_seq, eval_seq, iha (h.mono (Nat.le_max_left _ _)), ihb (h.mono (Nat.le_max_right _ _))]
  | orElse a b iha ihb =>
    rw [eval_orElse, eval_orElse, iha (h.mono (Nat.le_max_left _ _)), ihb (h.mono (Nat.le_max_right _ _))]
  | kite a b t e iha ihb iht ihe =>
    rw [eval_kite, eval_kite, iha (h.mono (Nat.le_max_left _ _)),
      ihb (h.mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))),
      iht (h.mono (Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))),
      ihe (h.mono (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))]

/-- The second budget is shared across sibling branches. Exhaustion has no
semantic verdict; each accepted node carries its evaluation equivalence. -/
private def flattenFuel? : Nat → Nat → {s : Srt} → (t : LTm C s) → (start : Nat) →
    Option (Flattened t start × Nat)
  | 0, _, _, _, _ | _ + 1, 0, _, _, _ => none
  | _ + 1, remaining + 1, _, .var k, start => some (.pure (.var k) start, remaining)
  | _ + 1, remaining + 1, _, .app0 (.lit v), start => some (.pure (.lit v) start, remaining)
  | _ + 1, remaining + 1, _, .app0 (.env e), start => some (.pure (.app0 (.env e)) start, remaining)
  | _ + 1, remaining + 1, _, .app0 (.root r h), start => some (.pure (.app0 (.root r h)) start, remaining)
  | _ + 1, remaining + 1, _, .err, start => some (.pure .err start, remaining)
  | depth + 1, remaining + 1, _, .app1 (.field h) q, start => do
    let (a, remaining) ← flattenFuel? depth remaining q start
    return (.app1 (.field h) a, remaining)
  | depth + 1, remaining + 1, _, .app1 (.unop op h) q, start => do
    let (a, remaining) ← flattenFuel? depth remaining q start
    return (.app1 (.unop op h) a, remaining)
  | depth + 1, remaining + 1, _, .app2 (.binop op h) t w, start => do
    let (a, remaining) ← flattenFuel? depth remaining t start
    let (b, remaining) ← flattenFuel? depth remaining w a.next
    return (.app2 (.binop op h) a b, remaining)
  | depth + 1, remaining + 1, _, .index .map q k, start => do
    let (a, remaining) ← flattenFuel? depth remaining q start
    let (b, remaining) ← flattenFuel? depth remaining k a.next
    return (.index .map a b, remaining)
  | depth + 1, remaining + 1, _, .obsW q, start => do
    let (a, remaining) ← flattenFuel? depth remaining q start
    let view ← SPath.view? a.term
    let guard ← view.path.guard?
    return (.word a view guard, remaining)
  | depth + 1, remaining + 1, _, .seq t w, start => do
    let (a, remaining) ← flattenFuel? depth remaining t start
    let (b, remaining) ← flattenFuel? depth remaining w a.next
    return (.seq a b, remaining)
  | depth + 1, remaining + 1, _, .orElse t w, start => do
    let (a, remaining) ← flattenFuel? depth remaining t start
    let (b, remaining) ← flattenFuel? depth remaining w a.next
    return (.orElse a b, remaining)
  | depth + 1, remaining + 1, _, .kite x y t e, start => do
    let (a, remaining) ← flattenFuel? depth remaining x start
    let (b, remaining) ← flattenFuel? depth remaining y a.next
    let (thn, remaining) ← flattenFuel? depth remaining t b.next
    let (els, remaining) ← flattenFuel? depth remaining e thn.next
    return (.kite a b thn els, remaining)
  | _ + 1, _ + 1, _, _, _ => none

/-- Flatten a source term with a shared node/depth budget and an explicit
fresh-atom start. Callers composing terms share the resulting `next`. -/
def flattenTermAt? {s : Srt} (budget start : Nat) (t : LTm C s) : Option (Flattened t start) :=
  (flattenFuel? budget budget t start).map Prod.fst

/-- Start beyond every atom already written in this source term. -/
def flattenTerm? {s : Srt} (budget : Nat) (t : LTm C s) : Option (Flattened t t.atomBound) :=
  flattenTermAt? budget t.atomBound t

structure FlattenedFormula (φ : LFml C) (start : Nat) where
  formula : LFml C
  reads : List (ReadOccurrence C)
  correct : ∀ (g : State C []) (ν : AEnv), ReadOccurrence.All g ν reads →
    (formula.holds g ν ↔ φ.holds g ν)

namespace FlattenedFormula

def next {φ : LFml C} {start : Nat} (a : FlattenedFormula φ start) : Nat := start + a.reads.length

def tt (start : Nat) : FlattenedFormula (LFml.tt (C := C)) start :=
  ⟨.tt, [], fun _ _ _ => Iff.rfl⟩

def eq {p : PrimTy} {t w : LTm C (.val p)} {start : Nat}
    (a : Flattened t start) (b : Flattened w a.next) : FlattenedFormula (.eq t w) start :=
  ⟨.eq a.term b.term, a.reads ++ b.reads, by
    intro g ν h
    obtain ⟨ha, hb⟩ := (ReadOccurrence.All.append_iff g ν _ _).mp h
    simp only [LFml.holds, a.correct g ν ha, b.correct g ν hb]⟩

def not {φ : LFml C} {start : Nat} (a : FlattenedFormula φ start) :
    FlattenedFormula (.not φ) start :=
  ⟨.not a.formula, a.reads, fun g ν h => not_congr (a.correct g ν h)⟩

def and {φ ψ : LFml C} {start : Nat} (a : FlattenedFormula φ start)
    (b : FlattenedFormula ψ a.next) : FlattenedFormula (.and φ ψ) start :=
  ⟨.and a.formula b.formula, a.reads ++ b.reads, by
    intro g ν h
    obtain ⟨ha, hb⟩ := (ReadOccurrence.All.append_iff g ν _ _).mp h
    exact and_congr (a.correct g ν ha) (b.correct g ν hb)⟩

def imp {φ ψ : LFml C} {start : Nat} (a : FlattenedFormula φ start)
    (b : FlattenedFormula ψ a.next) : FlattenedFormula (.imp φ ψ) start :=
  ⟨.imp a.formula b.formula, a.reads ++ b.reads, by
    intro g ν h
    obtain ⟨ha, hb⟩ := (ReadOccurrence.All.append_iff g ν _ _).mp h
    exact imp_congr (a.correct g ν ha) (b.correct g ν hb)⟩

end FlattenedFormula

def LFml.atomBound : LFml C → Nat
  | .tt => 0
  | .eq a b => max a.atomBound b.atomBound
  | .not φ => φ.atomBound
  | .and φ ψ | .imp φ ψ => max φ.atomBound ψ.atomBound
  | .all k _ φ => max (k + 1) φ.atomBound

private def flattenFormulaFuel? : Nat → Nat → (φ : LFml C) → (start : Nat) →
    Option (FlattenedFormula φ start × Nat)
  | 0, _, _, _ | _ + 1, 0, _, _ => none
  | _ + 1, remaining + 1, .tt, start => some (.tt start, remaining)
  | depth + 1, remaining + 1, .eq t w, start => do
    let (a, remaining) ← flattenFuel? depth remaining t start
    let (b, remaining) ← flattenFuel? depth remaining w a.next
    return (.eq a b, remaining)
  | depth + 1, remaining + 1, .not φ, start => do
    let (a, remaining) ← flattenFormulaFuel? depth remaining φ start
    return (.not a, remaining)
  | depth + 1, remaining + 1, .and φ ψ, start => do
    let (a, remaining) ← flattenFormulaFuel? depth remaining φ start
    let (b, remaining) ← flattenFormulaFuel? depth remaining ψ a.next
    return (.and a b, remaining)
  | depth + 1, remaining + 1, .imp φ ψ, start => do
    let (a, remaining) ← flattenFormulaFuel? depth remaining φ start
    let (b, remaining) ← flattenFormulaFuel? depth remaining ψ a.next
    return (.imp a b, remaining)
  | _ + 1, _ + 1, .all .., _ => none

/-- Quantifier-free source formulas share one occurrence namespace and one
node budget. Universal prefixes are handled by the existing input layer. -/
def flattenFormulaAt? (budget start : Nat) (φ : LFml C) : Option (FlattenedFormula φ start) :=
  (flattenFormulaFuel? budget budget φ start).map Prod.fst

def flattenFormula? (budget : Nat) (φ : LFml C) : Option (FlattenedFormula φ φ.atomBound) :=
  flattenFormulaAt? budget φ.atomBound φ

end Solidity.Decide
