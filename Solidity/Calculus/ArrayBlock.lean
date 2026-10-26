import Solidity.Calculus.ArrayReduction
import Solidity.Calculus.ArrayProperty

/-!
# Leaves with blocks over storage arrays (M7, feature 30)

`arrayReduction?` (`Calculus/ArrayReduction.lean`) takes a leaf whose body
reads storage arrays at symbolic indices and holds no quantifier; the
quantified pipeline and `apfPrep` read no array.  A negative block over an
array (`(∀ uint i; i < 3 → arr[i] == 0) → arr.length > 5 → arr[1] == 0`)
reached neither.  This pipeline is the arrays' with a preparation stage
between the prefix and the array stages, as `Calculus/LedgerBlock.lean`
puts one before the ledger cut: the body's blocks instantiated at the
index set (`apfPrep`, `Calculus/ArrayProperty.lean`, each dynamic array of
primitives read at a block variable floored slot by slot,
`FloorShape.arr`), the instance's array reads cut and decided as
`arrayReduction?` decides them.

The verdict is exact (`Prep.valid_iff`): a refutation of the cut instance
is realized (`arrRealize`), then its arrays rebuilt at the floors of the
index set, each slot `i` holding what slot `⌊i⌋` held and the live length
kept (`FloorShape.rebuild`, `arr_rebuild_slot`, `arr_rebuild_len`).  An
array has no default inside its slots, so the rebuilt array lists every
slot up to the first value of the index set past the old slots, `2^256`
slots where there is none: a refutation that exists, as a term, but that
an evaluation may not build.
-/

namespace Solidity.Decide

open ReadRealization Linear

variable {C : Contract}

/-! ## Instances folded

An instance at a literal index (`3 == 3 → (3 < 3) == true → …`) has guards
that are comparisons of literals: folded, the instance is `true` or its
body, and an instance whose guard is false reads nothing.  The fold is
exact at every state (`LFml.litFold_holds`). -/

/-- A literal's value. -/
def _root_.Solidity.Op0.litV? {s : Srt} : Op0 C s → Option (s.Den C [])
  | .lit v => some v
  | _ => none

/-- A unary operator on a literal value. -/
def _root_.Solidity.Op1.litV? {a s : Srt} : Op1 C a s → Option (a.Den C []) → Option (s.Den C [])
  | .unop op h, x => x.bind (op.evalT h)
  | _, _ => none

/-- A binary operator on literal values. -/
def _root_.Solidity.Op2.litV? {a b s : Srt} :
    Op2 C a b s → Option (a.Den C []) → Option (b.Den C []) → Option (s.Den C [])
  | .binop op h, x, y => x.bind fun x => y.bind fun y => binopT op h x (some y)
  | _, _, _ => none

/-- The value of a term of literals and operators on them, where it
returns; `none` where it reads anything else, or halts. -/
def LTm.litVal? : {s : Srt} → LTm C s → Option (s.Den C [])
  | _, .app0 o => Op0.litV? o
  | _, .app1 o t => Op1.litV? o t.litVal?
  | _, .app2 o a b => Op2.litV? o a.litVal? b.litVal?
  | _, _ => none

/-- What `litVal?` says of a term's value: at a value sort, its value. -/
def LitAt (H : HTy) : (s : Srt) → s.Den C [] → Option (s.Den C H) → Prop
  | .val _, v, x => x = some v
  | _, _, _ => True

theorem LTm.litVal?_ok (g : State C []) (ν : AEnv) {s : Srt} (t : LTm C s) :
    ∀ v, t.litVal? = some v → LitAt g.H s v (t.eval g ν) := by
  induction t with
  | app0 o =>
    intro v h
    cases o <;> simp only [LTm.litVal?, Op0.litV?, Option.some.injEq, reduceCtorEq] at h
    subst h
    rfl
  | app1 o x ih =>
    intro v h
    cases o <;> simp only [LTm.litVal?, Op1.litV?, reduceCtorEq] at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hv⟩ := h
    have e : (x.eval g ν : Option _) = some w := ih w hw
    show _ = some v
    rw [LTm.eval_app1, Close.Op1.eval_unop, e, Option.bind_some]
    exact hv
  | app2 o a b iha ihb =>
    intro v h
    cases o <;> simp only [LTm.litVal?, Op2.litV?, reduceCtorEq] at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, hv⟩ := h
    have ea : (a.eval g ν : Option _) = some x := iha x hx
    have eb : (b.eval g ν : Option _) = some y := ihb y hy
    show _ = some v
    rw [LTm.eval_app2, Close.Op2.eval_binop, ea, eb, Option.bind_some]
    exact hv
  | _ => intro v h; simp only [LTm.litVal?, reduceCtorEq] at h

/-- `φ ∧ ψ`, a `true` side dropped. -/
def LFml.mkAnd : LFml C → LFml C → LFml C
  | .tt, ψ => ψ
  | φ, .tt => φ
  | φ, ψ => .and φ ψ

/-- `φ → ψ`, a `true` premise dropped, a `false` premise or a `true`
conclusion `true`. -/
def LFml.mkImp : LFml C → LFml C → LFml C
  | .tt, ψ => ψ
  | .not .tt, _ => .tt
  | _, .tt => .tt
  | φ, ψ => .imp φ ψ

theorem LFml.holds_mkAnd (g : State C []) (ν : AEnv) (φ ψ : LFml C) :
    (LFml.mkAnd φ ψ).holds g ν ↔ φ.holds g ν ∧ ψ.holds g ν := by
  unfold LFml.mkAnd
  split <;> simp only [LFml.holds, true_and, and_true]

theorem LFml.holds_mkImp (g : State C []) (ν : AEnv) (φ ψ : LFml C) :
    (LFml.mkImp φ ψ).holds g ν ↔ (φ.holds g ν → ψ.holds g ν) := by
  unfold LFml.mkImp
  split <;> simp only [LFml.holds, true_implies, not_true_eq_false, false_implies, implies_true]

/-- The position of an atom. -/
def LTm.varPos? : {s : Srt} → LTm C s → Option Nat
  | _, .var k => some k
  | _, _ => none

theorem LTm.eq_of_varPos? {p : PrimTy} {t : LTm C (.val p)} {k : Nat} (h : t.varPos? = some k) :
    t = .var k := by
  cases t <;> first | (simp only [LTm.varPos?, Option.some.injEq] at h; subst h; rfl) | cases h

/-- **Comparisons of literals, and of an atom with itself, folded.** -/
def LFml.litFold : LFml C → LFml C
  | .tt => .tt
  | .eq (p := p) a b =>
    if a.varPos?.isSome && a.varPos? == b.varPos? then .tt else
    match (a.litVal? : Option p.Denote), (b.litVal? : Option p.Denote) with
    | some x, some y => if x = y then .tt else .not .tt
    | _, _ => .eq a b
  | .not φ => .not φ.litFold
  | .and φ ψ => LFml.mkAnd φ.litFold ψ.litFold
  | .imp φ ψ => LFml.mkImp φ.litFold ψ.litFold
  | .all k p φ => .all k p φ.litFold

theorem LFml.litFold_holds (g : State C []) : ∀ (φ : LFml C) (ν : AEnv), φ.litFold.holds g ν ↔ φ.holds g ν
  | .tt, _ => Iff.rfl
  | .eq (p := p) a b, ν => by
    unfold LFml.litFold
    split
    · rename_i hv
      simp only [Bool.and_eq_true, Option.isSome_iff_exists, beq_iff_eq] at hv
      obtain ⟨⟨k, hk⟩, he⟩ := hv
      have hb : b.varPos? = some k := he ▸ hk
      rw [LTm.eq_of_varPos? hk, LTm.eq_of_varPos? hb]
      exact ⟨fun _ => (LFml.holds_eq_iff g ν _ _).2 ⟨_, rfl, rfl⟩, fun _ => trivial⟩
    split
    · rename_i x y hx hy
      have ea : (a.eval g ν : Option p.Denote) = some x := LTm.litVal?_ok g ν a x hx
      have eb : (b.eval g ν : Option p.Denote) = some y := LTm.litVal?_ok g ν b y hy
      rw [LFml.holds_eq_iff, ea, eb]
      split
      · rename_i e
        subst e
        exact ⟨fun _ => ⟨x, rfl, rfl⟩, fun _ => trivial⟩
      · rename_i e
        exact ⟨fun h => (h trivial).elim, fun ⟨z, h1, h2⟩ => (e
          ((Option.some.inj h1).trans (Option.some.inj h2).symm)).elim⟩
    · exact Iff.rfl
  | .not φ, ν => not_congr (LFml.litFold_holds g φ ν)
  | .and φ ψ, ν => by
    rw [LFml.litFold, LFml.holds_mkAnd, LFml.litFold_holds g φ ν, LFml.litFold_holds g ψ ν]
    rfl
  | .imp φ ψ, ν => by
    rw [LFml.litFold, LFml.holds_mkImp, LFml.litFold_holds g φ ν, LFml.litFold_holds g ψ ν]
    rfl
  | .all k p φ, ν => forall_congr' fun v => LFml.litFold_holds g φ _

/-! ## Lengths as atoms

A refutation's arrays are rebuilt with slot `i` holding what slot `⌊i⌋`
held, so the rebuilt array has a slot `i` exactly where `⌊i⌋` is below the
old slots: past the index set's largest value below them, every slot up to
`2^256` is there.  With the array's live length in the index set the
slots stop at it (`arr_rebuild_slot`, where the old array has no slot past
its length).  The length is no index term the cut takes (an index may read
no array, `LTm.aFree`), so it is read as an atom first: each dynamic array
of primitives the blocks read at their variables gets a fresh atom past
the body's, its length reads replaced by it (`LTm.lenRep`) and its
definition in front (`HDef`, as `hoistPrep` hoists reads).  Exact: the
atoms set to the lengths where the prepared body holds, the same state and
atoms where it fails (`lenPrep`). -/

/-- A dynamic array of primitives at a root. -/
structure LenRoot (C : Contract) where
  a : Name
  e : PrimTy
  h : C.rootType a = some (.ref (.array (.prim e)))

/-- The root a name holds, if a dynamic array of primitives. -/
def LenRoot.of? (a : Name) : Option (LenRoot C) :=
  match h : C.rootType a with
  | some (.ref (.array (.prim e))) => some ⟨a, e, h⟩
  | _ => none

/-- The dynamic arrays of primitives the negative `uint` blocks read at
their variables, each once. -/
def lenRoots (B : LFml C) : List (LenRoot C) := (B.blockRoots .uint true).eraseDups.filterMap LenRoot.of?

/-- Each with its atom, from `n` on. -/
def lenAtoms : Nat → List (LenRoot C) → List (LenRoot C × Nat)
  | _, [] => []
  | n, r :: rs => (r, n) :: lenAtoms (n + 1) rs

theorem lenAtoms_keys : ∀ (n : Nat) (rs : List (LenRoot C)),
    (lenAtoms n rs).map (·.2) = List.range' n rs.length
  | _, [] => rfl
  | n, r :: rs => by
    rw [lenAtoms, List.map_cons, lenAtoms_keys (n + 1) rs, List.length_cons, List.range'_succ]

/-- The atom's definition: the root's live length. -/
def LenRoot.hdef (d : LenRoot C × Nat) : HDef C := ⟨.uint, .obsL (.app0 (.root d.1.a d.1.h)), d.2⟩

/-- A bare state variable's name. -/
def LTm.bareRoot? : {s : Srt} → LTm C s → Option Name
  | _, .app0 (.root r _) => some r
  | _, _ => none

/-- The atom of a root, if it has one. -/
def lenAtomOf : List (LenRoot C × Nat) → Name → Option Nat
  | [], _ => none
  | (r, m) :: ds, a => if r.a = a then some m else lenAtomOf ds a

theorem lenAtomOf_mem {a : Name} {m : Nat} : ∀ {ds : List (LenRoot C × Nat)}, lenAtomOf ds a = some m →
    ∃ r, (r, m) ∈ ds ∧ r.a = a
  | [], h => nomatch h
  | (r, m') :: ds, h => by
    unfold lenAtomOf at h
    split at h
    · rename_i hr
      cases h
      exact ⟨r, List.mem_cons_self, hr⟩
    · obtain ⟨r', h1, h2⟩ := lenAtomOf_mem h
      exact ⟨r', List.mem_cons_of_mem _ h1, h2⟩

/-- **Every length read of a root of `ds` read as its atom.** -/
def LTm.lenRep (ds : List (LenRoot C × Nat)) : {s : Srt} → LTm C s → LTm C s
  | _, .var k => .var k
  | _, .app0 o => .app0 o
  | _, .app1 o x => .app1 o (x.lenRep ds)
  | _, .app2 o x y => .app2 o (x.lenRep ds) (y.lenRep ds)
  | _, .app3 o x y z => .app3 o (x.lenRep ds) (y.lenRep ds) (z.lenRep ds)
  | _, .index it q i => .index it (q.lenRep ds) (i.lenRep ds)
  | _, .obsW q => .obsW (q.lenRep ds)
  | _, .obsL q =>
    match q.bareRoot?.bind (lenAtomOf ds) with
    | some m => .var m
    | none => .obsL (q.lenRep ds)
  | _, .obsH q => .obsH (q.lenRep ds)
  | _, .seq d a => .seq (d.lenRep ds) (a.lenRep ds)
  | _, .orElse a b => .orElse (a.lenRep ds) (b.lenRep ds)
  | _, .kite a b t e => .kite (a.lenRep ds) (b.lenRep ds) (t.lenRep ds) (e.lenRep ds)
  | _, .err => .err

/-- A length read of a root read alike at any of its types' proofs. -/
theorem lenRoot_read (g : State C []) (ν : AEnv) (r : LenRoot C) {E : Ty}
    (h : C.rootType r.a = some (.ref (.array E))) :
    (LTm.eval g ν (.obsL (.app0 (.root r.a h))) : Option PrimTy.uint.Denote) =
      (LTm.eval g ν (.obsL (.app0 (.root r.a r.h))) : Option PrimTy.uint.Denote) := by
  have e : (Ty.ref (.array E)) = .ref (.array (.prim r.e)) := Option.some.inj (h.symm.trans r.h)
  cases e
  rfl

theorem LTm.eval_lenRep (g : State C []) (ν : AEnv) (ds : List (LenRoot C × Nat))
    (hG : ∀ d ∈ ds, (LenRoot.hdef d).Good g ν) : ∀ {s : Srt} (t : LTm C s), (t.lenRep ds).eval g ν = t.eval g ν := by
  intro s t
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih => rw [LTm.lenRep, LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o x y ihx ihy => rw [LTm.lenRep, LTm.eval_app2, LTm.eval_app2, ihx, ihy]
  | app3 o x y z ihx ihy ihz => rw [LTm.lenRep, LTm.eval_app3, LTm.eval_app3, ihx, ihy, ihz]
  | index it q i ihq ihi => rw [LTm.lenRep, LTm.eval_index, LTm.eval_index, ihq, ihi]
  | obsW q ih => rw [LTm.lenRep, LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsH q ih => rw [LTm.lenRep, LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq d a ihd iha => rw [LTm.lenRep, LTm.eval_seq, LTm.eval_seq, ihd, iha]
  | orElse a b iha ihb => rw [LTm.lenRep, LTm.eval_orElse, LTm.eval_orElse, iha, ihb]
  | kite a b t e iha ihb iht ihe => rw [LTm.lenRep, LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]
  | obsL q ih =>
    unfold LTm.lenRep
    split
    · rename_i m hm
      rw [Option.bind_eq_some_iff] at hm
      obtain ⟨a, ha, hm⟩ := hm
      obtain ⟨r, hr, rfl⟩ := lenAtomOf_mem hm
      have hg := hG _ hr
      unfold HDef.Good LenRoot.hdef at hg
      cases q with
      | app0 o =>
        cases o with
        | root a' h' =>
          simp only [LTm.bareRoot?, Option.some.injEq] at ha
          subst ha
          rw [lenRoot_read g ν r h']
          exact hg.symm
        | _ => simp only [LTm.bareRoot?, reduceCtorEq] at ha
      | _ => simp only [LTm.bareRoot?, reduceCtorEq] at ha
    · rw [LTm.eval_obsL, LTm.eval_obsL, ih]

/-- Every length read of a root of `ds` read as its atom, in a formula. -/
def LFml.lenRep (ds : List (LenRoot C × Nat)) : LFml C → LFml C
  | .tt => .tt
  | .eq a b => .eq (a.lenRep ds) (b.lenRep ds)
  | .not φ => .not (φ.lenRep ds)
  | .and φ ψ => .and (φ.lenRep ds) (ψ.lenRep ds)
  | .imp φ ψ => .imp (φ.lenRep ds) (ψ.lenRep ds)
  | .all k p φ => .all k p (φ.lenRep ds)

theorem LFml.holds_lenRep (g : State C []) (ds : List (LenRoot C × Nat)) (n : Nat)
    (hn : ∀ d ∈ ds, n ≤ d.2) :
    ∀ (φ : LFml C) (ν : AEnv), φ.atomBound ≤ n → (∀ d ∈ ds, (LenRoot.hdef d).Good g ν) →
      ((φ.lenRep ds).holds g ν ↔ φ.holds g ν)
  | .tt, _, _, _ => Iff.rfl
  | .eq a b, ν, _, hG => by
    simp only [LFml.lenRep, LFml.holds, LTm.eval_lenRep g ν ds hG]
  | .not φ, ν, hb, hG => not_congr (LFml.holds_lenRep g ds n hn φ ν hb hG)
  | .and φ ψ, ν, hb, hG => by
    simp only [LFml.atomBound, Nat.max_le] at hb
    exact and_congr (LFml.holds_lenRep g ds n hn φ ν hb.1 hG) (LFml.holds_lenRep g ds n hn ψ ν hb.2 hG)
  | .imp φ ψ, ν, hb, hG => by
    simp only [LFml.atomBound, Nat.max_le] at hb
    exact imp_congr (LFml.holds_lenRep g ds n hn φ ν hb.1 hG) (LFml.holds_lenRep g ds n hn ψ ν hb.2 hG)
  | .all k p φ, ν, hb, hG => by
    simp only [LFml.atomBound, Nat.max_le] at hb
    exact forall_congr' fun v => LFml.holds_lenRep g ds n hn φ _ hb.2 fun d hd =>
      HDef.good_set (hG d hd) p k v (fun h => nomatch h) (by have := hn d hd; simp only [LenRoot.hdef]; omega)

/-- **Each array's live length read as an atom**, its definition in front:
exact at every state (`Prep`). -/
def lenPrep (B : LFml C) : Prep B where
  body := .imp (LFml.conj ((lenAtoms B.atomBound (lenRoots B)).map fun d => (LenRoot.hdef d).fml))
    (B.lenRep (lenAtoms B.atomBound (lenRoots B)))
  sound := fun hv g ν => by
    let ds := lenAtoms B.atomBound (lenRoots B)
    have hge : ∀ d ∈ ds, B.atomBound ≤ d.2 := fun d hd => by
      have hm : d.2 ∈ ds.map (·.2) := List.mem_map.2 ⟨d, hd, rfl⟩
      rw [lenAtoms_keys, List.mem_range'_1] at hm
      exact hm.1
    let es := ds.map LenRoot.hdef
    have hes : ∀ e ∈ es, B.atomBound ≤ e.m := fun e he => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
      exact hge d hd
    have hnd : (es.map (·.m)).Nodup := by
      rw [List.map_map]
      show (ds.map (·.2)).Nodup
      rw [lenAtoms_keys]
      exact List.nodup_range'
    let μ := HDef.fill g ν es ν
    have hagree : ν.AgreesBelow B.atomBound μ := HDef.fill_below g ν B.atomBound es ν hes
    have hgood : ∀ d ∈ ds, (LenRoot.hdef d).Good g μ := fun d hd => by
      have hfill := HDef.fill_get g ν es ν hnd (LenRoot.hdef d) (List.mem_map.2 ⟨d, hd, rfl⟩)
      unfold HDef.Good
      rw [hfill]
      rfl
    have hc : (LFml.conj (ds.map fun d => (LenRoot.hdef d).fml)).holds g μ := by
      rw [LFml.holds_conj]
      intro f hf
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hf
      exact (HDef.holds_fml g μ _).2 (hgood d hd)
    have hB := (LFml.holds_lenRep g ds B.atomBound hge B μ (Nat.le_refl _) hgood).1 (hv g μ hc)
    exact (LFml.holds_agree_below g B hagree).2 hB
  refute := fun g ν hn => ⟨g, fun hB => hn fun hc => by
    have hge : ∀ d ∈ lenAtoms B.atomBound (lenRoots B), B.atomBound ≤ d.2 := fun d hd => by
      have hm : d.2 ∈ (lenAtoms B.atomBound (lenRoots B)).map (·.2) := List.mem_map.2 ⟨d, hd, rfl⟩
      rw [lenAtoms_keys, List.mem_range'_1] at hm
      exact hm.1
    rw [LFml.holds_conj] at hc
    exact (LFml.holds_lenRep g _ B.atomBound hge B ν (Nat.le_refl _) fun d hd =>
      (HDef.holds_fml g ν _).1 (hc _ (List.mem_map.2 ⟨d, hd, rfl⟩))).2 hB⟩

/-- The length atoms, as index terms. -/
def lenKeys (B : LFml C) : List (LTm C (.val .uint)) :=
  (lenAtoms B.atomBound (lenRoots B)).map fun d => .var d.2

/-- **The preparation of a body with blocks over arrays**: the lengths as
atoms (`lenPrep`), then the blocks instantiated with them in the index set
(`apfPrepWith`). -/
@[irreducible] def blockPrep (B : LFml C) : Prep B := (lenPrep B).trans (apfPrepWith (lenKeys B) (lenPrep B).body)

/-! ## The Theory's slot reads folded

The elimination reads an element `q` of a storage array as the Theory
reads it, `orElse(if has(q) then find(q) else ⊥, d)` with `d` the
default: the slot's word where it is there, the default where not.  The
storage's own word at a slot not there is the default too, so at a total
path that is `find(q)` (`LTm.slotFold`): one read where there were two,
and no fallback to lift. -/

/-- The path of a slot test. -/
def LTm.hasPath? : LTm C (.val .bool) → Option ((T : Ty) × LTm C (.path T))
  | .obsH q => some ⟨_, q⟩
  | _ => none

/-- The path of a word read. -/
def LTm.wordPath? {p : PrimTy} : LTm C (.val p) → Option (LTm C (.path (.prim p)))
  | .obsW q => some q
  | _ => none

theorem LTm.eq_of_hasPath? {c : LTm C (.val .bool)} {T : Ty} {q : LTm C (.path T)}
    (h : c.hasPath? = some ⟨T, q⟩) : c = .obsH q := by
  cases c <;> simp only [LTm.hasPath?, reduceCtorEq, Option.some.injEq] at h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj h
  cases eq_of_heq h
  rfl

theorem LTm.eq_of_wordPath? {p : PrimTy} {x : LTm C (.val p)} {q : LTm C (.path (.prim p))}
    (h : x.wordPath? = some q) : x = .obsW q := by
  cases x <;> simp only [LTm.wordPath?, reduceCtorEq, Option.some.injEq] at h
  subst h
  rfl

theorem LTm.eq_of_isErr {s : Srt} {y : LTm C s} (h : y.isErr = true) : y = .err := by
  cases y <;> first | rfl | simp only [LTm.isErr, Bool.false_eq_true] at h

/-- `orElse(if has(q) then find(q) else ⊥, d)`, `q` total and `d` the
default: `find(q)`. -/
def slotIte? {p : PrimTy} (c : LTm C (.val .bool)) (x y d : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match c.hasPath?, x.wordPath? with
  | some ⟨_, qh⟩, some qw =>
    if (qh.beqR qw && y.isErr && qw.totalB && (d.litVal? : Option p.Denote) == some (PrimTy.dflt p)) = true
    then some (.obsW qw) else none
  | _, _ => none

def _root_.Solidity.Op3.slotRead? {a b c s : Srt} :
    Op3 C a b c s → LTm C a → LTm C b → LTm C c → LTm C s → Option (LTm C s)
  | .ite, c, x, y, d => slotIte? c x y d
  | _, _, _, _, _ => none

/-- The slot read of `orElse(a, d)`, if it is one. -/
def LTm.slotRead? {s : Srt} : LTm C s → LTm C s → Option (LTm C s)
  | .app3 o c x y, d => o.slotRead? c x y d
  | _, _ => none

/-- **The Theory's slot reads folded**, in every term. -/
def LTm.slotFold : {s : Srt} → LTm C s → LTm C s
  | _, .var k => .var k
  | _, .app0 o => .app0 o
  | _, .app1 o x => .app1 o x.slotFold
  | _, .app2 o x y => .app2 o x.slotFold y.slotFold
  | _, .app3 o x y z => .app3 o x.slotFold y.slotFold z.slotFold
  | _, .index it q i => .index it q.slotFold i.slotFold
  | _, .obsW q => .obsW q.slotFold
  | _, .obsL q => .obsL q.slotFold
  | _, .obsH q => .obsH q.slotFold
  | _, .seq d a => .seq d.slotFold a.slotFold
  | _, .orElse a b =>
    match a.slotRead? b with
    | some t => t
    | none => .orElse a.slotFold b.slotFold
  | _, .kite a b t e => .kite a.slotFold b.slotFold t.slotFold e.slotFold
  | _, .err => .err

theorem slotIte?_eval (g : State C []) (ν : AEnv) {p : PrimTy} {c : LTm C (.val .bool)}
    {x y d t : LTm C (.val p)} (h : slotIte? c x y d = some t) :
    t.eval g ν = (LTm.orElse (.app3 .ite c x y) d).eval g ν := by
  unfold slotIte? at h
  split at h
  · rename_i T qh qw hc hx
    split at h
    · rename_i hb
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨⟨⟨hq, hy⟩, ht⟩, hd⟩ := hb
      have e := LTm.sigma_eq_of_beqR hq
      obtain ⟨hT, e⟩ := Sigma.mk.inj e
      injection hT with hT'
      subst hT'
      cases eq_of_heq e
      rw [LTm.eq_of_hasPath? hc, LTm.eq_of_wordPath? hx, LTm.eq_of_isErr hy]
      have hdv : (d.eval g ν : Option p.Denote) = some (PrimTy.dflt p) := LTm.litVal?_ok g ν d _ hd
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (LTm.totalB_eval g ν qw ht)
      rw [LTm.eval_orElse, LTm.eval_app3, Close.Op3.eval_ite, LTm.eval_obsH, LTm.eval_obsW, hr, hdv]
      simp only [Option.bind_some]
      cases hh : g.storage.obs.has (.ref r) with
      | true => rfl
      | false =>
        show some (g.storage.obs.word (.ref r)) = some (PrimTy.dflt p)
        rw [Storage.obs_has_ref] at hh
        rw [Storage.obs_word_ref]
        show some (SVal.wordOf ((g.storage.get r.hroot).findM r.path)) = _
        cases hf : (g.storage.get r.hroot).findM r.path with
        | none => rfl
        | some v =>
          have : ((g.storage.get r.hroot).findM r.path).isSome = false := hh
          rw [hf] at this
          cases this
    · cases h
  · cases h

theorem LTm.slotRead?_eval (g : State C []) (ν : AEnv) {s : Srt} (a d t : LTm C s)
    (h : a.slotRead? d = some t) : t.eval g ν = (LTm.orElse a d).eval g ν := by
  cases a with
  | app3 o c x y =>
    cases o with
    | ite => exact slotIte?_eval g ν h
    | _ => simp only [LTm.slotRead?, Op3.slotRead?, reduceCtorEq] at h
  | _ => simp only [LTm.slotRead?, reduceCtorEq] at h

theorem LTm.eval_slotFold (g : State C []) (ν : AEnv) : ∀ {s : Srt} (t : LTm C s),
    t.slotFold.eval g ν = t.eval g ν := by
  intro s t
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih => rw [LTm.slotFold, LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o x y ihx ihy => rw [LTm.slotFold, LTm.eval_app2, LTm.eval_app2, ihx, ihy]
  | app3 o x y z ihx ihy ihz => rw [LTm.slotFold, LTm.eval_app3, LTm.eval_app3, ihx, ihy, ihz]
  | index it q i ihq ihi => rw [LTm.slotFold, LTm.eval_index, LTm.eval_index, ihq, ihi]
  | obsW q ih => rw [LTm.slotFold, LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL q ih => rw [LTm.slotFold, LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH q ih => rw [LTm.slotFold, LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq d a ihd iha => rw [LTm.slotFold, LTm.eval_seq, LTm.eval_seq, ihd, iha]
  | kite a b t e iha ihb iht ihe => rw [LTm.slotFold, LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]
  | orElse a b iha ihb =>
    unfold LTm.slotFold
    split
    · rename_i t ht
      exact LTm.slotRead?_eval g ν a b t ht
    · rw [LTm.eval_orElse, LTm.eval_orElse, iha, ihb]

/-- The slot reads of a formula folded. -/
def LFml.slotFold : LFml C → LFml C
  | .tt => .tt
  | .eq a b => .eq a.slotFold b.slotFold
  | .not φ => .not φ.slotFold
  | .and φ ψ => .and φ.slotFold ψ.slotFold
  | .imp φ ψ => .imp φ.slotFold ψ.slotFold
  | .all k p φ => .all k p φ.slotFold

theorem LFml.slotFold_holds (g : State C []) : ∀ (φ : LFml C) (ν : AEnv), φ.slotFold.holds g ν ↔ φ.holds g ν
  | .tt, _ => Iff.rfl
  | .eq a b, ν => by simp only [LFml.slotFold, LFml.holds, LTm.eval_slotFold]
  | .not φ, ν => not_congr (LFml.slotFold_holds g φ ν)
  | .and φ ψ, ν => and_congr (LFml.slotFold_holds g φ ν) (LFml.slotFold_holds g ψ ν)
  | .imp φ ψ, ν => imp_congr (LFml.slotFold_holds g φ ν) (LFml.slotFold_holds g ψ ν)
  | .all k p φ, ν => forall_congr' fun v => LFml.slotFold_holds g φ _

/-- The body with its blocks instantiated (`apfPrep`), comparisons of
literals folded, its slot tests folded and its fallbacks lifted. -/
@[irreducible] def LFml.blockLift (B : LFml C) : LFml C :=
  ((blockPrep B).body.slotFold.litFold.hasFold.orLift orFuel).litFold

theorem LFml.blockLift_holds (g : State C []) (B : LFml C) (ν : AEnv) :
    B.blockLift.holds g ν ↔ (blockPrep B).body.holds g ν := by
  unfold LFml.blockLift
  exact (LFml.litFold_holds g _ ν).trans ((LFml.orLift_holds g orFuel _ ν).trans
    ((LFml.hasFold_holds g _ ν).trans ((LFml.litFold_holds g _ ν).trans (LFml.slotFold_holds g _ ν))))

/-- **The array stages of a body with blocks**: its universal prefix, the
blocks instantiated (`apfPrep`), the fallbacks lifted and the arrays cut. -/
structure ArrayBlockBody (ψ : LFml C) where
  pre : UniversalPrefix ψ
  covered : ∀ q ∈ pre.body.freeParams, q ∈ pre.parameters
  cut : LFml C
  reads : List (ARead C)
  hcut : pre.body.blockLift.aCut? pre.body.blockLift.atomBound = some (cut, reads)

namespace ArrayBlockBody

/-- The cut instance, its comparisons of literals folded again (the index
atoms of reads at literal indices). -/
abbrev core {ψ : LFml C} (b : ArrayBlockBody ψ) : LFml C := b.cut.litFold

/-- The leaf the arithmetic stages take. -/
abbrev leaf {ψ : LFml C} (b : ArrayBlockBody ψ) : LFml C := b.core.gx.liftCond condLiftFuel

theorem holds_body {ψ : LFml C} (b : ArrayBlockBody ψ) (g : State C []) (ν : AEnv)
    (h : ψ.holds g AEnv.dflt) : b.pre.body.holds g ν := by
  have := b.pre.instantiate g AEnv.dflt ν h
  refine (LFml.holds_agree_free g _ fun q hq => ?_).1 this
  rw [Parameters.read_assign, if_pos (b.covered q hq)]

/-- **The leaf is valid exactly where the cut, lifted instance is.** -/
theorem valid_iff {ψ : LFml C} (b : ArrayBlockBody ψ) :
    (∀ g, ψ.holds g AEnv.dflt) ↔ b.leaf.Valid := by
  rw [LFml.liftCond_valid]
  have hgx : b.core.gx.Valid ↔ b.cut.Valid :=
    forall_congr' fun g => forall_congr' fun ν => (LFml.gx_holds g _ ν).trans (LFml.litFold_holds g _ ν)
  rw [hgx, LFml.aCut_valid_iff b.hcut (Nat.le_refl _)]
  have hl : b.pre.body.blockLift.Valid ↔ (blockPrep b.pre.body).body.Valid :=
    forall_congr' fun g => forall_congr' fun ν => LFml.blockLift_holds g _ ν
  rw [hl, (blockPrep b.pre.body).valid_iff]
  constructor
  · intro h g ν
    exact b.holds_body g ν (h g)
  · intro h g
    exact b.pre.close g AEnv.dflt fun ν => h g ν

/-- The state the cut instance's atoms realize (`arrRealize`). -/
def realized {ψ : LFml C} (b : ArrayBlockBody ψ) (g : State C []) (ν : AEnv) : State C [] :=
  arrRealize ν b.pre.body.blockLift.atomBound b.reads g

theorem realized_refutes {ψ : LFml C} (b : ArrayBlockBody ψ) (g : State C []) (ν : AEnv)
    (hK : ¬ b.cut.holds g ν) : ¬ (blockPrep b.pre.body).body.holds (b.realized g ν) ν := fun hP =>
  LFml.aCut_refutes b.hcut g ν hK ((LFml.blockLift_holds (b.realized g ν) b.pre.body ν).mpr hP)

/-- **A refutation of the cut instance refutes the leaf**, in the state its
arrays are realized in, then rebuilt at the floors. -/
def refutesCut {ψ : LFml C} (b : ArrayBlockBody ψ) (g : State C []) (ν : AEnv)
    (hK : ¬ b.cut.holds g ν) : {σ : State C [] // ¬ ψ.holds σ AEnv.dflt} :=
  ⟨((blockPrep b.pre.body).refute (b.realized g ν) ν (b.realized_refutes g ν hK)).1, fun hψ =>
    ((blockPrep b.pre.body).refute (b.realized g ν) ν (b.realized_refutes g ν hK)).2 (b.holds_body _ ν hψ)⟩

/-- **A refutation of the arithmetic's leaf refutes the leaf**. -/
def refutes {ψ : LFml C} (b : ArrayBlockBody ψ) (g : State C []) (ν : AEnv)
    (h : ¬ b.leaf.holds g ν) : {σ : State C [] // ¬ ψ.holds σ AEnv.dflt} :=
  b.refutesCut g ν fun hk => h ((LFml.liftCond_holds g _ _ ν).mpr ((LFml.gx_holds g _ ν).mpr
    ((LFml.litFold_holds g _ ν).mpr hk)))

end ArrayBlockBody

/-- The array stages with blocks, computed. -/
def arrayBlockBody? (ψ : LFml C) : Option (ArrayBlockBody ψ) := do
  let u ← UniversalPrefix.ofFormula? 1024 ψ
  if hc : ∀ q ∈ u.body.freeParams, q ∈ u.parameters then
    if (blockPrep u.body).body.slotFold.litFold.ors ≤ orBudget then
      match hk : u.body.blockLift.aCut? u.body.blockLift.atomBound with
      | some (K, rs) => some ⟨u, hc, K, rs, hk⟩
      | none => none
    else none
  else none

/-- **A leaf with blocks over storage arrays, decided by arithmetic.** -/
structure ArrayBlockReduction (φ : Fml C []) where
  normalization : DeclarationReduction φ
  source : SourceReduction normalization.formula
  body : ArrayBlockBody source.leaf.elim.condSimp.prenex
  flat : FlattenedArithmetic body.leaf

/-- **The pipeline**: the arrays' (`arrayReduction?`), the body prepared by
array property instantiation (`apfPrep`) before the array stages. -/
def arrayBlockReduction? (φ : Fml C []) : Option (ArrayBlockReduction φ) := do
  let d ← ProgramNormalization.ofFormula? 2048 φ
  let r ← sourceReduction? d.formula
  let b ← arrayBlockBody? r.leaf.elim.condSimp.prenex
  if (b.core.gx.liftCondB condLiftFuel liftBudget).isNone then none
  return ⟨d, r, b, ← flattenedArithmetic? (readBudget b.leaf.cutAll) b.leaf⟩

namespace ArrayBlockReduction

theorem leaf_iff {φ : Fml C []} (r : ArrayBlockReduction φ) :
    Fml.Valid φ ↔ ∀ g, r.source.leaf.elim.condSimp.prenex.holds g AEnv.dflt := by
  constructor
  · intro h g
    exact (LFml.prenex_holds g _ _).mpr ((LFml.condSimp_holds g _ _).mpr
      ((r.source.elim_holds_iff g).mpr ((r.normalization.correct g).mpr (h g))))
  · intro h g
    exact (r.normalization.correct g).mp ((r.source.elim_holds_iff g).mp
      ((LFml.condSimp_holds g _ _).mp ((LFml.prenex_holds g _ _).mp (h g))))

theorem valid_iff {φ : Fml C []} (r : ArrayBlockReduction φ) :
    Fml.Valid φ ↔ r.flat.encoding.arithmetic.Valid :=
  r.leaf_iff.trans (r.body.valid_iff.trans r.flat.valid_iff)

/-- A countermodel of the arithmetic, as a state refuting the leaf. -/
def countermodelOf {φ : Fml C []} (r : ArrayBlockReduction φ)
    (cm : {vs // ¬ r.flat.encoding.arithmetic.holds vs}) : {σ : State C [] // ¬ holds σ φ} :=
  let actual := r.flat.countermodelOf cm
  let s := r.body.refutes actual.state actual.atoms actual.refutes
  ⟨s.1, fun hv => s.2 ((LFml.prenex_holds _ _ _).mpr ((LFml.condSimp_holds _ _ _).mpr
    ((r.source.elim_holds_iff _).mpr ((r.normalization.correct _).mpr hv))))⟩

/-- **The verdict**: a proof, or a countermodel, its counterassignment first
shrunk (`ArrayReduction.shrinkCodes`). -/
def verify {φ : Fml C []} (r : ArrayBlockReduction φ) :
    Sum (PLift (Fml.Valid φ)) {σ : State C [] // ¬ holds σ φ} :=
  let A := r.flat.encoding.arithmetic
  match A.guarded.verify with
  | .inl h => .inl ⟨r.valid_iff.mpr (A.valid_iff.mpr h.down)⟩
  | .inr ⟨x, hx⟩ =>
    let x' := ArrayReduction.codesOf
      (ArrayReduction.shrinkCodes A.guarded 4 ((List.range A.guarded.width).map x).toArray)
    if h : A.guarded.check x' = false then
      .inr (r.countermodelOf (A.countermodelOf x' fun hv =>
        Bool.false_ne_true (h ▸ (AFml.check_iff _ _).mpr hv)))
    else .inr (r.countermodelOf (A.countermodelOf x hx))

end ArrayBlockReduction

/-! ## The fragment -/

/-- **The eliminated leaf's fragment with blocks over arrays**: the array
stages with blocks succeed, and their leaf is in `LFml.Src true`, of lifting
weight below `condLiftFuel`, lifted within the budget and within M4's node
bound. -/
def LFml.arrayBlockCovered (ψ : LFml C) : Bool :=
  match arrayBlockBody? ψ with
  | some b =>
    (b.core.gx.src? true).isSome && decide (b.core.gx.condMax < condLiftFuel) &&
      (b.core.gx.liftCondB condLiftFuel liftBudget).isSome &&
      decide (b.leaf.cutAll.nodes ≤ 511)
  | none => false

/-- **The fragment of the decision with blocks over arrays.** -/
def _root_.Solidity.Fml.arrayBlockCovered (φ : Fml C []) : Bool :=
  match leafOf? φ with
  | some ψ => ψ.arrayBlockCovered
  | none => false

/-- **The decision with blocks over arrays never refuses its fragment.** -/
theorem arrayBlockReduction?_isSome (φ : Fml C []) (h : φ.arrayBlockCovered = true) :
    (arrayBlockReduction? φ).isSome = true := by
  unfold Fml.arrayBlockCovered at h
  cases hl : leafOf? φ with
  | none => rw [hl] at h; cases h
  | some ψ =>
    rw [hl] at h
    simp only [leafOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hl
    obtain ⟨d, hd, r, hr, rfl⟩ := hl
    dsimp only [LFml.arrayBlockCovered] at h
    cases hb : arrayBlockBody? r.leaf.elim.condSimp.prenex with
    | none => rw [hb] at h; cases h
    | some b =>
      rw [hb] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hsrc, hm⟩, hcap⟩, hn⟩ := h
      obtain ⟨⟨hs⟩, -⟩ := Option.isSome_iff_exists.mp hsrc
      have hlift := LFml.liftCond_src condLiftFuel hs hm
      obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp (flattenedArithmetic?_isSome b.leaf hlift hn)
      have hnone : (b.core.gx.liftCondB condLiftFuel liftBudget).isNone = false := by
        cases hX : b.core.gx.liftCondB condLiftFuel liftBudget with
        | none => rw [hX] at hcap; cases hcap
        | some _ => rfl
      simp only [arrayBlockReduction?, hd, hr, hb, Option.bind_eq_bind, Option.bind_some, hnone,
        Bool.false_eq_true, if_false, hF]
      rfl

/-- info: 'Solidity.Decide.arrayBlockReduction?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arrayBlockReduction?_isSome

/-- info: 'Solidity.Decide.ArrayBlockReduction.valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ArrayBlockReduction.valid_iff

end Solidity.Decide
