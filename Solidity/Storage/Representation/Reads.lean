import Solidity.Storage.Representation.Model
import Solidity.Storage.HashedSeparation

/-! Source reads from represented scalar, mapping and array values.
The symbolic read laws use no hash premise. Physical transport must later
restrict observations to a covered finite touched set. -/
namespace Solidity.Storage.Representation

/-- One symbolic full-word write. -/
def write (w : Store) (l : Loc) (v : Semantics.Word) : Store :=
  fun x => if x = l then v else w x

theorem write_same (w : Store) (l : Loc) (v : Semantics.Word) : write w l v l = v :=
  if_pos rfl

theorem write_other (w : Store) (l x : Loc) (v : Semantics.Word) (hne : x ≠ l) :
    write w l v x = w x := if_neg hne

/-- A scalar source save and a symbolic word write have matching results. -/
theorem scalar_save {p : PrimTy} (old new : p.Denote) (l : Loc) (w : Store) :
    (SVal.prim old).save .nil (.prim new) = some (.prim new) ∧
      ValueRep (.prim new) .word l (write w l (PrimTy.toWord new)) :=
  ⟨rfl, .scalar new l _ (write_same _ _ _)⟩

/-- A disjoint scalar observation survives a word write. -/
theorem scalar_frame {p : PrimTy} {v : p.Denote} {l x : Loc} {w : Store}
    (h : ValueRep (.prim v) .word l w) (hne : l ≠ x) (new : Semantics.Word) :
    ValueRep (.prim v) .word l (write w x new) :=
  .scalar v l _ ((write_other _ _ _ _ hne).trans (scalar_read h))

/-- A represented element's exact address, for arbitrary finite index. -/
theorem ElementsRep.get {E : Ty} {vs : List (SVal E)} {t : STy} {l : Loc} {w : Store}
    (h : ElementsRep vs t l w) : ∀ {i : Nat} {v : SVal E},
      vs[i]? = some v → ValueRep v t (l.add (i * t.size)) w := by
  induction vs generalizing l with
  | nil => intro i v hi; simp only [List.getElem?_nil] at hi; cases hi
  | cons head rest ih =>
    cases h with
    | cons _ _ _ _ _ hh ht =>
      intro i v hi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst v
        simpa only [Nat.zero_mul, Loc.add_zero] using hh
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        have hr : ValueRep v t ((l.add t.size).add (i * t.size)) w := ih ht hi
        rw [Loc.add_add] at hr
        simpa only [Nat.succ_mul, Nat.add_comm] using hr

/-- A fixed-array read uses the source's bounds/failure semantics. -/
theorem fixed_read {E : Ty} {n : Nat} {vs : SVec E n} {t : STy} {l : Loc} {w : Store}
    (h : ValueRep (.fixed vs) (.sarr t n) l w) {i : PrimTy.uint.Denote} {v : SVal E}
    (hi : vs.toList[i.val.toNat]? = some v) :
    (SVal.fixed vs).find (.atF i .nil) = some v ∧
      ValueRep v t (l.add (i.val.toNat * t.size)) w := by
  constructor
  · rw [SVal.find_atF, hi]
    exact SVal.find_nil v
  · cases h with
    | fixed _ _ _ _ _ elements => exact elements.get hi

/-- Dynamic-array reads include retained slots, as the existing `find` does. -/
theorem array_read {E : Ty} {n : Nat} {vs : SVec E n} {sh : SList E}
    {hn : n < 2 ^ 256} {t : STy} {l : Loc} {w : Store}
    (h : ValueRep (.array vs sh hn) (.darr t) l w)
    {i : PrimTy.uint.Denote} {v : SVal E}
    (hi : (vs.toList ++ sh.toList)[i.val.toNat]? = some v) :
    (SVal.array vs sh hn).find (.at i .nil) = some v ∧
      ValueRep v t (.data l (i.val.toNat * t.size)) w := by
  constructor
  · rw [SVal.find_at, hi]
    exact SVal.find_nil v
  · cases h with
    | array _ _ _ _ _ _ _ _ _ _ elements =>
      simpa only [Loc.add, Nat.zero_add] using elements.get hi

theorem array_header {E : Ty} {n : Nat} {vs : SVec E n} {sh : SList E}
    {hn : n < 2 ^ 256} {t : STy} {l : Loc} {w : Store}
    (h : ValueRep (.array vs sh hn) (.darr t) l w) : (w l).val = n := by
  cases h with
  | array _ _ _ _ _ _ _ _ _ header _ => exact header

/-- Mapping lookup and its default are the existing typed source operation. -/
theorem mapping_read {K : PrimTy} {V : Ty} {entries : SMap K V} {d : SVal V}
    {t : STy} {l : Loc} {w : Store}
    (h : ValueRep (.map entries d) (.map t) l w) (k : K.Denote) :
    ∃ v : SVal V, (SVal.map entries d).find (.key k .nil) = some v ∧
      ValueRep v t (.hash (PrimTy.toWord k).val.toNat l 0) w := by
  cases h with
  | mapping _ _ _ _ _ _ values =>
    refine ⟨_, ?_, values k⟩
    rw [SVal.find_key]
    cases Semantics.lookupBy k entries.toList <;>
      simp only [ Option.getD_none, Option.getD_some, SVal.find_nil]

/-- Missing array slots fail in the source, regardless of physical store contents. -/
theorem fixed_missing {E : Ty} {n : Nat} (vs : SVec E n) (i : PrimTy.uint.Denote)
    (hi : n ≤ i.val.toNat) : (SVal.fixed vs).find (.atF i .nil) = none := by
  rw [SVal.find_atF, List.getElem?_eq_none (by rw [SVec.length_toList]; exact hi)]

theorem array_missing {E : Ty} {n : Nat} (vs : SVec E n) (sh : SList E)
    (hn : n < 2 ^ 256) (i : PrimTy.uint.Denote)
    (hi : (vs.toList ++ sh.toList).length ≤ i.val.toNat) :
    (SVal.array vs sh hn).find (.at i .nil) = none := by
  rw [SVal.find_at, List.getElem?_eq_none hi]

/-- Reuse the committed source frame law at arbitrary typed paths. -/
theorem source_frame {T U V : Ty} {start changed : SVal T} {new : SVal U}
    {p : Path T U} {q : Path T V} (saved : start.save p new = some changed)
    (apart : Path.Diverges p q) : changed.find q = start.find q := by
  rw [SVal.find_eq_findM, SVal.find_eq_findM]
  exact SVal.findM_saveM_diverges apart start new (by
    rwa [← SVal.save_eq_saveM])

end Solidity.Storage.Representation
