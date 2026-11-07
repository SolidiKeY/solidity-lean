import Solidity.Frontend.QualifiedUnits.SignatureMembers

/-! Independent deterministic C3 merge judgment on original declaration identities.
The judgment mentions head/tail membership and deletion, never mergeOwners or
its fuel. The public equivalence accounts for the exact output-length budget;
the hierarchy-specific idUniverse bound is proved sufficient in
`Linearization.order_iff`. -/
namespace Solidity.Frontend.QualifiedUnits.MergeSpecification
open Solidity.Source

def Available (rows : List (List DeclId)) (head : DeclId) : Prop :=
  ∀ row, row ∈ rows → head ∉ row.drop 1

/-- First eligible head, with every preceding row independently blocked. -/
inductive First (rows : List (List DeclId)) : List (List DeclId) → DeclId → Prop where
  | take {head : DeclId} {tail : List DeclId} {rest : List (List DeclId)} :
      Available rows head → First rows ((head :: tail) :: rest) head
  | skip {row : List DeclId} {rest : List (List DeclId)} {head : DeclId} :
      (∀ candidate, row.head? = some candidate → ¬ Available rows candidate) →
      First rows rest head → First rows (row :: rest) head

def nonempty (rows : List (List DeclId)) : List (List DeclId) := rows.filter (· ≠ [])
def remove (head : DeclId) (rows : List (List DeclId)) : List (List DeclId) :=
  rows.map fun row => row.filter (· ≠ head)

inductive Merge : List (List DeclId) → List DeclId → Prop where
  | empty {rows : List (List DeclId)} : nonempty rows = [] → Merge rows []
  | step {rows : List (List DeclId)} {head : DeclId} {tail : List DeclId} :
      First (nonempty rows) (nonempty rows) head →
      Merge (remove head (nonempty rows)) tail → Merge rows (head :: tail)

theorem available_iff {rows : List (List DeclId)} {head : DeclId} :
    (rows.all fun row => !(row.drop 1).contains head) = true ↔ Available rows head := by
  simp only [List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, Available]

theorem first_iff {rows scan : List (List DeclId)} {head : DeclId} :
    scan.findSome? (fun row => row.head?.filter fun h => rows.all fun other => !(other.drop 1).contains h) = some head ↔
      First rows scan head := by
  induction scan with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons row rest ih =>
    cases row with
    | nil =>
      simp only [List.findSome?_cons, List.head?_nil, Option.filter_none]
      constructor
      · intro h; exact .skip (by intro candidate h; cases h) (ih.mp h)
      · intro h; cases h with | skip _ hs => exact ih.mpr hs
    | cons candidate tail =>
      by_cases ha : Available rows candidate
      · have hb := available_iff.mpr ha
        simp only [List.findSome?_cons, List.head?_cons, Option.filter_some, hb, ↓reduceIte]
        constructor
        · intro h; cases h; exact .take ha
        · intro h
          cases h with
          | take _ => rfl
          | skip blocked _ => exact False.elim (blocked candidate rfl ha)
      · have hb : (rows.all fun other => !(other.drop 1).contains candidate) = false :=
          Bool.eq_false_iff.mpr (fun h => ha (available_iff.mp h))
        simp only [List.findSome?_cons, List.head?_cons, Option.filter_some, hb, Bool.false_eq_true, ↓reduceIte]
        constructor
        · intro h
          exact .skip (by intro j hj; cases hj; exact ha) (ih.mp h)
        · intro h
          cases h with
          | take ht => exact False.elim (ha ht)
          | skip _ hs => exact ih.mpr hs

theorem first_nonempty {rows scan : List (List DeclId)} {head : DeclId}
    (h : First rows scan head) : scan ≠ [] := by
  cases h <;> intro equal <;> cases equal

/-- Soundness, including the exact positive fuel needed for the empty result. -/
theorem merge_sound {fuel : Nat} {rows : List (List DeclId)} {out : List DeclId}
    (h : SignatureMembers.mergeOwners fuel rows = some out) : Merge rows out ∧ out.length < fuel := by
  induction fuel generalizing rows out with
  | zero => cases h
  | succ fuel ih =>
    unfold SignatureMembers.mergeOwners at h
    dsimp only at h
    split at h
    · rename_i he
      have hn : nonempty rows = [] := List.isEmpty_iff.mp he
      cases Option.some.inj h
      exact ⟨.empty hn, Nat.zero_lt_succ _⟩
    · split at h
      · cases h
      · rename_i head hh
        rcases Option.map_eq_some_iff.mp h with ⟨tail,ht,he⟩
        cases he
        obtain ⟨hm,hf⟩ := ih ht
        exact ⟨.step (first_iff.mp hh) hm, Nat.succ_lt_succ hf⟩

theorem merge_complete {rows : List (List DeclId)} {out : List DeclId}
    (h : Merge rows out) : ∀ fuel, out.length < fuel → SignatureMembers.mergeOwners fuel rows = some out := by
  induction h with
  | empty hn =>
    intro fuel hf
    cases fuel with
    | zero => cases Nat.not_lt_zero _ hf
    | succ fuel =>
      simp only [SignatureMembers.mergeOwners, nonempty] at hn ⊢
      rw [hn]; rfl
  | @step rows head tail hh hm ih =>
    intro fuel hf
    cases fuel with
    | zero => cases Nat.not_lt_zero _ hf
    | succ fuel =>
      have hn : (nonempty rows).isEmpty = false :=
        List.isEmpty_eq_false_iff.mpr (first_nonempty hh)
      have ht := ih fuel (Nat.lt_of_succ_lt_succ hf)
      change SignatureMembers.mergeOwners (fuel + 1) rows = some (head :: tail)
      simp only [SignatureMembers.mergeOwners]
      change (if (nonempty rows).isEmpty = true then _ else _) = _
      rw [hn]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hc := first_iff.mpr hh
      change (match (nonempty rows).findSome? (fun row => row.head?.filter fun h => (nonempty rows).all fun other => !(other.drop 1).contains h) with
        | none => none
        | some h => (SignatureMembers.mergeOwners fuel (remove h (nonempty rows))).map (h :: ·)) = _
      rw [hc]
      change (SignatureMembers.mergeOwners fuel (remove head (nonempty rows))).map (head :: ·) = _
      rw [ht]; rfl

/-- Unconditional correspondence with a fuel-free judgment, not a supplied run. -/
theorem merge_iff {fuel : Nat} {rows : List (List DeclId)} {out : List DeclId} :
    SignatureMembers.mergeOwners fuel rows = some out ↔ Merge rows out ∧ out.length < fuel :=
  ⟨merge_sound, fun ⟨h,hf⟩ => merge_complete h fuel hf⟩

theorem First.member {rows scan : List (List DeclId)} {head : DeclId}
    (h : First rows scan head) : ∃ row, row ∈ scan ∧ head ∈ row := by
  induction h with
  | take _ => exact ⟨_, List.mem_cons_self, List.mem_cons_self⟩
  | skip _ _ ih =>
    obtain ⟨row,hr,hm⟩ := ih
    exact ⟨row,List.mem_cons_of_mem _ hr,hm⟩

theorem mem_remove {head j : DeclId} {rows : List (List DeclId)} :
    (∃ row, row ∈ remove head rows ∧ j ∈ row) ↔
      j ≠ head ∧ ∃ row, row ∈ rows ∧ j ∈ row := by
  constructor
  · rintro ⟨row,hr,hj⟩
    obtain ⟨original,ho,he⟩ := List.mem_map.mp hr
    subst row
    obtain ⟨hm,hne⟩ := List.mem_filter.mp hj
    exact ⟨of_decide_eq_true hne,original,ho,hm⟩
  · rintro ⟨hne,row,hr,hj⟩
    exact ⟨row.filter (· ≠ head),List.mem_map.mpr ⟨row,hr,rfl⟩,
      List.mem_filter.mpr ⟨hj,decide_eq_true hne⟩⟩

theorem mem_nonempty {j : DeclId} {rows : List (List DeclId)} :
    (∃ row, row ∈ nonempty rows ∧ j ∈ row) ↔ ∃ row, row ∈ rows ∧ j ∈ row := by
  constructor
  · rintro ⟨row,hr,hj⟩
    exact ⟨row,(List.mem_filter.mp hr).1,hj⟩
  · rintro ⟨row,hr,hj⟩
    have hn : row ≠ [] := by intro he; subst row; cases hj
    exact ⟨row,List.mem_filter.mpr ⟨hr,decide_eq_true hn⟩,hj⟩

/-- Successful merges contain every input identity, including diamond duplicates,
and no identity that was absent from all input rows. -/
theorem Merge.members {rows : List (List DeclId)} {out : List DeclId}
    (h : Merge rows out) (j : DeclId) : j ∈ out ↔ ∃ row, row ∈ rows ∧ j ∈ row := by
  induction h with
  | empty hn =>
    constructor
    · intro h; cases h
    · intro hm
      obtain ⟨row,hr,_⟩ := mem_nonempty.mpr hm
      rw [hn] at hr; cases hr
  | @step rows head tail hh hm ih =>
    rw [List.mem_cons, ih, mem_remove, mem_nonempty]
    constructor
    · intro h
      rcases h with he | ⟨_,hj⟩
      · subst j; exact mem_nonempty.mp hh.member
      · exact hj
    · intro h
      by_cases he : j = head
      · exact Or.inl he
      · exact Or.inr ⟨he,h⟩

/-- Repeated routes to the same declaration coalesce, rather than clash. -/
theorem Merge.nodup {rows : List (List DeclId)} {out : List DeclId}
    (h : Merge rows out) : out.Nodup := by
  induction h with
  | empty _ => exact List.nodup_nil
  | @step rows head tail hh hm ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro hj
      have hn := (mem_remove.mp ((hm.members head).mp hj)).1
      exact hn rfl
    · exact ih

/-- Increasing fuel cannot change a successful result. -/
theorem merge_monotone {fuel more : Nat} {rows : List (List DeclId)} {out : List DeclId}
    (h : SignatureMembers.mergeOwners fuel rows = some out) (hf : fuel ≤ more) :
    SignatureMembers.mergeOwners more rows = some out := by
  obtain ⟨hm,hlen⟩ := merge_sound h
  exact merge_complete hm more (Nat.lt_of_lt_of_le hlen hf)

/-- The fuel-free first-head judgment has a unique output. -/
theorem Merge.unique {rows : List (List DeclId)} {first second : List DeclId}
    (ha : Merge rows first) (hb : Merge rows second) : first = second := by
  have hf : first.length < first.length + second.length + 1 := by omega
  have hs : second.length < first.length + second.length + 1 := by omega
  exact Option.some.inj ((merge_complete ha _ hf).symm.trans (merge_complete hb _ hs))

/-- Original identities in controls differ by both unit and source position. -/
def a : DeclId := ⟨"A.sol",0⟩
def b : DeclId := ⟨"B.sol",0⟩
def c : DeclId := ⟨"B.sol",1⟩

theorem diamond_result : SignatureMembers.mergeOwners 4 [[b,a],[c,a],[b,c]] = some [b,c,a] := rfl

theorem diamond_judgment : Merge [[b,a],[c,a],[b,c]] [b,c,a] :=
  (merge_iff.mp diamond_result).1

theorem duplicate_route_identity : SignatureMembers.mergeOwners 2 [[a],[a]] = some [a] := rfl

theorem blocked_first_head : SignatureMembers.mergeOwners 3 [[a],[b,a]] = some [b,a] := rfl

theorem inconsistent_order_refused : SignatureMembers.mergeOwners 8 [[a,b],[b,a]] = none := rfl

theorem inconsistent_judgment_absent : ¬ ∃ out, Merge [[a,b],[b,a]] out := by
  rintro ⟨out,h⟩
  cases h with
  | empty he => cases he
  | step hf _ =>
    have ha : ¬ Available [[a,b],[b,a]] a := by
      intro hav
      exact hav [b,a] (by decide) (by decide)
    have hb : ¬ Available [[a,b],[b,a]] b := by
      intro hav
      exact hav [a,b] (by decide) (by decide)
    change First [[a,b],[b,a]] [[a,b],[b,a]] _ at hf
    cases hf with
    | take hav => exact ha hav
    | skip _ hs =>
      cases hs with
      | take hav => exact hb hav
      | skip _ hs => cases hs

theorem exact_budget_refused : SignatureMembers.mergeOwners 3 [[b,a],[c,a],[b,c]] = none := rfl

theorem zero_fuel_refused : SignatureMembers.mergeOwners 0 [] = none := rfl

theorem empty_rows_accepted : SignatureMembers.mergeOwners 1 [[],[]] = some [] := rfl

end Solidity.Frontend.QualifiedUnits.MergeSpecification
