import Solidity.Frontend.QualifiedUnits.MergeSpecification

/-! Independent C3 hierarchy judgment on original declaration identities.

`Linear P R owner out` is an inductive, fuel-free statement: every written
base path of a container resolves through the qualified unit-route relation,
every base has its own linearization and `out` is the owner followed by the
independent `MergeSpecification.Merge` of those linearizations and the local
base list. It never mentions `SignatureMembers.linearize`, `mergeOwners`,
`bases` or a numeric bound. It shares only the syntactic base-path
extractor `basePaths` with the executable `bases`.

`order_iff` proves that the executable `SignatureMembers.order` (its
`idUniverse` depth and `bound * bound + 2` merge budgets) is sound and complete
for this judgment, with no premise: a hierarchy exists exactly when `order`
succeeds, and the bound never refuses one. Precedence is the C3 monotonicity
property: every base linearization and the reversed local base list are
sublists of the result. Cyclic hierarchies have no derivation. Agreement with
solc's exact order rests on the deterministic first-head rule and pinned
fixtures, not on a compiler differential of `Linear` itself. This is not
inheritance/override legality (G14) and makes no claim about solc beyond the
pinned fixtures. -/
namespace Solidity.Frontend.QualifiedUnits.Linearization
open Solidity.Source MergeSpecification

/-- Ordered written base targets; one qualified unit route per written path. -/
inductive Routes (P : UnitSet) (R : List Remapping) (u : String) : List IdPath → List DeclId → Prop where
  | nil : Routes P R u [] []
  | cons {p : IdPath} {ps : List IdPath} {b : DeclId} {bs : List DeclId} :
      UnitRoute P R (Sees P R u p.head) p.tail b → Routes P R u ps bs → Routes P R u (p :: ps) (b :: bs)

/-- The written bases of an original container declaration, in source order. -/
def Bases (P : UnitSet) (R : List Remapping) (owner : DeclId) (bs : List DeclId) : Prop :=
  ∃ d, P.decl? owner = some d ∧ Container d.kind ∧ Routes P R owner.unit (basePaths d) bs

/-- Independent C3 linearization: each pair is a base with its own derivation. -/
inductive Linear (P : UnitSet) (R : List Remapping) : DeclId → List DeclId → Prop where
  | mk {owner : DeclId} {bs : List DeclId} {pairs : List (DeclId × List DeclId)} {out : List DeclId} :
      Bases P R owner bs → pairs.map Prod.fst = bs.reverse →
      (∀ pair, pair ∈ pairs → Linear P R pair.1 pair.2) →
      Merge (pairs.map Prod.snd ++ [bs.reverse]) out → Linear P R owner (owner :: out)

theorem routes_iff {P : UnitSet} {R : List Remapping} {u : String} {ps : List IdPath} {bs : List DeclId} :
    ps.mapM (unitBase P R u) = some bs ↔ Routes P R u ps bs := by
  induction ps generalizing bs with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq]
    constructor
    · intro h; subst bs; exact .nil
    · intro h; cases h; rfl
  | cons p ps ih =>
    simp only [List.mapM_cons, bind, pure]
    constructor
    · intro h
      cases hp : unitBase P R u p with
      | none => rw [hp] at h; cases h
      | some b =>
        rw [hp] at h
        cases hs : ps.mapM (unitBase P R u) with
        | none => simp only [Option.bind_some, hs, Option.bind_none] at h; cases h
        | some rest =>
          simp only [Option.bind_some, hs, Option.some.injEq] at h
          subst bs
          exact .cons (unitBase_iff.mp hp) (ih.mp hs)
    · intro h
      cases h with
      | cons hb hr =>
        rw [unitBase_iff.mpr hb, ih.mpr hr]
        rfl

theorem bases_iff {P : UnitSet} {R : List Remapping} {owner : DeclId} {bs : List DeclId} :
    SignatureMembers.bases P R owner = some bs ↔ Bases P R owner bs := by
  unfold SignatureMembers.bases Bases
  cases hd : P.decl? owner with
  | none =>
    constructor
    · intro h; cases h
    · rintro ⟨d,he,_⟩; cases he
  | some d =>
    by_cases hc : Container d.kind
    · simp only [hc, if_true, routes_iff, Option.some.injEq]
      constructor
      · intro h; exact ⟨d,rfl,hc,h⟩
      · rintro ⟨e,he,_,hr⟩; cases he; exact hr
    · simp only [hc, if_false, Option.some.injEq]
      constructor
      · intro h; cases h
      · rintro ⟨e,he,hk,_⟩; cases he; exact False.elim (hc hk)

theorem mapM_pairs {f : DeclId → Option (List DeclId)} {xs : List DeclId} {ys : List (List DeclId)}
    (h : xs.mapM f = some ys) :
    ∃ pairs : List (DeclId × List DeclId), pairs.map Prod.fst = xs ∧ pairs.map Prod.snd = ys ∧
      ∀ pair, pair ∈ pairs → f pair.1 = some pair.2 := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst ys
    exact ⟨[],rfl,rfl,fun _ hp => nomatch hp⟩
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure] at h
    cases hx : f x with
    | none => rw [hx] at h; cases h
    | some y =>
      rw [hx] at h
      cases hs : xs.mapM f with
      | none => simp only [Option.bind_some, hs, Option.bind_none] at h; cases h
      | some rest =>
        simp only [Option.bind_some, hs, Option.some.injEq] at h
        subst ys
        obtain ⟨pairs,hf,hsnd,hp⟩ := ih hs
        refine ⟨(x,y) :: pairs, by simp only [List.map_cons, hf], by simp only [List.map_cons, hsnd], ?_⟩
        intro pair hm
        rcases List.mem_cons.mp hm with he | hm
        · subst pair; exact hx
        · exact hp pair hm

theorem pairs_mapM {f : DeclId → Option (List DeclId)} {pairs : List (DeclId × List DeclId)}
    (h : ∀ pair, pair ∈ pairs → f pair.1 = some pair.2) :
    (pairs.map Prod.fst).mapM f = some (pairs.map Prod.snd) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    simp only [List.map_cons, List.mapM_cons, bind, pure]
    rw [h pair List.mem_cons_self, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    rfl

/-- Soundness of every bounded executable run, at any fuel and bound. -/
theorem linearize_sound {P : UnitSet} {R : List Remapping} {bound fuel : Nat} {owner : DeclId}
    {out : List DeclId} (h : SignatureMembers.linearize P R bound fuel owner = some out) :
    Linear P R owner out := by
  induction fuel generalizing owner out with
  | zero => cases h
  | succ fuel ih =>
    unfold SignatureMembers.linearize at h
    cases hb : SignatureMembers.bases P R owner with
    | none => rw [hb] at h; cases h
    | some bs =>
      simp only [hb, Option.bind_some] at h
      split at h
      · cases h
      · rename_i lists hl
        obtain ⟨merged,hm,he⟩ := Option.map_eq_some_iff.mp h
        subst out
        obtain ⟨pairs,hf,hs,hp⟩ := mapM_pairs hl
        have hmerge := (merge_iff.mp hm).1
        rw [← hs] at hmerge
        exact .mk (bases_iff.mp hb) hf (fun pair hpair => ih (hp pair hpair)) hmerge

theorem Linear.head {P : UnitSet} {R : List Remapping} {owner : DeclId} {out : List DeclId}
    (h : Linear P R owner out) : owner ∈ out := by
  cases h; exact List.mem_cons_self

theorem routes_unique {P : UnitSet} {R : List Remapping} {u : String} {ps : List IdPath}
    {bs cs : List DeclId} (hb : Routes P R u ps bs) (hc : Routes P R u ps cs) : bs = cs := by
  have eb := routes_iff.mpr hb
  have ec := routes_iff.mpr hc
  exact Option.some.inj (eb.symm.trans ec)

theorem bases_unique {P : UnitSet} {R : List Remapping} {owner : DeclId} {bs cs : List DeclId}
    (hb : Bases P R owner bs) (hc : Bases P R owner cs) : bs = cs :=
  Option.some.inj ((bases_iff.mpr hb).symm.trans (bases_iff.mpr hc))

theorem pairs_snd_unique {P : UnitSet} {R : List Remapping} :
    ∀ {first second : List (DeclId × List DeclId)},
      first.map Prod.fst = second.map Prod.fst →
      (∀ pair, pair ∈ first → ∀ other, Linear P R pair.1 other → pair.2 = other) →
      (∀ pair, pair ∈ second → Linear P R pair.1 pair.2) →
      first.map Prod.snd = second.map Prod.snd
  | [], [], _, _, _ => rfl
  | [], _ :: _, he, _, _ => by cases he
  | _ :: _, [], he, _, _ => by cases he
  | p :: ps, q :: qs, he, hu, hl => by
    simp only [List.map_cons, List.cons.injEq] at he ⊢
    refine ⟨?_, pairs_snd_unique he.2 (fun pair hm => hu pair (List.mem_cons_of_mem _ hm))
      (fun pair hm => hl pair (List.mem_cons_of_mem _ hm))⟩
    apply hu p List.mem_cons_self
    rw [he.1]
    exact hl q List.mem_cons_self

/-- The judgment is functional: a hierarchy has one linearization. -/
theorem Linear.unique {P : UnitSet} {R : List Remapping} {owner : DeclId} {first second : List DeclId}
    (ha : Linear P R owner first) (hb : Linear P R owner second) : first = second := by
  induction ha generalizing second with
  | @mk owner bs pairs out hbases hfst _ hmerge ih =>
    cases hb with
    | @mk _ cs others out' hbases' hfst' hlin' hmerge' =>
      cases bases_unique hbases hbases'
      have hs := pairs_snd_unique (hfst.trans hfst'.symm) ih hlin'
      rw [hs] at hmerge
      rw [Merge.unique hmerge hmerge']

private theorem length_le_of_nodup_subset :
    ∀ {M L : List DeclId}, M.Nodup → (∀ x, x ∈ M → x ∈ L) → M.length ≤ L.length
  | [], _, _, _ => Nat.zero_le _
  | a :: M, L, hM, h => by
    have ha : a ∈ L := h a List.mem_cons_self
    have hM' : M.Nodup := (List.nodup_cons.mp hM).2
    have hsub : ∀ x, x ∈ M → x ∈ L.erase a := fun x hx =>
      (List.mem_erase_of_ne fun e => (List.nodup_cons.mp hM).1 (by rw [← e]; exact hx)).mpr
        (h x (List.mem_cons_of_mem a hx))
    have hle : M.length ≤ (L.erase a).length := length_le_of_nodup_subset hM' hsub
    have hlen : (L.erase a).length = L.length - 1 := List.length_erase_of_mem ha
    have hpos : 0 < L.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- A merged identity lies in some base linearization (local bases are heads). -/
theorem merged_in_base {P : UnitSet} {R : List Remapping} {bs : List DeclId}
    {pairs : List (DeclId × List DeclId)} {out : List DeclId} {x : DeclId}
    (hfst : pairs.map Prod.fst = bs.reverse) (hlin : ∀ pair, pair ∈ pairs → Linear P R pair.1 pair.2)
    (hmerge : Merge (pairs.map Prod.snd ++ [bs.reverse]) out) (hx : x ∈ out) :
    ∃ pair, pair ∈ pairs ∧ x ∈ pair.2 := by
  obtain ⟨row,hr,hxr⟩ := (hmerge.members x).mp hx
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨pair,hp,he⟩ := List.mem_map.mp hr
    subst row
    exact ⟨pair,hp,hxr⟩
  · have hrow : row = bs.reverse := List.mem_singleton.mp hr
    subst row
    rw [← hfst] at hxr
    obtain ⟨pair,hp,he⟩ := List.mem_map.mp hxr
    subst x
    exact ⟨pair,hp,(hlin pair hp).head⟩

/-- Every base linearization is contained in the merged output. -/
theorem base_in_merged {bs : List DeclId} {pairs : List (DeclId × List DeclId)} {out : List DeclId}
    (hmerge : Merge (pairs.map Prod.snd ++ [bs.reverse]) out) {pair : DeclId × List DeclId}
    (hp : pair ∈ pairs) : ∀ x, x ∈ pair.2 → x ∈ out := fun x hx =>
  (hmerge.members x).mpr ⟨pair.2, List.mem_append_left _ (List.mem_map.mpr ⟨pair,hp,rfl⟩), hx⟩

/-- Every linearization is duplicate-free, and no member's own linearization
is longer: the owner cannot recur below itself, so cycles have no derivation. -/
theorem Linear.bounded {P : UnitSet} {R : List Remapping} {owner : DeclId} {out : List DeclId}
    (h : Linear P R owner out) :
    out.Nodup ∧ ∀ x, x ∈ out → ∀ other, Linear P R x other → other.length ≤ out.length := by
  induction h with
  | @mk owner bs pairs merged hbases hfst hlin hmerge ih =>
    have self : Linear P R owner (owner :: merged) := .mk hbases hfst hlin hmerge
    have below : ∀ x, x ∈ merged → ∀ other, Linear P R x other → other.length ≤ merged.length := by
      intro x hx other ho
      obtain ⟨pair,hp,hxp⟩ := merged_in_base hfst hlin hmerge hx
      have h1 := (ih pair hp).2 x hxp other ho
      have h2 := length_le_of_nodup_subset (ih pair hp).1 (base_in_merged hmerge hp)
      exact Nat.le_trans h1 h2
    have fresh : owner ∉ merged := by
      intro hm
      have := below owner hm _ self
      simp only [List.length_cons] at this
      omega
    refine ⟨List.nodup_cons.mpr ⟨fresh,hmerge.nodup⟩, ?_⟩
    intro x hx other ho
    rcases List.mem_cons.mp hx with he | hx
    · subst x
      rw [Linear.unique ho self]
      exact Nat.le_refl _
    · have := below x hx other ho
      simp only [List.length_cons]
      omega

/-- Every linearized identity is the owner or an original declaration. -/
theorem Linear.members {P : UnitSet} {R : List Remapping} {owner : DeclId} {out : List DeclId}
    (h : Linear P R owner out) : ∀ x, x ∈ out → x = owner ∨ ∃ d, P.decl? x = some d := by
  induction h with
  | @mk owner bs pairs merged hbases hfst hlin hmerge ih =>
    intro x hx
    rcases List.mem_cons.mp hx with he | hx
    · exact Or.inl he
    · obtain ⟨pair,hp,hxp⟩ := merged_in_base hfst hlin hmerge hx
      rcases ih pair hp x hxp with he | hd
      · right
        obtain ⟨d,_,_,hr⟩ := hbases
        have hb : pair.1 ∈ bs := by
          have : pair.1 ∈ bs.reverse := by rw [← hfst]; exact List.mem_map.mpr ⟨pair,hp,rfl⟩
          exact List.mem_reverse.mp this
        subst x
        clear hfst hlin hmerge ih hx hxp hp
        generalize basePaths d = ps at hr
        induction hr with
        | nil => cases hb
        | cons hu _ ihr =>
          rcases List.mem_cons.mp hb with he | hb
          · subst he
            obtain ⟨d,hd,_⟩ := hu.decl_exists
            exact ⟨d,hd⟩
          · exact ihr hb
      · exact Or.inr hd

/-- Any derivation runs at fuel at least its length and a merge budget covering it. -/
theorem linearize_complete {P : UnitSet} {R : List Remapping} {owner : DeclId} {out : List DeclId}
    (h : Linear P R owner out) :
    ∀ bound fuel, out.length ≤ fuel → out.length ≤ bound + 1 →
      SignatureMembers.linearize P R bound fuel owner = some out := by
  have hbnd := h.bounded
  induction h with
  | @mk owner bs pairs merged hbases hfst hlin hmerge ih =>
    intro bound fuel hf hb
    have below : ∀ pair, pair ∈ pairs → pair.2.length ≤ merged.length := fun pair hp =>
      length_le_of_nodup_subset (hlin pair hp).bounded.1 (base_in_merged hmerge hp)
    cases fuel with
    | zero => simp only [List.length_cons] at hf; omega
    | succ fuel =>
      simp only [List.length_cons] at hf hb
      have runs : ∀ pair, pair ∈ pairs → SignatureMembers.linearize P R bound fuel pair.1 = some pair.2 :=
        fun pair hp => ih pair hp (hlin pair hp).bounded bound fuel
          (Nat.le_trans (below pair hp) (by omega)) (Nat.le_trans (below pair hp) (by omega))
      have hmapM := pairs_mapM runs
      rw [hfst] at hmapM
      have hfuel : merged.length < bound * bound + 2 := by
        have : bound ≤ bound * bound + 1 := by
          cases bound with
          | zero => omega
          | succ n => exact Nat.le_succ_of_le (Nat.le_mul_self _)
        omega
      have hm := merge_iff.mpr ⟨hmerge, hfuel⟩
      unfold SignatureMembers.linearize
      rw [bases_iff.mpr hbases, Option.bind_some]
      simp only [hmapM, hm, Option.map_some]

/-- The executable bounded order is exactly the independent hierarchy judgment:
the `idUniverse` depth and merge budgets never refuse a valid hierarchy. -/
theorem order_iff {P : UnitSet} {R : List Remapping} {root : DeclId} {out : List DeclId} :
    SignatureMembers.order P R root = some out ↔ Linear P R root out := by
  constructor
  · intro h; exact linearize_sound h
  · intro h
    have hlen : out.length ≤ (idUniverse P root).length := by
      apply length_le_of_nodup_subset h.bounded.1
      intro x hx
      rcases h.members x hx with he | ⟨d,hd⟩
      · subst x; exact List.mem_cons_self
      · exact decl_mem_universe hd
    exact linearize_complete h _ _ (by omega) (by omega)

theorem First.available {rows scan : List (List DeclId)} {head : DeclId}
    (h : First rows scan head) : Available rows head := by
  induction h with
  | take ha => exact ha
  | skip _ _ ih => exact ih

/-- C3 monotonicity: every input row of a successful merge keeps its order. -/
theorem Merge.sublist {rows : List (List DeclId)} {out : List DeclId} (h : Merge rows out) :
    ∀ row, row ∈ rows → row.Sublist out := by
  induction h with
  | @empty rows hn =>
    intro row hr
    cases row with
    | nil => exact List.Sublist.slnil
    | cons x rest =>
      have : x :: rest ∈ nonempty rows := List.mem_filter.mpr ⟨hr, by simp only [ne_eq, reduceCtorEq, not_false_eq_true, decide_true]⟩
      rw [hn] at this; cases this
  | @step rows head tail hh hm ih =>
    intro row hr
    cases row with
    | nil => exact List.nil_sublist _
    | cons x rest =>
      have hne : x :: rest ∈ nonempty rows := List.mem_filter.mpr ⟨hr, by simp only [ne_eq, reduceCtorEq, not_false_eq_true, decide_true]⟩
      have hfree : head ∉ rest := by
        exact First.available hh (x :: rest) hne
      have hsub := ih ((x :: rest).filter (· ≠ head)) (List.mem_map.mpr ⟨_, hne, rfl⟩)
      by_cases hx : x = head
      · subst x
        have hkeep : rest.filter (· ≠ head) = rest :=
          List.filter_eq_self.mpr (fun a ha => decide_eq_true (fun e => hfree (e ▸ ha)))
        simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          ↓reduceIte, hkeep] at hsub
        exact hsub.cons₂ _
      · have hkeep : (x :: rest).filter (· ≠ head) = x :: rest := by
          apply List.filter_eq_self.mpr
          intro a ha
          rcases List.mem_cons.mp ha with he | ha
          · subst a; exact decide_eq_true hx
          · exact decide_eq_true (fun e => hfree (e ▸ ha))
        rw [hkeep] at hsub
        exact hsub.cons _

/-- Hierarchy precedence: every base's linearization, and the local base list
in solc's most-derived-first order, are sublists of the owner's linearization. -/
theorem Linear.precedence {P : UnitSet} {R : List Remapping} {owner : DeclId} {out : List DeclId}
    (h : Linear P R owner out) {bs : List DeclId} (hb : Bases P R owner bs) :
    bs.reverse.Sublist out.tail ∧ ∀ b, b ∈ bs → ∀ lin, Linear P R b lin → lin.Sublist out.tail := by
  cases h with
  | @mk _ cs pairs merged hbases hfst hlin hmerge =>
    cases bases_unique hb hbases
    refine ⟨Merge.sublist hmerge _ (List.mem_append_right _ (List.mem_singleton_self _)), ?_⟩
    intro b hmem lin hl
    have hrev : b ∈ pairs.map Prod.fst := by rw [hfst]; exact List.mem_reverse.mpr hmem
    obtain ⟨pair,hp,he⟩ := List.mem_map.mp hrev
    subst b
    rw [Linear.unique hl (hlin pair hp)]
    exact Merge.sublist hmerge _ (List.mem_append_left _ (List.mem_map.mpr ⟨pair,hp,rfl⟩))

/-- Acyclicity: the owner occurs in no base's linearization. -/
theorem Linear.acyclic {P : UnitSet} {R : List Remapping} {owner : DeclId} {out : List DeclId}
    (h : Linear P R owner out) {bs : List DeclId} (hb : Bases P R owner bs) :
    ∀ b, b ∈ bs → ∀ lin, Linear P R b lin → owner ∉ lin := by
  intro b hmem lin hl ho
  have hsub := (h.precedence hb).2 b hmem lin hl
  have hnd := h.bounded.1
  cases h with
  | mk _ _ _ _ =>
    exact (List.nodup_cons.mp hnd).1 (hsub.subset ho)

end Solidity.Frontend.QualifiedUnits.Linearization
