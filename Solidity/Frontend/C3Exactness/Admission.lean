import Solidity.Frontend.C3Exactness.Trace

/-!
# Existing declaration identities and inheritance admission

`rank` is the first declaration position selected by the existing producer's
contract-name lookup. No new graph well-formedness premise is introduced:
strict edge descent is derived from `Env.basesOK` itself.
-/
namespace Solidity.Frontend.C3Exactness
open Solidity.Source

/-- Exactly the top-level contract/interface predicate used by `Env.bases`. -/
def selects (c : String) (d : Decl) : Bool :=
  d.scope == none && d.name == c && (d.kind == .contract || d.kind == .interface)

/-- Existing source-order declaration identity; undeclared names get the length. -/
def rank (E : Env) (c : String) : Nat := E.decls.findIdx (selects c)

/-- First-match lookup and the first matching declaration position agree. -/
theorem find_getIdx {α : Type} (p : α → Bool) (xs : List α) :
    xs.find? p = xs[xs.findIdx p]? := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hp : p a
    · simp only [hp, Bool.false_eq_true, not_false_eq_true, List.find?_cons_of_neg,
        ih, List.findIdx_cons, cond_false, List.getElem?_cons_succ]
    · simp only [hp, List.find?_cons_of_pos, List.findIdx_cons, cond_true,
        List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero]

/-- A selected position is always within or just past the finite declaration list. -/
theorem rank_le (E : Env) (c : String) : rank E c ≤ E.decls.length :=
  List.findIdx_le_length

/-- A position inside the list really selects the named contract or interface. -/
theorem rank_selected (E : Env) (c : String) (hi : rank E c < E.decls.length) :
    selects c E.decls[rank E c] = true := List.findIdx_getElem

/-- Selection exposes the existing name, scope and kind facts. -/
theorem selects_iff (c : String) (d : Decl) : selects c d = true ↔
    d.scope = none ∧ d.name = c ∧ (d.kind = .contract ∨ d.kind = .interface) := by
  simp only [selects, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, and_assoc]

/-- Distinct resolved contract names have distinct actual declaration positions. -/
theorem rank_injective {E : Env} {a b : String}
    (ha : rank E a < E.decls.length) (hb : rank E b < E.decls.length)
    (he : rank E a = rank E b) : a = b := by
  have hna := (selects_iff a _).mp (rank_selected E a ha)
  have hnb := (selects_iff b _).mp (rank_selected E b hb)
  have hd := congrArg (fun i => E.decls[i]?) he
  change E.decls[rank E a]? = E.decls[rank E b]? at hd
  rw [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb] at hd
  exact hna.2.1.symm.trans ((congrArg Decl.name (Option.some.inj hd)).trans hnb.2.1)

/-- A name with no selected declaration has no producer inheritance edges. -/
theorem bases_empty_of_rank_eq {E : Env} {c : String}
    (he : rank E c = E.decls.length) : E.bases c = [] := by
  have hn : E.decls.find? (selects c) = none := by
    rw [find_getIdx]
    change E.decls[rank E c]? = none
    rw [he]
    exact List.getElem?_eq_none (Nat.le_refl _)
  unfold Env.bases
  change (match E.decls.find? (selects c) with
    | some ⟨.contract, _, _, _, .contract _ _ _ bs _⟩ => Env.bases.names bs
    | some ⟨.interface, _, _, _, .interface _ bs _⟩ => Env.bases.names bs
    | _ => []) = []
  rw [hn]

/-- Having any inheritance edge implies that the source contract is declared. -/
theorem rank_lt_of_base {E : Env} {c b : String} (hb : b ∈ E.bases c) :
    rank E c < E.decls.length := by
  have hle := rank_le E c
  by_cases hi : rank E c < E.decls.length
  · exact hi
  · have he : rank E c = E.decls.length := by omega
    rw [bases_empty_of_rank_eq he] at hb
    cases hb

/-- Any matching declaration occurs no earlier than the selected identity. -/
theorem rank_le_index {E : Env} {c : String} {i : Nat} {d : Decl}
    (hi : E.decls[i]? = some d) (hd : selects c d = true) : rank E c ≤ i := by
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hi
  by_cases hr : i < rank E c
  · have hf : selects c E.decls[i] = false := List.not_of_lt_findIdx hr
    rw [he, hd] at hf
    cases hf
  · omega

/-- Existing admission makes every inheritance edge descend in declaration identity. -/
theorem base_rank_lt {E : Env} (ha : E.basesOK = true) {c b : String}
    (hb : b ∈ E.bases c) : rank E b < rank E c := by
  have hc : rank E c < E.decls.length := rank_lt_of_base hb
  let d := E.decls[rank E c]
  have hd : selects c d = true := rank_selected E c hc
  have hs := (selects_iff c d).mp hd
  have hk : (d.kind == .contract || d.kind == .interface) = true := by
    simp only [Bool.or_eq_true, beq_iff_eq]
    exact hs.2.2
  have hz : (d, rank E c) ∈ E.decls.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hc)
  have hw := (List.all_eq_true.mp ha) (d, rank E c) hz
  change (!(d.kind == .contract || d.kind == .interface) ||
    (E.bases d.name).all fun b => ((E.decls.zipIdx).take (rank E c)).any fun di =>
      di.1.scope == none && di.1.name == b &&
        (di.1.kind == .interface || (d.kind == .contract && di.1.kind == .contract))) = true at hw
  rw [hk, Bool.not_true, Bool.false_or, hs.2.1] at hw
  obtain ⟨⟨d', j⟩, hm, hp⟩ := List.any_eq_true.mp ((List.all_eq_true.mp hw) b hb)
  have hj : j < rank E c := by
    obtain ⟨k, hkm, he⟩ := List.mem_take_iff_getElem.mp hm
    have he' := congrArg Prod.snd he
    simp only [List.getElem_zipIdx, Nat.zero_add] at he'
    omega
  have hg : E.decls[j]? = some d' :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_mem_take hm)
  have hp' : selects b d' = true := by
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
    apply (selects_iff b d').mpr
    refine ⟨hp.1.1, hp.1.2, ?_⟩
    rcases hp.2 with hi | ⟨_, hc'⟩
    · exact Or.inr hi
    · exact Or.inl hc'
  exact Nat.lt_of_le_of_lt (rank_le_index hg hp') hj

/-- Selected contract names are actual members of the finite declaration-name list. -/
theorem rank_name_mem {E : Env} {c : String} (hc : rank E c < E.decls.length) :
    c ∈ E.decls.map Decl.name := by
  have hn := (selects_iff c _).mp (rank_selected E c hc)
  exact List.mem_map.mpr ⟨_, List.getElem_mem hc, hn.2.1⟩

/-- The selected position is an existing declaration identity in `Syn.graph`. -/
theorem rank_graph (u : Syn .unit) (c : String) (hc : rank u.env c < u.decls.length) :
    ∃ d, (rank u.env c, d) ∈ u.graph ∧ selects c d = true := by
  refine ⟨u.decls[rank u.env c], ?_, rank_selected u.env c hc⟩
  exact List.mem_map.mpr ⟨(_, rank u.env c),
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hc), rfl⟩

/-- Duplicate-free membership bounds length even if the containing list repeats names. -/
theorem nodup_subset_length {α : Type} [DecidableEq α] {xs ys : List α}
    (hn : xs.Nodup) (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp only [List.length_nil]; omega
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    have hay : a ∈ ys := hs (List.mem_cons_self)
    have hsub : xs ⊆ ys.erase a := by
      intro x hx
      apply (List.mem_erase_of_ne (fun he : x = a => ha (he ▸ hx))).mpr
      exact hs (List.mem_cons_of_mem a hx)
    have hlen : xs.length ≤ (ys.erase a).length := ih ht hsub
    have he : (ys.erase a).length = ys.length - 1 := List.length_erase_of_mem hay
    have hpos : 0 < ys.length := List.length_pos_iff_exists_mem.mpr ⟨a, hay⟩
    simp only [List.length_cons]
    omega

/-- The producer's merge fuel is larger than the number of declarations. -/
theorem public_merge_fuel (E : Env) : E.decls.length < E.decls.length * E.decls.length + 2 := by
  have hm : E.decls.length ≤ E.decls.length * E.decls.length := Nat.le_mul_self _
  omega

end Solidity.Frontend.C3Exactness
