import Solidity.Frontend.C3Exactness.Linearization
import Solidity.Frontend.C3Exactness.Renaming

/-!
# Exact C3 over existing declaration-position identities

Only positions actually selected by the existing name lookup are encoded as
graph identities. Undeclared names use a sentinel in `rank` and are deliberately
not asserted to be graph nodes. The public identity equivalence discharges this
boundary with existing resolved-root selection evidence.
-/
namespace Solidity.Frontend.C3Exactness
open Solidity.Source

/-- Read the existing name of a declaration position. -/
def nameAt (E : Env) (i : Nat) : String := ((E.decls[i]?).map Decl.name).getD ""

/-- A selected actual declaration position, excluding the undeclared sentinel. -/
def GoodId (E : Env) (i : Nat) : Prop :=
  i < E.decls.length ∧ rank E (nameAt E i) = i

/-- Decoding a selected name's actual position recovers that name. -/
theorem nameAt_rank {E : Env} {c : String} (hc : rank E c < E.decls.length) :
    nameAt E (rank E c) = c := by
  have hn := (selects_iff c _).mp (rank_selected E c hc)
  simp only [nameAt, List.getElem?_eq_getElem hc, Option.map_some, Option.getD_some, hn.2.1]

/-- Resolved names encode as selected actual graph identities. -/
theorem rank_good {E : Env} {c : String} (hc : rank E c < E.decls.length) :
    GoodId E (rank E c) := ⟨hc, by rw [nameAt_rank hc]⟩

/-- Encoding is injective on precisely the resolved input-name support. -/
theorem rank_injects (E : Env) :
    InjectsOn (fun c => rank E c < E.decls.length) (rank E) :=
  fun _ _ ha hb he => rank_injective ha hb he

/-- Decoding is injective on precisely the selected position support. -/
theorem nameAt_injects (E : Env) : InjectsOn (GoodId E) (nameAt E) := by
  intro i j hi hj he
  exact hi.2.symm.trans ((congrArg (rank E) he).trans hj.2)

/-- Every input to an admitted exact-node merge names a real earlier declaration. -/
theorem merge_input_known {E : Env} {c : String} {Ls : List (List String)}
    (ha : E.basesOK = true) (hlen : Ls.length = (E.bases c).reverse.length)
    (hchildren : ∀ (i : Nat) (b : String) (Lb : List String),
      (E.bases c).reverse[i]? = some b → Ls[i]? = some Lb → ExactLin E b Lb) :
    ∀ x ∈ (Ls ++ [(E.bases c).reverse]).flatten, rank E x < E.decls.length := by
  intro x hx
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
  rcases List.mem_append.mp hl with hls | hbs
  · obtain ⟨i, b, hb, hLb⟩ := paired_get hlen hls
    have hr := (hchildren i b l hb hLb).rank_bound ha x hxl
    have hb' := base_rank_lt ha (List.mem_reverse.mp (List.mem_of_getElem? hb))
    exact Nat.lt_of_le_of_lt hr (Nat.lt_of_lt_of_le hb' (rank_le E c))
  · have he : l = (E.bases c).reverse := List.mem_singleton.mp hbs
    subst l
    exact Nat.lt_of_lt_of_le (base_rank_lt ha (List.mem_reverse.mp hxl)) (rank_le E c)

/-- Independent exact C3 derivations whose identities are actual declaration positions. -/
inductive IdentityLin (E : Env) : Nat → List Nat → Prop where
  | mk {c : String} {Ls : List (List Nat)} {M : List Nat} :
      rank E c < E.decls.length →
      Ls.length = (E.bases c).reverse.length →
      (∀ (i : Nat) (b : String) (Lb : List Nat),
        (E.bases c).reverse[i]? = some b → Ls[i]? = some Lb → IdentityLin E (rank E b) Lb) →
      Trace (Ls ++ [(E.bases c).reverse.map (rank E)]) M →
      IdentityLin E (rank E c) (rank E c :: M)

/-- Every exact name derivation lifts to independent declaration-position C3. -/
theorem ExactLin.identities {E : Env} {c : String} {L : List String}
    (ht : ExactLin E c L) (ha : E.basesOK = true) :
    rank E c < E.decls.length → IdentityLin E (rank E c) (L.map (rank E)) := by
  induction ht with
  | @mk c Ls M hlen hchildren htrace ih =>
    intro hc
    refine IdentityLin.mk (c := c) (Ls := Ls.map (List.map (rank E))) hc ?_ ?_ ?_
    · simpa only [List.length_map] using hlen
    · intro i b Lb hb hLb
      obtain ⟨hib, _⟩ := List.getElem?_eq_some_iff.mp hb
      have hi : i < Ls.length := by omega
      have he : Ls[i].map (rank E) = Lb := by
        simpa only [List.getElem?_map, List.getElem?_eq_getElem hi,
          Option.map_some, Option.some.injEq] using hLb
      rw [← he]
      exact ih i b Ls[i] hb (List.getElem?_eq_getElem hi)
        (Nat.lt_of_lt_of_le (base_rank_lt ha (List.mem_reverse.mp (List.mem_of_getElem? hb)))
          (rank_le E c))
    · have hm := htrace.rename (rank_injects E) (merge_input_known ha hlen hchildren)
      simpa only [List.map_append, List.map_cons, List.map_nil] using hm

/-- A positional merge input consists only of selected existing identities. -/
theorem identity_input_good {E : Env} {c : String} {Ls : List (List Nat)}
    (ha : E.basesOK = true) (hlen : Ls.length = (E.bases c).reverse.length)
    (hchildren : ∀ (i : Nat) (b : String) (Lb : List Nat),
      (E.bases c).reverse[i]? = some b → Ls[i]? = some Lb → ∀ j ∈ Lb, GoodId E j) :
    ∀ j ∈ (Ls ++ [(E.bases c).reverse.map (rank E)]).flatten, GoodId E j := by
  intro j hj
  obtain ⟨l, hl, hjl⟩ := List.mem_flatten.mp hj
  rcases List.mem_append.mp hl with hls | hbs
  · obtain ⟨i, b, hb, hLb⟩ := paired_get hlen hls
    exact hchildren i b l hb hLb j hjl
  · have he : l = (E.bases c).reverse.map (rank E) := List.mem_singleton.mp hbs
    subst l
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hjl
    subst j
    exact rank_good (Nat.lt_of_lt_of_le (base_rank_lt ha (List.mem_reverse.mp hb)) (rank_le E c))

/-- A positional derivation never contains a sentinel or an unselected duplicate occurrence. -/
theorem IdentityLin.known {E : Env} {i : Nat} {L : List Nat}
    (ht : IdentityLin E i L) (ha : E.basesOK = true) : ∀ j ∈ L, GoodId E j := by
  induction ht with
  | @mk c Ls M hc hlen hchildren htrace ih =>
    intro j hj
    rcases List.mem_cons.mp hj with he | hm
    · subst j; exact rank_good hc
    · exact identity_input_good ha hlen ih j ((htrace.mem_iff j).mp hm)

/-- Direct base identities decode to the existing producer's reversed base list. -/
theorem decode_bases {E : Env} {c : String} (ha : E.basesOK = true) :
    ((E.bases c).reverse.map (rank E)).map (nameAt E) = (E.bases c).reverse := by
  rw [List.map_map]
  apply Eq.trans (b := (E.bases c).reverse.map (fun b => b))
  · apply List.map_congr_left
    intro b hb
    exact nameAt_rank (Nat.lt_of_lt_of_le (base_rank_lt ha (List.mem_reverse.mp hb)) (rank_le E c))
  · exact List.map_id _

/-- Positional exact C3 decodes back to the exact name derivation. -/
theorem IdentityLin.decode {E : Env} {i : Nat} {L : List Nat}
    (ht : IdentityLin E i L) (ha : E.basesOK = true) :
    ExactLin E (nameAt E i) (L.map (nameAt E)) := by
  induction ht with
  | @mk c Ls M hc hlen hchildren htrace ih =>
    have hroot : nameAt E (rank E c) = c := nameAt_rank hc
    simp only [List.map_cons, hroot]
    refine ExactLin.mk (Ls := Ls.map (List.map (nameAt E))) ?_ ?_ ?_
    · simpa only [List.length_map] using hlen
    · intro i b Lb hb hLb
      obtain ⟨hib, _⟩ := List.getElem?_eq_some_iff.mp hb
      have hi : i < Ls.length := by omega
      have he : Ls[i].map (nameAt E) = Lb := by
        simpa only [List.getElem?_map, List.getElem?_eq_getElem hi,
          Option.map_some, Option.some.injEq] using hLb
      rw [← he]
      have hbknown : rank E b < E.decls.length :=
        Nat.lt_of_lt_of_le (base_rank_lt ha (List.mem_reverse.mp (List.mem_of_getElem? hb))) (rank_le E c)
      have hchild := ih i b Ls[i] hb (List.getElem?_eq_getElem hi)
      rw [nameAt_rank hbknown] at hchild
      exact hchild
    · have hm := htrace.rename (nameAt_injects E) (identity_input_good ha hlen
        (fun i b Lb hb hLb => (hchildren i b Lb hb hLb).known ha))
      simpa only [List.map_append, List.map_cons, List.map_nil, decode_bases ha] using hm

/-- Decoding and re-encoding a positional derivation preserves every identity. -/
theorem IdentityLin.roundtrip {E : Env} {i : Nat} {L : List Nat}
    (ht : IdentityLin E i L) (ha : E.basesOK = true) :
    (L.map (nameAt E)).map (rank E) = L := by
  rw [List.map_map]
  apply Eq.trans (b := L.map (fun j => j))
  · exact List.map_congr_left (fun j hj => (ht.known ha j hj).2)
  · exact List.map_id _

/-- Declaration-position output uniqueness follows from deterministic C3, not producer functionality. -/
theorem IdentityLin.unique {E : Env} {i : Nat} {a b : List Nat}
    (ha : IdentityLin E i a) (hb : IdentityLin E i b) (hadm : E.basesOK = true) : a = b := by
  have he := (ha.decode hadm).unique (hb.decode hadm)
  have hm := congrArg (List.map (rank E)) he
  change (a.map (nameAt E)).map (rank E) = (b.map (nameAt E)).map (rank E) at hm
  rw [ha.roundtrip hadm, hb.roundtrip hadm] at hm
  exact hm

/-- Each positional linearization lists every represented identity at most once. -/
theorem IdentityLin.nodup {E : Env} {i : Nat} {L : List Nat}
    (ht : IdentityLin E i L) (ha : E.basesOK = true) : L.Nodup := by
  have hn := (ht.decode ha).nodup ha
  change List.Pairwise (fun x y : String => x ≠ y) (L.map (nameAt E)) at hn
  rw [List.pairwise_map] at hn
  exact hn.imp (fun hne he => hne (congrArg (nameAt E) he))

/-- Every represented position is an existing declaration identity in the original unit graph. -/
theorem IdentityLin.graph_nodes {u : Syn .unit} {i : Nat} {L : List Nat}
    (ht : IdentityLin u.env i L) (ha : u.env.basesOK = true) :
    ∀ j ∈ L, ∃ d, (j, d) ∈ u.graph := by
  intro j hj
  have hg := ht.known ha j hj
  have hknown : rank u.env (nameAt u.env j) < u.decls.length := by
    rw [hg.2]; exact hg.1
  obtain ⟨d, hd, _⟩ := rank_graph u (nameAt u.env j) hknown
  rw [hg.2] at hd
  exact ⟨d, hd⟩

/-- Exact public merge/fuel correspondence lifted to actual declaration-position identities. -/
theorem linearize_identity_iff {E : Env} (ha : E.basesOK = true) (c : String)
    (hc : rank E c < E.decls.length) (I : List Nat) :
    (E.linearize c).map (List.map (rank E)) = some I ↔ IdentityLin E (rank E c) I := by
  constructor
  · intro hm
    cases hs : E.linearize c with
    | none => rw [hs] at hm; cases hm
    | some L =>
      rw [hs] at hm
      simp only [Option.map_some, Option.some.injEq] at hm
      subst I
      exact ((linearize_exact_iff ha c L).mp hs).identities ha hc
  · intro ht
    have hs := (linearize_exact_iff ha (nameAt E (rank E c)) (I.map (nameAt E))).mpr (ht.decode ha)
    rw [nameAt_rank hc] at hs
    rw [hs, Option.map_some, ht.roundtrip ha]

/-- The identity boundary is supplied by existing selected-declaration evidence. -/
theorem linearize_selected_identity_iff {E : Env} (ha : E.basesOK = true) (c : String)
    (hc : ∃ d ∈ E.decls, selects c d = true) (I : List Nat) :
    (E.linearize c).map (List.map (rank E)) = some I ↔ IdentityLin E (rank E c) I := by
  exact linearize_identity_iff ha c (List.findIdx_lt_length_of_exists hc) I

/-- Intrinsic collection puts every contract/interface declaration at file scope. -/
theorem collect_root_scope (scope : Option String) {cat : Cat} (s : Syn cat) :
    ∀ d ∈ s.collect scope, (d.kind = .contract ∨ d.kind = .interface) → d.scope = none := by
  fun_induction Syn.collect scope s <;> intro d hd hk <;>
    try simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  all_goals first
    | (subst hd; rfl)
    | (subst hd; rcases hk with he | he <;> cases he)
    | (rename_i ih; exact ih d hd hk)
    | (rename_i ih
       rcases hd with hd | hd
       · subst hd; rfl
       · exact ih d hd hk)
    | (rename_i ih1 ih2
       rcases hd with hd | hd
       · exact ih1 d hd hk
       · exact ih2 d hd hk)

/-- A real intrinsic contract/interface declaration supplies selection evidence directly. -/
theorem unit_decl_selected (u : Syn .unit) (d : Decl) (hd : d ∈ u.decls)
    (hk : d.kind = .contract ∨ d.kind = .interface) : selects d.name d = true := by
  apply (selects_iff d.name d).mpr
  exact ⟨collect_root_scope none u d hd hk, rfl, hk⟩

/-- Existing source-unit contract-name membership discharges the resolved-root boundary. -/
theorem unit_contract_selected (u : Syn .unit) (c : String) (hc : c ∈ u.env.contractNames) :
    ∃ d ∈ u.decls, selects c d = true := by
  change c ∈ (u.decls.filter fun d => d.kind == .contract || d.kind == .interface).map Decl.name at hc
  obtain ⟨d, hd, hn⟩ := List.mem_map.mp hc
  obtain ⟨hd', hk⟩ := List.mem_filter.mp hd
  have hk' : d.kind = .contract ∨ d.kind = .interface := by
    simpa only [Bool.or_eq_true, beq_iff_eq] using hk
  exact ⟨d, hd', by simpa only [hn] using unit_decl_selected u d hd' hk'⟩

/-- Source-unit identity exactness needs only existing base admission and existing root enumeration. -/
theorem unit_identity_iff (u : Syn .unit) (ha : u.env.basesOK = true) (c : String)
    (hc : c ∈ u.env.contractNames) (I : List Nat) :
    (u.env.linearize c).map (List.map (rank u.env)) = some I ↔ IdentityLin u.env (rank u.env c) I :=
  linearize_selected_identity_iff ha c (unit_contract_selected u c hc) I

/-- The original resolved source-unit relation discharges environment equality as well. -/
theorem resolved_identity_iff {s : Settings} {u : Syn .unit} {r : Resolution}
    (hr : Resolves' s u r) (ha : r.env.basesOK = true) (c : String)
    (hc : c ∈ r.env.contractNames) (I : List Nat) :
    (r.env.linearize c).map (List.map (rank r.env)) = some I ↔ IdentityLin r.env (rank r.env c) I := by
  rw [hr.2] at ha hc ⊢
  exact unit_identity_iff u ha c hc I

end Solidity.Frontend.C3Exactness
