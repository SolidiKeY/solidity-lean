import Solidity.Frontend.C3Exactness.Admission
import Solidity.Frontend.Static.C3

/-!
# Exact inheritance linearization and public fuel

`ExactLin` uses independent merge traces and recursive base derivations in the
producer's reversed direct-base order. It neither calls the producer nor assumes
its public linearization succeeds. Admission/fuel facts use `basesOK`, not the
already-successful `WellFormed.linearizes` field.
-/
namespace Solidity.Frontend.C3Exactness
open Solidity.Source

/-- Independent deterministic C3 derivation on the existing environment. -/
inductive ExactLin (E : Env) : String → List String → Prop where
  | mk {c : String} {Ls : List (List String)} {M : List String} :
      Ls.length = (E.bases c).reverse.length →
      (∀ (i : Nat) (b : String) (Lb : List String),
        (E.bases c).reverse[i]? = some b → Ls[i]? = some Lb → ExactLin E b Lb) →
      Trace (Ls ++ [(E.bases c).reverse]) M → ExactLin E c (c :: M)

/-- Equal-length parallel lists provide an actual source at every target member. -/
theorem paired_get {α β : Type} {bs : List α} {Ls : List β}
    (hlen : Ls.length = bs.length) {l : β} (hl : l ∈ Ls) :
    ∃ (i : Nat) (b : α), bs[i]? = some b ∧ Ls[i]? = some l := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hl
  have hb : i < bs.length := by omega
  exact ⟨i, bs[i], List.getElem?_eq_getElem hb, by
    rw [List.getElem?_eq_getElem hi, he]⟩

/-- Completeness companion to the existing mapM_spec, with exactly its index convention. -/
theorem mapM_complete {f : String → Option (List String)} :
    ∀ (bs : List String) (Ls : List (List String)), Ls.length = bs.length →
      (∀ (i : Nat) (b : String) (Lb : List String), bs[i]? = some b → Ls[i]? = some Lb → f b = some Lb) →
      bs.mapM f = some Ls
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by simp only [List.length_nil, List.length_cons] at hlen; omega
  | _ :: _, [], hlen, _ => by simp only [List.length_nil, List.length_cons] at hlen; omega
  | b :: bs, Lb :: Ls, hlen, hrel => by
    have hh : f b = some Lb := hrel 0 b Lb rfl rfl
    have ht : bs.mapM f = some Ls := mapM_complete bs Ls (by
      simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen)
      (fun i b' Lb' hb hLb => hrel (i + 1) b' Lb' hb hLb)
    simp only [List.mapM_cons, hh, ht, bind, pure, Option.bind_some]

/-- Every successful existing recursive run has the exact independent C3 derivation. -/
theorem linearizeF_exact_sound {E : Env} : ∀ n c L,
    E.linearizeF n c = some L → ExactLin E c L
  | 0, _, _, h => by cases h
  | n + 1, c, L, h => by
    unfold Env.linearizeF at h
    simp only at h
    split at h
    · cases h
    · rename_i Ls hLs
      cases hm : Env.merge (E.decls.length * E.decls.length + 2)
          (Ls ++ [(E.bases c).reverse]) with
      | none => rw [hm] at h; cases h
      | some M =>
        rw [hm] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hpt⟩ := Solidity.Frontend.Static.mapM_spec hLs
        exact .mk hlen (fun i b Lb hb hLb =>
          linearizeF_exact_sound n b Lb (hpt i b Lb hb hLb)) (merge_sound _ _ _ hm)

/-- Graph output uniqueness comes from deterministic child and merge traces. -/
theorem ExactLin.unique {E : Env} {c : String} {a b : List String}
    (ha : ExactLin E c a) (hb : ExactLin E c b) : a = b := by
  induction ha generalizing b with
  | @mk c Ls M hlen hchildren ht ih =>
    cases hb with
    | @mk _ Ls' M' hlen' hchildren' ht' =>
      have he : Ls = Ls' := by
        apply List.ext_getElem (hlen.trans hlen'.symm)
        intro i hi hi'
        have hbase : i < (E.bases c).reverse.length := by omega
        exact ih i (E.bases c).reverse[i] Ls[i]
          (List.getElem?_eq_getElem hbase) (List.getElem?_eq_getElem hi)
          (hchildren' i _ Ls'[i] (List.getElem?_eq_getElem hbase)
            (List.getElem?_eq_getElem hi'))
      subst Ls'
      exact congrArg (c :: ·) (ht.unique ht')

/-- Every merged ancestor has a smaller existing declaration identity. -/
theorem trace_rank_lt {E : Env} {c : String} {Ls : List (List String)} {M : List String}
    (ha : E.basesOK = true) (hlen : Ls.length = (E.bases c).reverse.length)
    (hchildren : ∀ (i : Nat) (b : String) (Lb : List String),
      (E.bases c).reverse[i]? = some b → Ls[i]? = some Lb →
        ∀ x ∈ Lb, rank E x ≤ rank E b)
    (ht : Trace (Ls ++ [(E.bases c).reverse]) M) :
    ∀ x ∈ M, rank E x < rank E c := by
  intro x hx
  obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp ((ht.mem_iff x).mp hx)
  rcases List.mem_append.mp hl with hls | hbs
  · obtain ⟨i, b, hb, hLb⟩ := paired_get hlen hls
    have hbm : b ∈ E.bases c := List.mem_reverse.mp (List.mem_of_getElem? hb)
    exact Nat.lt_of_le_of_lt (hchildren i b l hb hLb x hxl) (base_rank_lt ha hbm)
  · have he : l = (E.bases c).reverse := List.mem_singleton.mp hbs
    subst l
    exact base_rank_lt ha (List.mem_reverse.mp hxl)

/-- Arbitrary exact derivations contain only identities no later than their root. -/
theorem ExactLin.rank_bound {E : Env} {c : String} {L : List String}
    (ht : ExactLin E c L) (ha : E.basesOK = true) :
    ∀ x ∈ L, rank E x ≤ rank E c := by
  induction ht with
  | @mk c Ls M hlen hchildren htrace ih =>
    intro x hx
    rcases List.mem_cons.mp hx with he | hm
    · subst x; exact Nat.le_refl _
    · exact Nat.le_of_lt (trace_rank_lt ha hlen ih htrace x hm)

/-- The strict tail bound excludes the root even in shared-ancestor diamonds. -/
theorem ExactLin.tail_rank {E : Env} {c : String} {M : List String}
    (ht : ExactLin E c (c :: M)) (ha : E.basesOK = true) :
    ∀ x ∈ M, rank E x < rank E c := by
  cases ht with
  | mk hlen hchildren htrace =>
    exact trace_rank_lt ha hlen
      (fun i b Lb hb hLb => (hchildren i b Lb hb hLb).rank_bound ha) htrace

/-- Every merge tail is duplicate-free by the independent trace. -/
theorem ExactLin.tail_nodup {E : Env} {c : String} {M : List String}
    (ht : ExactLin E c (c :: M)) : M.Nodup := by
  cases ht with
  | mk _ _ htrace => exact htrace.nodup

/-- Finite declared names bound a merge tail regardless of repeated input occurrences. -/
theorem ExactLin.tail_length {E : Env} {c : String} {M : List String}
    (ht : ExactLin E c (c :: M)) (ha : E.basesOK = true) : M.length ≤ E.decls.length := by
  have hs : M ⊆ E.decls.map Decl.name := by
    intro x hx
    exact rank_name_mem (Nat.lt_of_lt_of_le (ht.tail_rank ha x hx) (rank_le E c))
  have hlen := nodup_subset_length ht.tail_nodup hs
  simpa only [List.length_map] using hlen

/-- Admitted exact graph linearizations list the root and every reachable name once. -/
theorem ExactLin.nodup {E : Env} {c : String} {L : List String}
    (ht : ExactLin E c L) (ha : E.basesOK = true) : L.Nodup := by
  cases ht with
  | @mk c Ls M hlen hchildren htrace =>
    have ht' : ExactLin E c (c :: M) := .mk hlen hchildren htrace
    exact List.nodup_cons.mpr ⟨fun hm => Nat.lt_irrefl _ (ht'.tail_rank ha c hm), htrace.nodup⟩

/-- Existing recursive depth and merge budgets cover every admitted exact derivation. -/
theorem ExactLin.complete {E : Env} {c : String} {L : List String}
    (ht : ExactLin E c L) (ha : E.basesOK = true) :
    ∀ n, rank E c < n → E.linearizeF n c = some L := by
  induction ht with
  | @mk c Ls M hlen hchildren htrace ih =>
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
      have hmap : (E.bases c).reverse.mapM (E.linearizeF n) = some Ls :=
        mapM_complete _ _ hlen (fun i b Lb hb hLb =>
          ih i b Lb hb hLb n (by
            have hbr := base_rank_lt ha (List.mem_reverse.mp (List.mem_of_getElem? hb))
            omega))
      have ht' : ExactLin E c (c :: M) := .mk hlen hchildren htrace
      have hm : Env.merge (E.decls.length * E.decls.length + 2)
          (Ls ++ [(E.bases c).reverse]) = some M :=
        htrace.complete _ (Nat.lt_of_le_of_lt (ht'.tail_length ha) (public_merge_fuel E))
      change (match (E.bases c).reverse.mapM (E.linearizeF n) with
        | none => none
        | some ls => (Env.merge (E.decls.length * E.decls.length + 2)
            (ls ++ [(E.bases c).reverse])).map (c :: ·)) = some (c :: M)
      simp only [hmap, hm, Option.map_some]

/-- Exact correspondence for the existing public entrypoint under its existing base admission. -/
theorem linearize_exact_iff {E : Env} (ha : E.basesOK = true) (c : String) (L : List String) :
    E.linearize c = some L ↔ ExactLin E c L := by
  constructor
  · exact linearizeF_exact_sound _ c L
  · intro ht
    exact ht.complete ha (E.decls.length + 1) (by have hr := rank_le E c; omega)

/-- Public failure under admission is absence of an independent exact derivation. -/
theorem linearize_none_iff {E : Env} (ha : E.basesOK = true) (c : String) :
    E.linearize c = none ↔ ¬ ∃ L, ExactLin E c L := by
  constructor
  · intro hn ⟨L, ht⟩
    have hs := (linearize_exact_iff ha c L).mpr ht
    rw [hn] at hs
    cases hs
  · intro hn
    cases hs : E.linearize c with
    | none => rfl
    | some L => exact False.elim (hn ⟨L, (linearize_exact_iff ha c L).mp hs⟩)

/-- Successful outputs are unique across arbitrary recursive fuel values. -/
theorem linearizeF_unique {E : Env} {c : String} {a b : List String} {m n : Nat}
    (ha : E.linearizeF m c = some a) (hb : E.linearizeF n c = some b) : a = b :=
  (linearizeF_exact_sound m c a ha).unique (linearizeF_exact_sound n c b hb)

/-- Existing inheritance-edge reachability, including the contract itself. -/
inductive Reaches (E : Env) : String → String → Prop where
  | refl {c} : Reaches E c c
  | step {c b x} : b ∈ E.bases c → Reaches E b x → Reaches E c x

/-- Exact graph membership includes all and only reachable names. -/
theorem ExactLin.mem_iff {E : Env} {c : String} {L : List String}
    (ht : ExactLin E c L) : ∀ x, x ∈ L ↔ Reaches E c x := by
  induction ht with
  | @mk c Ls M hlen hchildren htrace ih =>
    intro x
    constructor
    · intro hx
      rcases List.mem_cons.mp hx with he | hm
      · subst x; exact .refl
      · obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp ((htrace.mem_iff x).mp hm)
        rcases List.mem_append.mp hl with hls | hbs
        · obtain ⟨i, b, hb, hLb⟩ := paired_get hlen hls
          exact .step (List.mem_reverse.mp (List.mem_of_getElem? hb))
            ((ih i b l hb hLb x).mp hxl)
        · have he : l = (E.bases c).reverse := List.mem_singleton.mp hbs
          subst l
          exact .step (List.mem_reverse.mp hxl) .refl
    · intro hr
      cases hr with
      | refl => exact List.mem_cons_self
      | @step _ b _ hb hbx =>
        obtain ⟨i, Lb, hLb, hb'⟩ := paired_get hlen.symm (List.mem_reverse.mpr hb)
        have hx : x ∈ Lb := (ih i b Lb hb' hLb x).mpr hbx
        apply List.mem_cons_of_mem c
        apply (htrace.mem_iff x).mpr
        exact List.mem_flatten.mpr ⟨Lb, List.mem_append_left _ (List.mem_of_getElem? hLb), hx⟩

/-- The producer's reversed direct-base order is an ordered sublist of the tail. -/
theorem ExactLin.direct_order {E : Env} {c : String} {L : List String}
    (ht : ExactLin E c L) : (E.bases c).reverse.Sublist (L.drop 1) := by
  cases ht with
  | mk _ _ htrace =>
    exact htrace.local_order _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

/-- Every base's complete C3 order is preserved as a sublist of the descendant's tail. -/
theorem ExactLin.monotone {E : Env} {c b : String} {L Lb : List String}
    (ht : ExactLin E c L) (hb : b ∈ E.bases c) (htb : ExactLin E b Lb) :
    Lb.Sublist (L.drop 1) := by
  cases ht with
  | mk hlen hchildren htrace =>
    obtain ⟨i, Lb', hLb, hb'⟩ := paired_get hlen.symm (List.mem_reverse.mpr hb)
    have he : Lb' = Lb := (hchildren i b Lb' hb' hLb).unique htb
    subst Lb'
    exact htrace.local_order _ (List.mem_append_left _ (List.mem_of_getElem? hLb))

/-- Constructor order is exactly the reversal of successful deterministic C3. -/
theorem exact_ctorOrder {E : Env} {c : String} {L : List String}
    (hs : E.linearize c = some L) : E.ctorOrder c = L.reverse := by
  simp only [Env.ctorOrder, Env.chain, hs, Option.getD_some]

/-- The constructor sequence lists direct bases in source `is` order before the root. -/
theorem ctor_direct_order {E : Env} {c : String} {L : List String}
    (hs : E.linearize c = some L) : (E.bases c).Sublist (E.ctorOrder c).dropLast := by
  have ht : ExactLin E c L := linearizeF_exact_sound _ c L hs
  have ho := ht.direct_order.reverse
  rw [exact_ctorOrder hs]
  cases ht with
  | mk _ _ _ =>
    simpa only [List.drop_one, List.tail_cons, List.reverse_reverse,
      List.reverse_cons, List.dropLast_concat] using ho

/-- Each inherited base's constructor sequence is preserved in a descendant. -/
theorem ctor_monotone {E : Env} {c b : String} {L Lb : List String}
    (hs : E.linearize c = some L) (hb : b ∈ E.bases c)
    (hsb : E.linearize b = some Lb) :
    (E.ctorOrder b).Sublist (E.ctorOrder c).dropLast := by
  have ht := linearizeF_exact_sound _ c L hs
  have htb := linearizeF_exact_sound _ b Lb hsb
  have ho := (ht.monotone hb htb).reverse
  rw [exact_ctorOrder hs, exact_ctorOrder hsb]
  cases ht with
  | mk _ _ _ =>
    simpa only [List.drop_one, List.tail_cons, List.reverse_cons, List.dropLast_concat] using ho

/-- With existing admission each name appears at most once in the public constructor sequence. -/
theorem ctor_nodup {E : Env} {c : String} {L : List String}
    (ha : E.basesOK = true) (hs : E.linearize c = some L) : (E.ctorOrder c).Nodup := by
  rw [exact_ctorOrder hs]
  apply List.pairwise_reverse.mpr
  exact (((linearize_exact_iff ha c L).mp hs).nodup ha).imp (fun h => Ne.symm h)

/-- An actual self-cycle fails at every recursive fuel, without any admission assumption. -/
theorem linearizeF_self_cycle {E : Env} {c : String} (hc : E.bases c = [c]) :
    ∀ n, E.linearizeF n c = none
  | 0 => rfl
  | n + 1 => by
    simp only [Env.linearizeF, hc, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.mapM_cons, linearizeF_self_cycle hc n, List.mapM_nil, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, Option.bind_none]

/-- Finite graph obstruction: a blocked merge, or an inheritance edge leading to one. -/
inductive GraphBlocked (E : Env) : String → Prop where
  | merge {c : String} {Ls : List (List String)} :
      Ls.length = (E.bases c).reverse.length →
      (∀ (i : Nat) (b : String) (Lb : List String),
        (E.bases c).reverse[i]? = some b → Ls[i]? = some Lb → ExactLin E b Lb) →
      Stuck (Ls ++ [(E.bases c).reverse]) → GraphBlocked E c
  | base {c b : String} : b ∈ E.bases c → GraphBlocked E b → GraphBlocked E c

/-- A failed finite option traversal has a concrete failing member. -/
theorem mapM_none {f : String → Option (List String)} : ∀ bs : List String,
    bs.mapM f = none → ∃ b ∈ bs, f b = none
  | [], h => by cases h
  | b :: bs, h => by
    cases hb : f b with
    | none => exact ⟨b, List.mem_cons_self, hb⟩
    | some Lb =>
      simp only [List.mapM_cons, bind, pure, hb, Option.bind_some] at h
      cases ht : bs.mapM f with
      | none =>
        obtain ⟨b', hm, hf⟩ := mapM_none bs ht
        exact ⟨b', List.mem_cons_of_mem b hm, hf⟩
      | some Ls => rw [ht] at h; cases h

/-- A finite graph obstruction excludes every successful independent derivation. -/
theorem GraphBlocked.not_exact {E : Env} {c : String} (hb : GraphBlocked E c) :
    ∀ {L}, ¬ ExactLin E c L := by
  induction hb with
  | @merge c Ls hlen hchildren hs =>
    intro L ht
    cases ht with
    | @mk _ Ls' M hlen' hchildren' htrace =>
      have he : Ls = Ls' := by
        apply List.ext_getElem (hlen.trans hlen'.symm)
        intro i hi hi'
        have hbase : i < (E.bases c).reverse.length := by omega
        exact (hchildren i _ _ (List.getElem?_eq_getElem hbase)
          (List.getElem?_eq_getElem hi)).unique
          (hchildren' i _ _ (List.getElem?_eq_getElem hbase) (List.getElem?_eq_getElem hi'))
      subst Ls'
      exact hs.not_trace htrace
  | @base c b hbase hb ih =>
    intro L ht
    cases ht with
    | mk hlen hchildren _ =>
      obtain ⟨i, Lb, hLb, hb'⟩ := paired_get hlen.symm (List.mem_reverse.mpr hbase)
      exact ih (hchildren i b Lb hb' hLb)

/-- Existing acyclic admission gives a derivation or a constructive graph obstruction. -/
theorem graph_trace_or_blocked {E : Env} (ha : E.basesOK = true) (c : String) :
    (∃ L, ExactLin E c L) ∨ GraphBlocked E c := by
  suffices ∀ n (c : String), rank E c = n →
      (∃ L, ExactLin E c L) ∨ GraphBlocked E c from this _ c rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro c hn
    cases hm : (E.bases c).reverse.mapM E.linearize with
    | none =>
      obtain ⟨b, hb, hf⟩ := mapM_none _ hm
      have hb' : b ∈ E.bases c := List.mem_reverse.mp hb
      have hlt : rank E b < n := by rw [← hn]; exact base_rank_lt ha hb'
      rcases ih _ hlt b rfl with ⟨L, ht⟩ | hs
      · have he := (linearize_exact_iff ha b L).mpr ht
        rw [hf] at he
        cases he
      · exact Or.inr (.base hb' hs)
    | some Ls =>
      obtain ⟨hlen, hpt⟩ := Solidity.Frontend.Static.mapM_spec hm
      have hchildren : ∀ (i : Nat) (b : String) (Lb : List String),
          (E.bases c).reverse[i]? = some b → Ls[i]? = some Lb → ExactLin E b Lb :=
        fun i b Lb hb hLb => (linearize_exact_iff ha b Lb).mp (hpt i b Lb hb hLb)
      rcases trace_or_stuck (Ls ++ [(E.bases c).reverse]) with ⟨M, ht⟩ | hs
      · exact Or.inl ⟨c :: M, .mk hlen hchildren ht⟩
      · exact Or.inr (.merge hlen hchildren hs)

/-- Public admitted-graph failure is precisely a finite genuine C3 graph obstruction. -/
theorem linearize_none_iff_blocked {E : Env} (ha : E.basesOK = true) (c : String) :
    E.linearize c = none ↔ GraphBlocked E c := by
  constructor
  · intro hn
    rcases graph_trace_or_blocked ha c with ⟨L, ht⟩ | hb
    · exact False.elim (((linearize_none_iff ha c).mp hn) ⟨L, ht⟩)
    · exact hb
  · intro hb
    apply (linearize_none_iff ha c).mpr
    rintro ⟨L, ht⟩
    exact hb.not_exact ht

/-- A checked graph obstruction fails at every fuel, without assuming admission. -/
theorem GraphBlocked.linearizeF_none {E : Env} {c : String}
    (hb : GraphBlocked E c) (n : Nat) : E.linearizeF n c = none := by
  cases hs : E.linearizeF n c with
  | none => rfl
  | some L => exact False.elim (hb.not_exact (linearizeF_exact_sound n c L hs))

/-- A nonempty inheritance path, used as a checked cycle witness. -/
inductive CyclePath (E : Env) : String → String → Prop where
  | direct {c b} : b ∈ E.bases c → CyclePath E c b
  | step {c b x} : b ∈ E.bases c → CyclePath E b x → CyclePath E c x

/-- Existing base admission rules out every nonempty cycle by strict rank descent. -/
theorem CyclePath.rank_lt {E : Env} {c b : String} (hp : CyclePath E c b)
    (ha : E.basesOK = true) : rank E b < rank E c := by
  induction hp with
  | direct hb => exact base_rank_lt ha hb
  | step hb hp ih => exact Nat.lt_trans ih (base_rank_lt ha hb)

/-- Every exact derivation supplies a strictly shorter exact derivation for each base. -/
theorem ExactLin.base_length {E : Env} {c b : String} {L : List String}
    (ht : ExactLin E c L) (hb : b ∈ E.bases c) :
    ∃ Lb, ExactLin E b Lb ∧ Lb.length < L.length := by
  cases ht with
  | mk hlen hchildren htrace =>
    obtain ⟨i, Lb, hLb, hb'⟩ := paired_get hlen.symm (List.mem_reverse.mpr hb)
    have hsub := htrace.local_order Lb (List.mem_append_left _ (List.mem_of_getElem? hLb))
    exact ⟨Lb, hchildren i b Lb hb' hLb, Nat.lt_succ_of_le hsub.length_le⟩

/-- A nonempty path forces strict derivation-length descent, without admission assumptions. -/
theorem CyclePath.descendant {E : Env} {c b : String} (hp : CyclePath E c b) :
    ∀ {L}, ExactLin E c L → ∃ Lb, ExactLin E b Lb ∧ Lb.length < L.length := by
  induction hp with
  | direct hb => intro L ht; exact ht.base_length hb
  | step hb hp ih =>
    intro L ht
    obtain ⟨Lb, htb, hblen⟩ := ht.base_length hb
    obtain ⟨Lx, htx, hxlen⟩ := ih htb
    exact ⟨Lx, htx, Nat.lt_trans hxlen hblen⟩

/-- A checked actual cycle excludes independent exact C3 at every derivation depth. -/
theorem CyclePath.not_exact {E : Env} {c : String} (hp : CyclePath E c c) :
    ∀ {L}, ¬ ExactLin E c L := by
  intro L ht
  obtain ⟨Lb, htb, hlen⟩ := hp.descendant ht
  have he : L = Lb := ht.unique htb
  rw [← he] at hlen
  exact Nat.lt_irrefl _ hlen

/-- Every finite-fuel producer run refuses a graph with a checked cycle witness. -/
theorem CyclePath.linearizeF_none {E : Env} {c : String} (hp : CyclePath E c c) (n : Nat) :
    E.linearizeF n c = none := by
  cases hs : E.linearizeF n c with
  | none => rfl
  | some L => exact False.elim (hp.not_exact (linearizeF_exact_sound n c L hs))

end Solidity.Frontend.C3Exactness
