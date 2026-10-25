import Solidity.Calculus.HashSwap

/-!
# Refuting a leaf with hashes under its own premise (M7, plan step 7)

`Calculus/HashSwap.lean` reads a leaf's fresh byte strings as the words
their hashes return (`Fml.swPrefix`): a valid reading proves the leaf.  A
refutation must be a state that meets the goal's own hash premise
(`Fml.HashFree`), so it cannot pick the hashes: it picks the byte strings.
`Fml.swInst k cs` is the swapped leaf with the `i`-th string's word fixed to
the hash of a fixed one-word string, the `cs[i]`-th of a family
(`famBytes`): strings with one class share it, strings of two classes have
two.  A state that refutes it refutes the leaf: the strings allocated with
those bytes hash to exactly those words (`State.alloc_hashId_self`), and a
heap of the family's strings alone meets every premise of the leaf
(`Fml.hashFree_fam`), the family's hashes being distinct and nonzero
(`famOK`, checked in the kernel for four classes, `famOK_four`).
-/

namespace Solidity.Decide

variable {C : Contract}

/-! ## The family of byte strings -/

/-- The `j`-th string of the family: the one word `j`. -/
def famBytes (j : Nat) : List Int := [(uintOfNat j).1]

/-- The `j`-th string, an object. -/
def famObj (H : HTy) (j : Nat) : MObj H (.array (.prim .uint)) :=
  (⟨[uintOfNat j], by show 1 < 2 ^ 256; decide⟩ : {l : List (MVal H (.prim .uint)) // l.length < 2 ^ 256})

theorem famObj_words (H : HTy) (j : Nat) :
    MObj.words (.array (.prim .uint)) (famObj H j) = famBytes j := rfl

/-- The word the `j`-th string hashes to. -/
def famHash (k : HashKind) (j : Nat) : PrimTy.uint.Denote := k.apply (famBytes j)

/-- The family's first `n` strings hash to distinct, nonzero words. -/
def famOK (k : HashKind) (n : Nat) : Bool :=
  (List.range n).all fun i => (famHash k i).1 != 0 &&
    (List.range n).all fun j => i == j || (famHash k i).1 != (famHash k j).1

theorem famOK_ne {k : HashKind} {n : Nat} (h : famOK k n = true) {j : Nat} (hj : j < n) :
    (famHash k j).1 ≠ 0 := by
  simp only [famOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact (h j hj).1

theorem famOK_inj {k : HashKind} {n : Nat} (h : famOK k n = true) {i j : Nat} (hi : i < n)
    (hj : j < n) (e : famHash k i = famHash k j) : i = j := by
  simp only [famOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true, beq_iff_eq] at h
  rcases (h i hi).2 j hj with h' | h'
  · exact h'
  · exact absurd (congrArg Subtype.val e) h'

/-- The most classes of strings a leaf's refutation is built for. -/
def famBound : Nat := 4

theorem famOK_keccak : famOK .keccak famBound = true := by decide +kernel
theorem famOK_sha256 : famOK .sha256 famBound = true := by decide +kernel
theorem famOK_ripemd160 : famOK .ripemd160 famBound = true := by decide +kernel

/-- The family checked for every kind the premise reads. -/
theorem famOK_bound (k : HashKind) (hk : k ≠ .ecrecover) : famOK k famBound = true := by
  cases k with
  | keccak => exact famOK_keccak
  | sha256 => exact famOK_sha256
  | ripemd160 => exact famOK_ripemd160
  | ecrecover => exact absurd rfl hk


/-! ## A heap of the family's strings meets every premise -/

/-- Every object of the heap is one of the family's first `N` strings. -/
def FamHeap (N : Nat) (g : State C []) : Prop :=
  ∀ {R : RefTy} (r : HRef g.H R), ∃ j < N, MObj.words R (g.heap.get r) = famBytes j

/-- What a hash of an identity reads and returns in such a heap: nothing and
`0`, or a string of the family and its hash. -/
theorem FamHeap.hash {N : Nat} {g : State C []} (hF : FamHeap N g) (k : HashKind) (R : RefTy)
    (id : Nat) :
    (g.memT.hashInput R id = none ∧ g.memT.hashId k R id = PrimTy.dflt .uint) ∨
      ∃ j < N, g.memT.hashInput R id = some ((famBytes j).map fun b => b.toNat % 256) ∧
        g.memT.hashId k R id = famHash k j := by
  unfold Grown.hashInput Grown.hashId
  cases hr : HRef.ofId? g.memT.H' R id with
  | none => exact .inl ⟨rfl, rfl⟩
  | some r =>
    obtain ⟨j, hj, hw⟩ := hF r
    refine .inr ⟨j, hj, ?_, ?_⟩
    · show some ((MObj.words R (g.heap.get r)).map _) = some _
      rw [hw]
    · show k.apply (MObj.words R (g.heap.get r)) = _
      rw [hw]
      rfl

theorem FamHeap.empty (N : Nat) (g : State C []) (hH : g.H = []) : FamHeap N g := by
  intro R r
  have h := (List.getElem?_eq_some_iff.1 r.get?).1
  have h0 : g.H.length = 0 := by rw [hH]; rfl
  omega

/-- **Allocating a string of the family keeps the heap of the family.** -/
theorem FamHeap.alloc {N : Nat} {Γ : Ctx} {σ : State C Γ} (hF : FamHeap N σ.glob) {j : Nat}
    (hj : j < N) : FamHeap N (σ.alloc (famObj σ.H j)).1.glob := by
  intro R r
  by_cases hr : r.id < σ.H.length
  · have hg : σ.H[r.id]? = some R := by
      have hid := r.get?
      change (σ.H ++ [.array (.prim .uint)])[r.id]? = some R at hid
      rw [List.getElem?_append_left hr] at hid
      exact hid
    let r₀ : HRef σ.H R := ⟨r.id, hg⟩
    have he : r = r₀.wk (List.prefix_append σ.H [.array (.prim .uint)]) := by
      cases r; rfl
    obtain ⟨i, hi, hw⟩ := hF r₀
    refine ⟨i, hi, ?_⟩
    show MObj.words R ((σ.heap.alloc (famObj σ.H j)).1.get r) = _
    rw [he, Heap.keeps_alloc σ.heap (famObj σ.H j) r₀, MObj.words_wk]
    exact hw
  · have hid := r.get?
    change (σ.H ++ [.array (.prim .uint)])[r.id]? = some R at hid
    have hl : r.id = σ.H.length := by
      have := (List.getElem?_eq_some_iff.1 hid).1
      simp only [List.length_append, List.length_singleton] at this
      omega
    have hR : R = .array (.prim .uint) := by
      rw [hl, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero] at hid
      exact (Option.some.inj hid).symm
    subst hR
    have he : r = (σ.heap.alloc (famObj σ.H j)).2 := by
      cases r; simp only at hl; subst hl; rfl
    refine ⟨j, hj, ?_⟩
    show MObj.words _ ((σ.heap.alloc (famObj σ.H j)).1.get r) = _
    rw [he, Heap.get_alloc, MObj.words_wk]
    rfl

/-- A hash node `Tm.sw` reads as a word reads the starting memory. -/
theorem _root_.Solidity.Op2.hashSw?_hashIn {k k' : HashKind} {Γ : Ctx} (σ : State C Γ)
    {inp : Option (List Nat)} {out : PrimTy.uint.Denote} {a b s : Srt} (o : Op2 C a b s)
    (x : Tm C Γ a) (y : Tm C Γ b) {t' : Tm C (Ctx.sw Γ) s} (ht : o.hashSw? k x y = some t')
    (h : (Tm.app2 o x y).HashIn σ k' inp out) :
    k' = k ∧ ∃ R id, inp = σ.glob.memT.hashInput R id ∧ out = σ.glob.memT.hashId k' R id := by
  unfold Op2.hashSw? at ht
  split at ht
  · rename_i R k₀ i
    have hk : k₀ = k := by
      by_cases hk : k₀ = k
      · exact hk
      · simp only [hk, if_false, reduceCtorEq] at ht
    rcases h with h | h | h
    · revert h
      show Op2.HashIn (H := σ.H) k' inp out (Op2.hash (R := R) k₀) (some σ.glob.memT)
        ((TEnv.get i σ.env).map (·.id)) → _
      cases TEnv.get i σ.env with
      | none => exact fun h => h.elim
      | some r =>
        rintro ⟨rfl, h1, h2⟩
        exact ⟨hk, R, r.id, h1, h2⟩
    · exact h.elim
    · exact h.elim
  · cases ht

/-- The hash nodes of a term `Tm.sw` takes are of its kind and read the
starting memory. -/
theorem _root_.Solidity.Tm.sw_hashIn {k k' : HashKind} {Γ : Ctx} (σ : State C Γ)
    {inp : Option (List Nat)} {out : PrimTy.uint.Denote} : {s : Srt} → (t : Tm C Γ s) →
    {t' : Tm C (Ctx.sw Γ) s} → t.sw k = some t' → t.HashIn σ k' inp out →
      k' = k ∧ ∃ R id, inp = σ.glob.memT.hashInput R id ∧ out = σ.glob.memT.hashId k' R id
  | _, .netOf i a, _, e, h => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 e
    exact Tm.sw_hashIn σ a ha h
  | s, .app1 (a := a) o x, _, e, h => by
    simp only [Tm.sw] at e
    split at e
    · cases e
    · obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 e
      exact Tm.sw_hashIn σ x hx h
  | s, .app2 (a := a) (b := b) o x y, _, e, h => by
    simp only [Tm.sw] at e
    split at e
    · rename_i t₀ hh
      exact o.hashSw?_hashIn σ x y hh h
    · split at e
      · cases e
      · rename_i hm
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hm
        obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
        obtain ⟨y', hy, rfl⟩ := Option.map_eq_some_iff.1 e
        rcases h with h | h | h
        · cases o <;> first | exact h.elim | exact absurd hm.1.1 (by decide)
        · exact Tm.sw_hashIn σ x hx h
        · exact Tm.sw_hashIn σ y hy h
  | s, .app3 (a := a) (b := b) (c := c) o x y z, _, e, h => by
    simp only [Tm.sw] at e
    split at e
    · cases e
    · obtain ⟨x', hx, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨y', hy, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨z', hz, rfl⟩ := Option.map_eq_some_iff.1 e
      rcases h with h | h | h
      · exact Tm.sw_hashIn σ x hx h
      · exact Tm.sw_hashIn σ y hy h
      · exact Tm.sw_hashIn σ z hz h
  | _, .pvV _, _, _, h | _, .pvP _, _, _, h | _, .pvS _, _, _, h | _, .pvI _, _, _, h
  | _, .app0 _, _, _, h | _, .pvZ _, _, _, h => h.elim


/-- The hash nodes of a formula `Fml.sw` takes are of its kind and read the
memory it starts in, past its updates too. -/
theorem _root_.Solidity.Fml.sw_hashIn {k k' : HashKind} {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {φ' : Fml C (Ctx.sw Γ)}, φ.sw k = some φ' → ∀ (σ : State C Γ) {inp : Option (List Nat)}
      {out : PrimTy.uint.Denote}, Fml.HashIn k' inp out σ φ →
      k' = k ∧ ∃ R id, inp = σ.glob.memT.hashInput R id ∧ out = σ.glob.memT.hashId k' R id := by
  induction φ with
  | tt => intro _ _ _ _ _ h; exact h.elim
  | eq a b =>
    intro _ e σ _ _ h
    obtain ⟨a', ha, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.1 e
    rcases h with h | h
    · exact Tm.sw_hashIn σ a ha h
    · exact Tm.sw_hashIn σ b hb h
  | wellFormed s =>
    intro _ e σ _ _ h
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 e
    exact Tm.sw_hashIn σ s hs h
  | not φ ih =>
    intro _ e σ _ _ h
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact ih hφ σ h
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ =>
    intro _ e σ _ _ h
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    rcases h with h | h
    · exact ihφ hφ σ h
    · exact ihψ hψ σ h
  | upd m U φ ih =>
    intro _ e σ _ _ h
    obtain ⟨U', hU, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    · obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
      cases U with
      | snoc U₀ e₀ =>
        cases U₀ with
        | nil =>
          have hU' : (e₀.sw1? k).map (.snoc .nil) = some U' := hU
          obtain ⟨e', he, rfl⟩ := Option.map_eq_some_iff.1 hU'
          cases e₀ with
          | storage s =>
            have he' : (s.sw k).map UpdElem.storage = some e' := he
            obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 he'
            rcases h with (h | h) | ⟨g, σ', hg, hL, h⟩
            · exact h.elim
            · exact Tm.sw_hashIn σ s hs h
            · have hg' : (s.eval σ).bind (fun st => some (σ.globG.withStorage st)) = some g := hg
              obtain ⟨st, -, ⟨⟩⟩ := Option.bind_eq_some_iff.1 hg'
              have hσ : σ'.glob = { σ.glob with storage := st } := hL.2.1
              obtain ⟨hk, R, id, h1, h2⟩ := ih hφ σ' h
              refine ⟨hk, R, id, ?_, ?_⟩
              · rw [h1, hσ]; rfl
              · rw [h2, hσ]; rfl
          | «local» i r =>
            have he' : (r.sw k).map (UpdElem.local i.sw) = some e' := he
            obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 he'
            cases r with
            | val t =>
              have hr' : (t.sw k).map Rhs.val = some r' := hr
              obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hr'
              rcases h with (h | h) | ⟨g, σ', hg, hL, h⟩
              · exact h.elim
              · exact Tm.sw_hashIn σ t ht h
              · have hg' : (t.eval σ).bind (fun _ => some σ.globG) = some g := hg
                obtain ⟨_, -, ⟨⟩⟩ := Option.bind_eq_some_iff.1 hg'
                have hσ : σ'.glob = σ.glob := hL.2.1
                obtain ⟨hk, R, id, h1, h2⟩ := ih hφ σ' h
                exact ⟨hk, R, id, by rw [h1, hσ], by rw [h2, hσ]⟩
            | _ => cases hr
          | _ => cases he
        | _ => cases hU
      | decl U₀ x r =>
        cases U₀ with
        | nil =>
          have hU' : (r.sw k).map (.decl .nil x) = some U' := hU
          obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 hU'
          cases r with
          | val t =>
            have hr' : (t.sw k).map Rhs.val = some r' := hr
            obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hr'
            rcases h with (h | h) | ⟨g, σ', hg, hL, h⟩
            · exact h.elim
            · exact Tm.sw_hashIn σ t ht h
            · have hg' : (t.eval σ).bind (fun _ => some σ.globG) = some g := hg
              obtain ⟨_, -, ⟨⟩⟩ := Option.bind_eq_some_iff.1 hg'
              have hσ : σ'.glob = σ.glob := hL.2.1
              obtain ⟨hk, R, id, h1, h2⟩ := ih hφ σ' h
              exact ⟨hk, R, id, by rw [h1, hσ], by rw [h2, hσ]⟩
          | _ => cases hr
        | _ => cases hU
      | _ => cases hU
    · cases e
  | modal | havoc | all | bind | anon | allocAll | grow => intro _ e; cases e

/-- **A heap of the family's strings meets the premise** of a formula
`Fml.sw` takes. -/
theorem _root_.Solidity.Fml.hashFree_fam {k : HashKind} {Γ : Ctx} {φ : Fml C Γ}
    {φ' : Fml C (Ctx.sw Γ)} (e : φ.sw k = some φ') (σ : State C Γ) {N : Nat}
    (hF : FamHeap N σ.glob) (hok : famOK k N = true) : φ.HashFree σ := by
  intro k' _ i₁ i₂ out h₁ h₂
  obtain ⟨rfl, R₁, id₁, rfl, ho₁⟩ := Fml.sw_hashIn φ e σ h₁
  obtain ⟨-, R₂, id₂, rfl, ho₂⟩ := Fml.sw_hashIn φ e σ h₂
  rcases hF.hash k' R₁ id₁ with ⟨hi₁, hh₁⟩ | ⟨j₁, hj₁, hi₁, hh₁⟩ <;>
    rcases hF.hash k' R₂ id₂ with ⟨hi₂, hh₂⟩ | ⟨j₂, hj₂, hi₂, hh₂⟩
  · rw [hi₁, hi₂]
  · exact absurd (congrArg Subtype.val ((hh₁.symm.trans ho₁.symm).trans (ho₂.trans hh₂))).symm
      (famOK_ne hok hj₂)
  · exact absurd (congrArg Subtype.val ((hh₂.symm.trans ho₂.symm).trans (ho₁.trans hh₁))).symm
      (famOK_ne hok hj₁)
  · rw [hi₁, hi₂, famOK_inj hok hj₁ hj₂ ((hh₁.symm.trans ho₁.symm).trans (ho₂.trans hh₂))]

/-! ## The leaf with its strings chosen -/

/-- **The swapped leaf with its strings chosen**: `Fml.swPrefix`, the `i`-th
fresh string's word fixed to the hash of the family's `cs[i]`-th string. -/
def _root_.Solidity.Fml.swInst (k : HashKind) : {Γ : Ctx} → List Nat → Fml C Γ →
    Option (Fml C (Ctx.sw Γ))
  | _, cs, .all x p φ => (Fml.swInst k cs φ).map (.all x p)
  | _, cs, .allocAll x R φ =>
    match cs with
    | [] => none
    | j :: cs =>
      if R = .array (.prim .uint) then
        (Fml.swInst k cs φ).map fun φ' =>
          .all x .uint (.imp (.eq (.pvV .here) (.app0 (.lit (famHash k j)))) φ')
      else none
  | _, _, .tt => Fml.sw k .tt
  | _, _, .eq a b => Fml.sw k (.eq a b)
  | _, _, .wellFormed s => Fml.sw k (.wellFormed s)
  | _, _, .not φ => Fml.sw k (.not φ)
  | _, _, .and φ ψ => Fml.sw k (.and φ ψ)
  | _, _, .imp φ ψ => Fml.sw k (.imp φ ψ)
  | _, _, .upd m U φ => Fml.sw k (.upd m U φ)
  | _, _, .modal .. | _, _, .havoc _ | _, _, .bind .. | _, _, .anon .. | _, _, .grow _ => none

/-- A formula `Fml.swInst` takes meets its premise in a heap of the family. -/
theorem _root_.Solidity.Fml.hashFree_inst {k : HashKind} {Γ : Ctx} {φ : Fml C Γ} {cs : List Nat}
    {φ' : Fml C (Ctx.sw Γ)} (e : φ.swInst k cs = some φ') (σ : State C Γ) {N : Nat}
    (hF : FamHeap N σ.glob) (hok : famOK k N = true) : φ.HashFree σ := by
  cases φ with
  | all | allocAll => intro _ _ _ _ _ h; exact h.elim
  | modal | havoc | bind | anon | grow => cases e
  | _ => exact Fml.hashFree_fam e σ hF hok

/-- **What the leaf says under its premise, its strings chosen in the
family, the swapped leaf says.** -/
theorem _root_.Solidity.Fml.swInst_holds {k : HashKind} {N : Nat} (hok : famOK k N = true)
    {Γ : Ctx} (φ : Fml C Γ) : ∀ {cs : List Nat} {φ' : Fml C (Ctx.sw Γ)}, φ.swInst k cs = some φ' →
      (∀ j ∈ cs, j < N) → ∀ (τ : State C Γ) (τ' : State C (Ctx.sw Γ)), SwRel k τ τ' →
      FamHeap N τ.glob → Fml.holdsS τ φ → holds τ' φ' := by
  induction φ with
  | all x p φ ih =>
    intro cs _ e hcs τ τ' h hF hs
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact fun v => ih hφ hcs _ _ (h.push v) hF (hs v (Fml.hashFree_inst hφ _ hF hok))
  | allocAll x R φ ih =>
    intro cs _ e hcs τ τ' h hF hs
    cases cs with
    | nil => cases e
    | cons j cs =>
      simp only [Fml.swInst] at e
      split at e
      · rename_i hR
        subst hR
        obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
        have hj : j < N := hcs j (List.mem_cons_self ..)
        intro w hw
        have hw' : w = famHash k j := Option.some.inj hw
        subst hw'
        let o := famObj τ.H j
        have hF' : FamHeap N (τ.alloc o).1.glob := hF.alloc hj
        have h' := (h.alloc o).pushMem (τ.alloc o).2
        rw [State.alloc_hashId_self, famObj_words] at h'
        exact ih hφ (fun i hi => hcs i (List.mem_cons_of_mem _ hi)) _ _ h' hF'
          (hs o (Fml.hashFree_inst hφ _ hF' hok))
      · cases e
  | tt | eq | wellFormed | not | and | imp | upd =>
    intro cs _ e _ τ τ' h _ hs
    exact (Fml.sw_holds _ e τ τ' h).2 ((Fml.holdsS_of_sw _ e τ).1 hs)
  | modal | havoc | bind | anon | grow => intro _ _ e; cases e

/-- The state with no memory. -/
def _root_.Solidity.State.noHeap (σ : State C []) : State C [] :=
  { σ with H := [], heap := Heap.empty, env := () }

/-- **A refutation of the swapped leaf with its strings chosen refutes the
leaf under its premise**: in the state with no memory, the leaf's fresh
strings allocated with the chosen bytes. -/
theorem _root_.Solidity.Fml.swInst_refutes {k : HashKind} {N : Nat} (hok : famOK k N = true)
    {φ : Fml C []} {cs : List Nat} {φ' : Fml C []} (e : φ.swInst k cs = some φ')
    (hcs : ∀ j ∈ cs, j < N) {σ : State C []} (hr : ¬ holds σ φ') : ¬ Fml.holdsH σ.noHeap φ := by
  intro hH
  have hF : FamHeap N σ.noHeap.glob := FamHeap.empty N _ rfl
  exact hr (Fml.swInst_holds hok φ e hcs σ.noHeap σ ⟨⟨rfl, rfl, rfl, rfl⟩, fun i => nomatch i⟩ hF
    (hH (Fml.hashFree_inst e _ hF hok)))

end Solidity.Decide
