import Solidity.Calculus.HashRelabel

/-!
# Completeness of the refutations of leaves with hashes (M7, plan step 7)

A refutation of the swapped leaf (`Fml.swPrefix`, words free) gives one of
an instance with the family's words (`Fml.swInst`), where the leaf's
strings are the family's: the free words, read in order, fall into classes
(`classesOf`, a restricted growth string of `rgs`), the instance at those
classes has one family word per class, and the refuting state relabeled
(`RelRL`, `Calculus/HashRelabel.lean`) refutes it (`Fml.swPrefix_complete`).

`Fml.swInstV` is the instance at any words, of which `Fml.swInst` is the
family's (`Fml.swInst_eq`); a refutation of the free reading is one of its
instance at the words it chose (`Fml.swPrefix_insts`), and an instance at
the family's words, relabeled, reads as the instance at the free ones
(`Fml.swInstV_transfer`).
-/

namespace Solidity.Decide

variable {C : Contract}

/-! ## Instances at any words -/

/-- The fresh strings of a leaf's prefix. -/
def _root_.Solidity.Fml.allocCount : {Γ : Ctx} → Fml C Γ → Nat
  | _, .all _ _ φ => φ.allocCount
  | _, .allocAll _ _ φ => φ.allocCount + 1
  | _, _ => 0

/-- `Fml.swPrefix` with the `i`-th fresh string's word fixed to `vs[i]`. -/
def _root_.Solidity.Fml.swInstV (k : HashKind) : {Γ : Ctx} → List PrimTy.uint.Denote → Fml C Γ →
    Option (Fml C (Ctx.sw Γ))
  | _, vs, .all x p φ => (Fml.swInstV k vs φ).map (.all x p)
  | _, vs, .allocAll x R φ =>
    match vs with
    | [] => none
    | v :: vs =>
      if R = .array (.prim .uint) then
        (Fml.swInstV k vs φ).map fun φ' => .all x .uint (.imp (.eq (.pvV .here) (.app0 (.lit v))) φ')
      else none
  | _, _, .tt => Fml.sw k .tt
  | _, _, .eq a b => Fml.sw k (.eq a b)
  | _, _, .wellFormed s => Fml.sw k (.wellFormed s)
  | _, _, .not φ => Fml.sw k (.not φ)
  | _, _, .and φ ψ => Fml.sw k (.and φ ψ)
  | _, _, .imp φ ψ => Fml.sw k (.imp φ ψ)
  | _, _, .upd m U φ => Fml.sw k (.upd m U φ)
  | _, _, .modal .. | _, _, .havoc _ | _, _, .bind .. | _, _, .anon .. | _, _, .grow _ => none

theorem _root_.Solidity.Fml.swInst_eq (k : HashKind) {Γ : Ctx} (φ : Fml C Γ) :
    ∀ cs : List Nat, φ.swInst k cs = φ.swInstV k (cs.map (famHash k)) := by
  induction φ with
  | all x p φ ih => intro cs; simp only [Fml.swInst, Fml.swInstV, ih]
  | allocAll x R φ ih =>
    intro cs
    cases cs with
    | nil => rfl
    | cons j cs => simp only [Fml.swInst, Fml.swInstV, List.map_cons, ih]
  | _ => intro _; rfl

/-- **A refutation of the free reading refutes its instance at the words it
chose.** -/
theorem _root_.Solidity.Fml.swPrefix_insts (k : HashKind) {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {φ' : Fml C (Ctx.sw Γ)}, φ.swPrefix k = some φ' → ∀ σ : State C (Ctx.sw Γ), ¬ holds σ φ' →
      ∃ (vs : List PrimTy.uint.Denote) (φv : Fml C (Ctx.sw Γ)), vs.length = φ.allocCount ∧
        φ.swInstV k vs = some φv ∧ ¬ holds σ φv := by
  induction φ with
  | all x p φ ih =>
    intro _ e σ hn
    obtain ⟨φ₁, hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    have : ∃ v, ¬ holds (σ.push (t := .val p) v) φ₁ := Classical.byContradiction fun hc =>
      hn fun v => Classical.byContradiction fun hv => hc ⟨v, hv⟩
    obtain ⟨v, hv⟩ := this
    obtain ⟨vs, φv, hl, he, hnv⟩ := ih hφ _ hv
    refine ⟨vs, .all x p φv, hl, ?_, fun ha => hnv (ha v)⟩
    show (Fml.swInstV k vs φ).map _ = _
    rw [he]; rfl
  | allocAll x R φ ih =>
    intro _ e σ hn
    simp only [Fml.swPrefix] at e
    split at e
    · rename_i hR
      subst hR
      obtain ⟨φ₁, hφ, rfl⟩ := Option.map_eq_some_iff.1 e
      have : ∃ v, ¬ holds (σ.push (t := .val .uint) v) φ₁ := Classical.byContradiction fun hc =>
        hn fun v => Classical.byContradiction fun hv => hc ⟨v, hv⟩
      obtain ⟨v, hv⟩ := this
      obtain ⟨vs, φv, hl, he, hnv⟩ := ih hφ _ hv
      refine ⟨v :: vs, .all x .uint (.imp (.eq (.pvV .here) (.app0 (.lit v))) φv),
        by simp only [List.length_cons, Fml.allocCount, hl], ?_, fun ha => hnv (ha v rfl)⟩
      simp only [Fml.swInstV, if_true, he, Option.map_some]
    · cases e
  | tt | eq | wellFormed | not | and | imp | upd =>
    intro _ e σ hn
    exact ⟨[], _, rfl, e, hn⟩
  | modal | havoc | bind | anon | grow => intro _ e; cases e

/-! ## The instances at fixed and at free words, related -/

/-- The levels of the prefix's fresh strings are `V`'s, of its other
binders not, and the body's context is past them all. -/
def _root_.Solidity.Fml.prefixOK (V : List Nat) : {Γ : Ctx} → Fml C Γ → Bool
  | Γ, .all _ _ φ => !V.contains Γ.length && Fml.prefixOK V φ
  | Γ, .allocAll _ _ φ => V.contains Γ.length && Fml.prefixOK V φ
  | Γ, .tt | Γ, .eq .. | Γ, .wellFormed _ | Γ, .not _ | Γ, .and .. | Γ, .imp .. | Γ, .upd ..
  | Γ, .modal .. | Γ, .havoc _ | Γ, .bind .. | Γ, .anon .. | Γ, .grow _ => V.all (· < Γ.length)

/-- The swapped leaf is in the relabeling fragment. -/
def _root_.Solidity.Fml.swRL (k : HashKind) (V : List Nat) (K : List Name) {Γ : Ctx}
    (φ : Fml C Γ) : Bool :=
  (φ.swPrefix k).any (·.rl V K)

/-- The fixed words of an instance and the free ones `ρ` sends them to. -/
inductive WordPairs (ρ : PrimTy.uint.Denote → PrimTy.uint.Denote) (Cs : List PrimTy.uint.Denote) :
    List PrimTy.uint.Denote → List PrimTy.uint.Denote → Prop where
  | nil : WordPairs ρ Cs [] []
  | cons {v c : PrimTy.uint.Denote} {vs cs : List PrimTy.uint.Denote} :
      c ∈ Cs → ρ c = v → WordPairs ρ Cs vs cs → WordPairs ρ Cs (v :: vs) (c :: cs)

section Transfer

variable {ρ : PrimTy.uint.Denote → PrimTy.uint.Denote} {Cs : List PrimTy.uint.Denote}
  {V : List Nat} {K : List Name}

theorem RelRL.pushN {Γ : Ctx} {τ'' τ' : State C Γ} (h : RelRL ρ Cs V K τ'' τ')
    (hn : V.contains Γ.length = false) {p : PrimTy} (v : p.Denote) :
    RelRL ρ Cs V K (τ''.push (t := .val p) v) (τ'.push (t := .val p) v) := by
  refine ⟨h.glob, h.stK, h.stO, fun {t} i hi => ?_, fun i hi => ?_, fun {t} i hi => ?_, h.inj⟩
  · cases i with
    | here => rw [Idx.level_here, hn] at hi; cases hi
    | there j => rw [Idx.level_there] at hi; exact h.locT j hi
  · cases i with
    | here => rw [Idx.level_here, hn] at hi; cases hi
    | there j => rw [Idx.level_there] at hi; exact h.locV j hi
  · cases i with
    | here => rfl
    | there j => rw [Idx.level_there] at hi; exact h.locO j hi

theorem RelRL.pushV {Γ : Ctx} {τ'' τ' : State C Γ} (h : RelRL ρ Cs V K τ'' τ')
    (hn : V.contains Γ.length = true) {c v : PrimTy.uint.Denote} (hc : c ∈ Cs) (hρ : ρ c = v) :
    RelRL ρ Cs V K (τ''.push (t := .val .uint) c) (τ'.push (t := .val .uint) v) := by
  refine ⟨h.glob, h.stK, h.stO, fun {t} i hi => ?_, fun i hi => ?_, fun {t} i hi => ?_, h.inj⟩
  · cases i with
    | here => rfl
    | there j => rw [Idx.level_there] at hi; exact h.locT j hi
  · cases i with
    | here => exact ⟨hρ, hc⟩
    | there j => rw [Idx.level_there] at hi; exact h.locV j hi
  · cases i with
    | here => rw [Idx.level_here, hn] at hi; cases hi
    | there j => rw [Idx.level_there] at hi; exact h.locO j hi

/-- **The instance at the fixed words, relabeled, reads as the instance at
the free ones.** -/
theorem _root_.Solidity.Fml.swInstV_transfer (hK : KTyped C K) (k : HashKind) {Γ : Ctx}
    (φ : Fml C Γ) : ∀ (vs cs : List PrimTy.uint.Denote) {φv φc : Fml C (Ctx.sw Γ)},
      φ.swInstV k vs = some φv → φ.swInstV k cs = some φc →
      WordPairs ρ Cs vs cs →
      φ.swRL k V K = true → φ.prefixOK V = true →
      ∀ τ'' τ' : State C (Ctx.sw Γ), RelRL ρ Cs V K τ'' τ' → holds τ'' φc → holds τ' φv := by
  induction φ with
  | all x p φ ih =>
    intro vs cs _ _ ev ec hvc hrl hpre τ'' τ' h hc
    obtain ⟨φv, hv, rfl⟩ := Option.map_eq_some_iff.1 ev
    obtain ⟨φc, hc', rfl⟩ := Option.map_eq_some_iff.1 ec
    simp only [Fml.prefixOK, Bool.and_eq_true, Bool.not_eq_true'] at hpre
    have hrl' : φ.swRL k V K = true := by
      simp only [Fml.swRL, Fml.swPrefix] at hrl ⊢
      cases hp : φ.swPrefix k with
      | none => rw [hp] at hrl; cases hrl
      | some φ' => rw [hp] at hrl; exact hrl
    exact fun v => ih vs cs hv hc' hvc hrl' hpre.2 _ _ (h.pushN (by rw [List.length_map]; exact hpre.1) v) (hc v)
  | allocAll x R φ ih =>
    intro vs cs _ _ ev ec hvc hrl hpre τ'' τ' h hc
    simp only [Fml.prefixOK, Bool.and_eq_true] at hpre
    cases hvc with
    | nil => cases ev
    | cons hc0 hρ0 hvc =>
      rename_i v c vs cs
      simp only [Fml.swInstV] at ev ec
      split at ev
      · rw [if_pos (by assumption)] at ec
        obtain ⟨φv, hv, rfl⟩ := Option.map_eq_some_iff.1 ev
        obtain ⟨φc, hc', rfl⟩ := Option.map_eq_some_iff.1 ec
        intro w hw
        have hw' : w = v := Option.some.inj hw
        subst hw'
        have hrl' : φ.swRL k V K = true := by
          simp only [Fml.swRL, Fml.swPrefix] at hrl ⊢
          rw [if_pos (by assumption)] at hrl
          cases hp : φ.swPrefix k with
          | none => rw [hp] at hrl; cases hrl
          | some φ' => rw [hp] at hrl; exact hrl
        exact ih vs cs hv hc' hvc hrl' hpre.2 _ _ (h.pushV (by rw [List.length_map]; exact hpre.1) hc0 hρ0) (hc c rfl)
      · cases ev
  | tt | eq | wellFormed | not | and | imp | upd =>
    intro vs cs _ _ ev ec _ hrl hpre τ'' τ' h hc
    have e : _ = _ := ev.symm.trans ec
    cases e
    have ev' := ev
    simp only [Fml.swInstV] at ev'
    simp only [Fml.swRL, Fml.swPrefix, ev', Option.any_some] at hrl
    simp only [Fml.prefixOK, List.all_eq_true, decide_eq_true_eq] at hpre
    exact (Fml.rl_holds hK _ hrl τ'' τ' (fun l hl => by rw [List.length_map]; exact hpre l hl) h).1 hc
  | modal | havoc | bind | anon | grow => intro _ _ _ _ ev; cases ev

end Transfer


/-! ## The classes of the free words -/

section Classes

/-- The classes of `n` strings, each a list of class numbers: the first
string in class `0`, each next in a class already used or in the next new
one (restricted growth strings). -/
def rgsFrom : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, m => (List.range (m + 1)).flatMap fun c => (rgsFrom n (max m (c + 1))).map (c :: ·)

/-- The classes of `n` strings. -/
def rgs (n : Nat) : List (List Nat) := rgsFrom n 0

/-- A word of the swapped leaf. -/
abbrev HWord := PrimTy.uint.Denote

/-- The position of `v` in `reps`. -/
def posOf (v : HWord) : List HWord → Nat
  | [] => 0
  | w :: ws => if v = w then 0 else posOf v ws + 1

theorem posOf_lt {v : HWord} : {reps : List HWord} → v ∈ reps → posOf v reps < reps.length
  | [], h => absurd h List.not_mem_nil
  | w :: ws, h => by
    unfold posOf
    split
    · simp only [List.length_cons]; omega
    · rename_i hne
      have : v ∈ ws := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd e hne
        · exact e
      have := posOf_lt this
      simp only [List.length_cons]; omega

theorem posOf_append {v : HWord} (l : List HWord) : {reps : List HWord} → v ∈ reps →
    posOf v (reps ++ l) = posOf v reps
  | [], h => absurd h List.not_mem_nil
  | w :: ws, h => by
    simp only [List.cons_append, posOf]
    split
    · rfl
    · rename_i hne
      have : v ∈ ws := by
        rcases List.mem_cons.1 h with e | e
        · exact absurd e hne
        · exact e
      rw [posOf_append l this]

theorem posOf_append_self {v : HWord} : {reps : List HWord} → v ∉ reps →
    posOf v (reps ++ [v]) = reps.length
  | [], _ => by simp [posOf]
  | w :: ws, h => by
    simp only [List.cons_append, posOf, List.length_cons]
    rw [if_neg (fun e => h (by rw [e]; exact List.mem_cons_self ..)),
      posOf_append_self (fun hm => h (List.mem_cons_of_mem _ hm))]

theorem posOf_inj {v w : HWord} : {reps : List HWord} → v ∈ reps → w ∈ reps →
    posOf v reps = posOf w reps → v = w
  | [], h, _, _ => absurd h List.not_mem_nil
  | u :: us, hv, hw, e => by
    unfold posOf at e
    by_cases hvu : v = u
    · by_cases hwu : w = u
      · exact hvu.trans hwu.symm
      · rw [if_pos hvu, if_neg hwu] at e; cases e
    · by_cases hwu : w = u
      · rw [if_neg hvu, if_pos hwu] at e; cases e
      · rw [if_neg hvu, if_neg hwu] at e
        have hv' : v ∈ us := (List.mem_cons.1 hv).resolve_left hvu
        have hw' : w ∈ us := (List.mem_cons.1 hw).resolve_left hwu
        exact posOf_inj hv' hw' (Nat.succ.inj e)

/-- The class of each word, in order: its first word's position among the
classes seen. -/
def classesAux : List HWord → List HWord → List Nat
  | _, [] => []
  | reps, v :: vs =>
    if v ∈ reps then posOf v reps :: classesAux reps vs
    else reps.length :: classesAux (reps ++ [v]) vs

/-- The classes' first words. -/
def repsAux : List HWord → List HWord → List HWord
  | reps, [] => reps
  | reps, v :: vs => if v ∈ reps then repsAux reps vs else repsAux (reps ++ [v]) vs

/-- The classes of a list of words. -/
def classesOf (vs : List HWord) : List Nat := classesAux [] vs

theorem classesAux_mem : (vs reps : List HWord) →
    classesAux reps vs ∈ rgsFrom vs.length reps.length
  | [], _ => by simp only [classesAux, List.length_nil, rgsFrom, List.mem_singleton]
  | v :: vs, reps => by
    simp only [classesAux, List.length_cons, rgsFrom, List.mem_flatMap, List.mem_range,
      List.mem_map]
    split
    · rename_i hv
      have hlt := posOf_lt hv
      refine ⟨posOf v reps, by omega, _, ?_, rfl⟩
      rw [show max reps.length (posOf v reps + 1) = reps.length by omega]
      exact classesAux_mem vs reps
    · refine ⟨reps.length, by omega, _, ?_, rfl⟩
      rw [show max reps.length (reps.length + 1) = (reps ++ [v]).length by
        simp only [List.length_append, List.length_singleton]; omega]
      exact classesAux_mem vs (reps ++ [v])

theorem classesOf_mem (vs : List HWord) : classesOf vs ∈ rgs vs.length :=
  classesAux_mem vs []

theorem repsAux_ext : (vs reps : List HWord) → ∃ extra, repsAux reps vs = reps ++ extra
  | [], reps => ⟨[], by simp only [repsAux, List.append_nil]⟩
  | v :: vs, reps => by
    simp only [repsAux]
    split
    · exact repsAux_ext vs reps
    · obtain ⟨e, he⟩ := repsAux_ext vs (reps ++ [v])
      exact ⟨[v] ++ e, by rw [he, List.append_assoc]⟩

theorem repsAux_length : (vs reps : List HWord) → (repsAux reps vs).length ≤ reps.length + vs.length
  | [], reps => by simp only [repsAux, List.length_nil, Nat.add_zero, Nat.le_refl]
  | v :: vs, reps => by
    simp only [repsAux, List.length_cons]
    split
    · have := repsAux_length vs reps; omega
    · have := repsAux_length vs (reps ++ [v])
      simp only [List.length_append, List.length_singleton] at this; omega

/-- Each word's class is its position among the classes' first words. -/
theorem classesAux_zip : (vs reps : List HWord) → ∀ p ∈ vs.zip (classesAux reps vs),
    p.1 ∈ repsAux reps vs ∧ p.2 = posOf p.1 (repsAux reps vs)
  | [], _, p, hp => by simp only [classesAux, List.zip_nil_left, List.not_mem_nil] at hp
  | v :: vs, reps, p, hp => by
    simp only [classesAux, repsAux] at hp ⊢
    split at hp
    · rename_i hv
      rw [if_pos hv]
      rcases List.mem_cons.1 (by simpa only [List.zip_cons_cons] using hp) with e | e
      · subst e
        obtain ⟨ex, hex⟩ := repsAux_ext vs reps
        rw [hex]
        exact ⟨List.mem_append_left _ hv, (posOf_append ex hv).symm⟩
      · exact classesAux_zip vs reps p e
    · rename_i hv
      rw [if_neg hv]
      rcases List.mem_cons.1 (by simpa only [List.zip_cons_cons] using hp) with e | e
      · subst e
        obtain ⟨ex, hex⟩ := repsAux_ext vs (reps ++ [v])
        rw [hex]
        refine ⟨List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)), ?_⟩
        rw [posOf_append ex (List.mem_append_right _ (List.mem_singleton_self _)),
          posOf_append_self hv]
      · exact classesAux_zip vs (reps ++ [v]) p e

theorem classesAux_length : (vs reps : List HWord) → (classesAux reps vs).length = vs.length
  | [], _ => rfl
  | v :: vs, reps => by
    simp only [classesAux, List.length_cons]
    split <;> simp only [List.length_cons, classesAux_length]

end Classes

/-! ## A storage relabeled -/

section Realize

theorem Storage.find_key_some (st : Storage C) (r : Name)
    (hr : C.rootType r = some (.ref (.mapping .uint (.prim .uint)))) (y : HWord) :
    st.find ⟨r, hr, .key y .nil⟩ =
      some (.prim (SVal.wordOf (st.find ⟨r, hr, .key y .nil⟩))) := by
  show (st.get hr).find (.key y .nil) = some (.prim (SVal.wordOf ((st.get hr).find (.key y .nil))))
  rw [SVal.find_eq_findM]
  generalize st.get hr = m
  cases m with
  | map es d =>
    simp only [SVal.findM]
    split
    · rename_i x _
      cases x with
      | prim w => rfl
    · cases d with
      | prim w => rfl

/-- Words written at keys of one root. -/
theorem Storage.writeKeys (r : Name) (hr : C.rootType r = some (.ref (.mapping .uint (.prim .uint))))
    (f : HWord → HWord) : ∀ (L : List HWord) (st : Storage C), ∃ st₁ : Storage C,
      (∀ y, st₁.find ⟨r, hr, .key y .nil⟩ =
        if y ∈ L then some (.prim (f y)) else st.find ⟨r, hr, .key y .nil⟩) ∧
      (∀ (r₂ : Name) {T : Ty} (h₂ : C.rootType r₂ = some T), r ≠ r₂ → st₁.get h₂ = st.get h₂)
  | [], st => ⟨st, fun y => by simp only [List.not_mem_nil, if_false], fun _ _ _ _ => rfl⟩
  | x :: L, st => by
    obtain ⟨st₁, hf₁, hg₁⟩ := Storage.writeKeys r hr f L st
    obtain ⟨st₂, -, hf₂, hg₂⟩ := Storage.write_key st₁ r hr x (f x)
    refine ⟨st₂, fun y => ?_, fun r₂ T h₂ hne => (hg₂ r₂ h₂ hne).trans (hg₁ r₂ h₂ hne)⟩
    rw [hf₂, hf₁]
    by_cases hy : y = x
    · subst hy; simp only [if_true, List.mem_cons_self]
    · simp only [hy, if_false, List.mem_cons, false_or]

/-- Words written at keys of several roots. -/
theorem Storage.writeRoots (L : List HWord) (F : (r : Name) →
    C.rootType r = some (.ref (.mapping .uint (.prim .uint))) → HWord → HWord) :
    ∀ (Ks : List Name), (∀ r ∈ Ks, C.rootType r = some (.ref (.mapping .uint (.prim .uint)))) →
      ∀ st : Storage C, ∃ st₁ : Storage C,
      (∀ r ∈ Ks, ∀ (hr : C.rootType r = some (.ref (.mapping .uint (.prim .uint)))) y,
        st₁.find ⟨r, hr, .key y .nil⟩ =
          if y ∈ L then some (.prim (F r hr y)) else st.find ⟨r, hr, .key y .nil⟩) ∧
      (∀ (r₂ : Name) {T : Ty} (h₂ : C.rootType r₂ = some T), r₂ ∉ Ks → st₁.get h₂ = st.get h₂)
  | [], _, st => ⟨st, fun _ h => absurd h List.not_mem_nil, fun _ _ _ _ => rfl⟩
  | r₀ :: Ks, hKs, st => by
    obtain ⟨st₁, hf₁, hg₁⟩ := Storage.writeRoots L F Ks
      (fun r hr => hKs r (List.mem_cons_of_mem _ hr)) st
    have hr₀ := hKs r₀ (List.mem_cons_self ..)
    obtain ⟨st₂, hf₂, hg₂⟩ := Storage.writeKeys r₀ hr₀ (F r₀ hr₀) L st₁
    refine ⟨st₂, fun r hm hr y => ?_, fun r₂ T h₂ hn => ?_⟩
    · by_cases e : r = r₀
      · subst e
        rw [hf₂ y]
        split
        · rfl
        · rename_i hy
          by_cases hk : r ∈ Ks
          · rw [hf₁ r hk hr₀ y, if_neg hy]
          · rw [show st₁.find ⟨r, hr₀, .key y .nil⟩ = st.find ⟨r, hr₀, .key y .nil⟩ from by
              show (st₁.get hr₀).find _ = (st.get hr₀).find _
              rw [hg₁ r hr₀ hk]]
      · have hk : r ∈ Ks := (List.mem_cons.1 hm).resolve_left e
        rw [show st₂.find ⟨r, hr, .key y .nil⟩ = st₁.find ⟨r, hr, .key y .nil⟩ from by
          show (st₂.get hr).find _ = (st₁.get hr).find _
          rw [hg₂ r hr (Ne.symm e)]]
        exact hf₁ r hk hr y
    · have hne : r₀ ≠ r₂ := fun e => hn (e ▸ List.mem_cons_self ..)
      have hk : r₂ ∉ Ks := fun hk => hn (List.mem_cons_of_mem _ hk)
      rw [hg₂ r₂ h₂ hne, hg₁ r₂ h₂ hk]

/-- **A state relabeled into one with the fixed words' keys**: each root of
`K` holds at a fixed key `x` what it held at `ρ x`. -/
theorem relabel_state {K : List Name} (hK : KTyped C K) (ρ : HWord → HWord) (Cs : List HWord)
    (hinj : ∀ x ∈ Cs, ∀ y ∈ Cs, ρ x = ρ y → x = y) (V : List Nat) (σ' : State C []) :
    ∃ σ'' : State C [], RelRL ρ Cs V K σ'' σ' := by
  obtain ⟨st, hf, hg⟩ := Storage.writeRoots Cs
    (fun r hr y => SVal.wordOf (σ'.storage.find ⟨r, hr, .key (ρ y) .nil⟩)) K hK σ'.storage
  refine ⟨σ'.withStorage st, RelRL.mk ⟨rfl, rfl, rfl⟩ ?_ (fun r _ hr hn => hg r hr hn)
    (fun i => (nomatch i)) (fun i => (nomatch i)) (fun i => (nomatch i)) hinj⟩
  intro r hm hr x hx
  show st.find _ = σ'.storage.find _
  rw [hf r hm hr x, if_pos hx, ← Storage.find_key_some]

end Realize

/-! ## Completeness -/

section Complete

theorem _root_.Solidity.Fml.swInstV_length (k : HashKind) {Γ : Ctx} (φ : Fml C Γ) :
    ∀ (vs ws : List HWord) {φv : Fml C (Ctx.sw Γ)}, φ.swInstV k vs = some φv →
      ws.length = vs.length → ∃ φw, φ.swInstV k ws = some φw := by
  induction φ with
  | all x p φ ih =>
    intro vs ws _ e hl
    obtain ⟨φ₁, h₁, rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨φ₂, h₂⟩ := ih vs ws h₁ hl
    exact ⟨.all x p φ₂, by simp only [Fml.swInstV, h₂, Option.map_some]⟩
  | allocAll x R φ ih =>
    intro vs ws _ e hl
    cases vs with
    | nil => cases e
    | cons v vs =>
      cases ws with
      | nil => cases hl
      | cons w ws =>
        simp only [Fml.swInstV] at e ⊢
        split at e
        · rename_i hR
          obtain ⟨φ₁, h₁, rfl⟩ := Option.map_eq_some_iff.1 e
          obtain ⟨φ₂, h₂⟩ := ih vs ws h₁ (by simpa only [List.length_cons, Nat.add_right_cancel_iff]
            using hl)
          exact ⟨_, by rw [if_pos hR, h₂]; rfl⟩
        · cases e
  | tt | eq | wellFormed | not | and | imp | upd => intro _ _ _ e _; exact ⟨_, e⟩
  | modal | havoc | bind | anon | grow => intro _ _ _ e; cases e

/-- **Completeness of the refutations**: where the swapped leaf is not
valid, an instance of the leaf at some classes of its strings is not. -/
theorem _root_.Solidity.Fml.swPrefix_complete {k : HashKind} (hk : k ≠ .ecrecover) {φ : Fml C []}
    {φ' : Fml C []} (e : φ.swPrefix k = some φ') {V : List Nat} {K : List Name}
    (hK : KTyped C K) (hrl : φ.swRL k V K = true) (hpre : φ.prefixOK V = true)
    (hn : φ.allocCount ≤ famBound) (hnv : ¬ Fml.Valid φ') :
    ∃ cs ∈ rgs φ.allocCount, ∃ φf, φ.swInst k cs = some φf ∧ ¬ Fml.Valid φf := by
  have : ∃ σ', ¬ holds σ' φ' := Classical.byContradiction fun hc =>
    hnv fun σ => Classical.byContradiction fun hσ => hc ⟨σ, hσ⟩
  obtain ⟨σ', hσ'⟩ := this
  obtain ⟨vs, φv, hl, ev, hnvv⟩ := Fml.swPrefix_insts k φ e σ' hσ'
  let cs := classesOf vs
  let F := repsAux [] vs
  have hcs : cs ∈ rgs φ.allocCount := hl ▸ classesOf_mem vs
  have hz := classesAux_zip vs []
  have hFlen : F.length ≤ famBound := by
    have := repsAux_length vs []
    simp only [List.length_nil, Nat.zero_add] at this
    show (repsAux [] vs).length ≤ famBound
    omega
  have hok := famOK_bound k hk
  -- `ρ` sends the hash of a class's number to the class's first word
  let ρ : HWord → HWord := fun x => (F.find? fun w => famHash k (posOf w F) == x).getD x
  have hρ : ∀ v ∈ F, ρ (famHash k (posOf v F)) = v := by
    intro v hv
    show (F.find? fun w => famHash k (posOf w F) == famHash k (posOf v F)).getD _ = v
    cases hf : F.find? fun w => famHash k (posOf w F) == famHash k (posOf v F) with
    | none =>
      have := List.find?_eq_none.1 hf v hv
      simp only [beq_self_eq_true, not_true_eq_false] at this
    | some w =>
      have hw := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [beq_iff_eq] at hp
      exact posOf_inj hw hv (famOK_inj hok (Nat.lt_of_lt_of_le (posOf_lt hw) hFlen)
        (Nat.lt_of_lt_of_le (posOf_lt hv) hFlen) hp)
  let Cs := cs.map (famHash k)
  have hCs : ∀ x ∈ Cs, ∃ v ∈ F, x = famHash k (posOf v F) := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    have hlen : vs.length = cs.length := (classesAux_length vs []).symm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hi' : i < vs.length := hlen ▸ hi
    have hm : (vs[i], cs[i]) ∈ vs.zip cs := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp only [List.length_zip]; omega, by simp only [List.getElem_zip]⟩
    obtain ⟨hv, hc'⟩ := hz _ hm
    exact ⟨vs[i], hv, by simp only at hc'; rw [hc']⟩
  have hinj : ∀ x ∈ Cs, ∀ y ∈ Cs, ρ x = ρ y → x = y := by
    intro x hx y hy hxy
    obtain ⟨v, hv, rfl⟩ := hCs x hx
    obtain ⟨w, hw, rfl⟩ := hCs y hy
    rw [hρ v hv, hρ w hw] at hxy
    rw [hxy]
  -- the instance at the fixed words
  obtain ⟨φc, ec⟩ := Fml.swInstV_length k φ vs Cs ev (by
    simp only [Cs, List.length_map, cs, classesOf, classesAux_length])
  have hpairs : ∀ (ws : List HWord) (ds : List Nat), (∀ p ∈ ws.zip ds, p.1 ∈ F ∧ p.2 = posOf p.1 F) →
      ws.length = ds.length → (∀ d ∈ ds, famHash k d ∈ Cs) →
      WordPairs ρ Cs ws (ds.map (famHash k)) := by
    intro ws
    induction ws with
    | nil => intro ds _ hl _; cases ds with | nil => exact .nil | cons => cases hl
    | cons w ws ih =>
      intro ds hz' hl hmem
      cases ds with
      | nil => cases hl
      | cons d ds =>
        have h0 := hz' (w, d) (List.mem_cons_self ..)
        simp only at h0
        refine .cons (hmem d (List.mem_cons_self ..)) ?_ (ih ds (fun p hp => hz' p
          (List.mem_cons_of_mem _ hp)) (by simpa only [List.length_cons, Nat.add_right_cancel_iff]
            using hl) (fun d' hd => hmem d' (List.mem_cons_of_mem _ hd)))
        rw [h0.2]
        exact hρ w h0.1
  have hwp : WordPairs ρ Cs vs Cs := hpairs vs cs hz (classesAux_length vs []).symm
    (fun d hd => List.mem_map_of_mem hd)
  obtain ⟨σ'', hrel⟩ := relabel_state hK ρ Cs hinj V σ'
  refine ⟨cs, hcs, φc, by rw [Fml.swInst_eq]; exact ec, fun hv => hnvv ?_⟩
  exact Fml.swInstV_transfer hK k φ vs Cs ev ec hwp hrl hpre σ'' σ' hrel (hv σ'')

end Complete

end Solidity.Decide
