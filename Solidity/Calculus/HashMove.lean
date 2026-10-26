import Solidity.Calculus.HashKinds3
import Solidity.Calculus.LeafTotality

/-!
# Strings the first kind does not hash, moved (M7, plan step 7: feature 29)

`Fml.tk` (`Calculus/HashKinds.lean`) links the second kind's words to the
first kind's by the premise, a pair of strings at a time.  A string of the
second kind the first kind hashes nowhere has no first-kind hash for the
premise to read, so the decision's reading links no pair of it
(`Fml.tkKeep`); its swapped word is then read nowhere.  Completeness
(`Fml.tk_complete`) relabels the second kind's words along the classes the
first kind's words make, which reads the whole link.  So a refutation of
the decision's reading is first *moved*: each such word set, by
`linkChoice` with the two kinds' roles swapped, to follow its extra word's
class (`Fml.tkBody_move`, through the prefix `Fml.tk_move`), one level at a
time (`Moved`), each change framed by `Fml.rl_holds` at that one level
(`holds_setLocal_frame`).  The moved state refutes the reading with every
pair linked, which `Fml.tk_complete` takes (`Fml.tk_complete_move`).
-/

namespace Solidity.Decide

variable {C : Contract} {N : Nat}

/-! ## States with words moved -/

/-- `τ''` is `τ` with word locals at levels of `D` set, one at a time. -/
inductive Moved (D : List Nat) {Γ : Ctx} (τ : State C Γ) : State C Γ → Prop
  | refl : Moved D τ τ
  | set {τ' : State C Γ} : Moved D τ τ' → (i : Idx Γ (.val .uint)) → i.level ∈ D →
      (v : PrimTy.uint.Denote) → Moved D τ (τ'.setLocal i v)

theorem Moved.push_inv {D : List Nat} {Γ : Ctx} {t : LTy} {τ : State C Γ} {v : t.TDenote C τ.H}
    {τ'' : State C (t :: Γ)} (h : Moved D (τ.push v) τ'') :
    ∃ (σ'' : State C Γ) (v'' : t.TDenote C σ''.H), Moved D τ σ'' ∧ τ'' = σ''.push v'' := by
  induction h with
  | refl => exact ⟨τ, v, .refl, rfl⟩
  | set _ i hi w ih =>
    obtain ⟨σ'', v'', hm, rfl⟩ := ih
    cases i with
    | here => exact ⟨σ'', w, hm, rfl⟩
    | there j =>
      refine ⟨σ''.setLocal j w, v'', .set hm j ?_ w, rfl⟩
      rwa [Idx.level_there] at hi

/-! ## One level framed -/

theorem Idx.level_lt {Γ : Ctx} {t : LTy} (i : Idx Γ t) : i.level < Γ.length := by
  have := i.toNat_lt
  unfold Idx.level
  omega

theorem Idx.toNat_of_level {Γ : Ctx} {t u : LTy} {i : Idx Γ t} {j : Idx Γ u} (h : i.level = j.level) :
    i.toNat = j.toNat := by
  have := i.toNat_lt
  have := j.toNat_lt
  unfold Idx.level at h
  omega

/-- **A formula that reads no word at level `l`** (`Fml.rl` at `[l]` and no
keyed root) holds alike with that word set. -/
theorem holds_setLocal_frame {Γ : Ctx} (F : Fml C Γ) (i : Idx Γ (.val .uint))
    (hF : F.rl [i.level] [] = true) (σ : State C Γ) (v : PrimTy.uint.Denote) :
    holds (σ.setLocal i v) F ↔ holds σ F := by
  have hK : KTyped C [] := fun _ h => absurd h List.not_mem_nil
  refine Fml.rl_holds (ρ := fun _ => σ.getV i) (Cs := [v]) hK F hF _ _ (fun l hl => ?_) ?_
  · rw [List.mem_singleton] at hl
    subst hl
    exact Idx.level_lt i
  refine ⟨⟨rfl, rfl, rfl⟩, fun _ h => absurd h List.not_mem_nil, fun _ _ _ _ => rfl,
    fun {t} j hj => ?_, fun j hj => ?_, fun {t} j hj => ?_, fun x hx y hy _ => ?_⟩
  · simp only [List.contains_iff_mem, List.mem_singleton] at hj
    exact (Idx.ty_eq_of_toNat (Idx.toNat_of_level hj.symm)).symm
  · simp only [List.contains_iff_mem, List.mem_singleton] at hj
    obtain rfl := Idx.toNat_inj i j (Idx.toNat_of_level hj.symm)
    refine ⟨rfl, ?_⟩
    rw [State.getV_setLocal_same]
    exact List.mem_singleton_self _
  · have hne : i.toNat ≠ j.toNat := fun e => by
      have : j.level = i.level := by unfold Idx.level; rw [e]
      rw [this] at hj
      simp only [List.contains_cons, beq_self_eq_true, Bool.true_or, Bool.true_eq_false] at hj
    exact State.getV_setLocal_ne _ _ _ hne v
  · rw [List.mem_singleton.1 hx, List.mem_singleton.1 hy]

/-! ## Several levels set -/

/-- The word locals `ps` set, the first last. -/
def setMany {Γ : Ctx} (τ : State C Γ) : List (Idx Γ (.val .uint) × PrimTy.uint.Denote) → State C Γ
  | [] => τ
  | p :: ps => (setMany τ ps).setLocal p.1 p.2

theorem moved_setMany {D : List Nat} {Γ : Ctx} (τ : State C Γ) :
    (ps : List (Idx Γ (.val .uint) × PrimTy.uint.Denote)) → (∀ p ∈ ps, p.1.level ∈ D) →
      Moved D τ (setMany τ ps)
  | [], _ => .refl
  | p :: ps, h =>
    .set (moved_setMany τ ps fun q hq => h q (List.mem_cons_of_mem _ hq)) p.1 (h p List.mem_cons_self) p.2

theorem getV_setMany_off {Γ : Ctx} (τ : State C Γ) (j : Idx Γ (.val .uint)) :
    (ps : List (Idx Γ (.val .uint) × PrimTy.uint.Denote)) → (∀ p ∈ ps, p.1.toNat ≠ j.toNat) →
      (setMany τ ps).getV j = τ.getV j
  | [], _ => rfl
  | p :: ps, h => by
    show ((setMany τ ps).setLocal p.1 p.2).getV j = _
    rw [State.getV_setLocal_ne _ _ _ (h p List.mem_cons_self)]
    exact getV_setMany_off τ j ps fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem getV_setMany_on {Γ : Ctx} (τ : State C Γ) (j : Idx Γ (.val .uint)) (v : PrimTy.uint.Denote) :
    (ps : List (Idx Γ (.val .uint) × PrimTy.uint.Denote)) → (j, v) ∈ ps →
      (∀ p ∈ ps, p.1.toNat = j.toNat → p = (j, v)) → (setMany τ ps).getV j = v
  | [], h, _ => absurd h List.not_mem_nil
  | p :: ps, h, hu => by
    show ((setMany τ ps).setLocal p.1 p.2).getV j = _
    by_cases hp : p.1.toNat = j.toNat
    · obtain rfl := hu p List.mem_cons_self hp
      exact State.getV_setLocal_same _ _ _
    · rw [State.getV_setLocal_ne _ _ _ hp]
      rcases List.mem_cons.1 h with h | h
      · rw [← h] at hp; exact absurd rfl hp
      · exact getV_setMany_on τ j v ps h fun q hq => hu q (List.mem_cons_of_mem _ hq)

theorem holds_setMany_frame {Γ : Ctx} (F : Fml C Γ) (σ : State C Γ) :
    (ps : List (Idx Γ (.val .uint) × PrimTy.uint.Denote)) → (∀ p ∈ ps, F.rl [p.1.level] [] = true) →
      (holds (setMany σ ps) F ↔ holds σ F)
  | [], _ => Iff.rfl
  | p :: ps, h => by
    show holds ((setMany σ ps).setLocal p.1 p.2) F ↔ _
    rw [holds_setLocal_frame F p.1 (h p List.mem_cons_self)]
    exact holds_setMany_frame F σ ps fun q hq => h q (List.mem_cons_of_mem _ hq)

/-! ## Past new binders -/

section Up

variable {Γ : Ctx}

/-- A position of the swapped context past `m` new binders. -/
def swUp {t : LTy} : (m : Nat) → Idx (Ctx.sw Γ) t → Idx (Ctx.sw (List.replicate m (.val .uint) ++ Γ)) t
  | 0, j => j
  | m + 1, j => .there (swUp m j)

theorem swUp_level {t : LTy} : (m : Nat) → (j : Idx (Ctx.sw Γ) t) → (swUp m j).level = j.level
  | 0, _ => rfl
  | m + 1, j => by
    show (Idx.there (swUp m j) : Idx (Ctx.sw (List.replicate (m + 1) (.val .uint) ++ Γ)) t).level = _
    rw [Idx.level_there, swUp_level m j]

theorem swUp_sw {R : RefTy} (i : Idx Γ (.mem R)) : (m : Nat) → swUp m i.sw = (i.wk (Thin.dropN m)).sw
  | 0 => rfl
  | m + 1 => congrArg Idx.there (swUp_sw i m)

theorem envOfSw_set {H : HTy} (j : Idx (Ctx.sw Γ) (.val .uint)) (v : PrimTy.uint.Denote) :
    (m : Nat) → (es : Fin m → PrimTy.uint.Denote) → (e : TEnv C H (Ctx.sw Γ)) →
      envOfSw m es (TEnv.set j v e) = TEnv.set (swUp m j) v (envOfSw m es e)
  | 0, _, _ => rfl
  | m + 1, es, e => congrArg (Prod.mk (es 0)) (envOfSw_set j v m (fun i => es i.succ) e)

theorem setMany_envOfSw (τ : State C (Ctx.sw Γ)) (m : Nat) (es : Fin m → PrimTy.uint.Denote) :
    (ps : List (Idx (Ctx.sw Γ) (.val .uint) × PrimTy.uint.Denote)) →
      (setMany τ ps).withEnv (envOfSw m es (setMany τ ps).env) =
        setMany (τ.withEnv (envOfSw m es τ.env)) (ps.map fun p => (swUp m p.1, p.2))
  | [] => rfl
  | p :: ps => by
    show ((setMany τ ps).setLocal p.1 p.2).withEnv (envOfSw m es ((setMany τ ps).setLocal p.1 p.2).env) =
      (setMany (τ.withEnv (envOfSw m es τ.env)) (ps.map fun p => (swUp m p.1, p.2))).setLocal (swUp m p.1) p.2
    rw [← setMany_envOfSw τ m es ps]
    show State.withEnv _ (envOfSw m es (TEnv.set p.1 p.2 (setMany τ ps).env)) = _
    rw [envOfSw_set]
    rfl

end Up

/-! ## The fragment of the move -/

/-- **The strings of the second kind the link does not keep**: past one
string, those the first kind does not hash where the premise always reads
them (the first kind hashes them nowhere, `Fml.tkBody`). -/
def _root_.Solidity.Fml.tkDead (k₁ k₂ : HashKind) {Γ : Ctx} (ψ : Fml C Γ) : List Nat :=
  if (ψ.hLevels k₂).eraseDups.length ≤ 1 then [] else
    (ψ.hLevels k₂).eraseDups.filter fun l => !(ψ.topLevels k₁).contains l

/-- **The swapped body reads no word the move sets.** -/
def _root_.Solidity.Fml.tkBodyMove (k₁ k₂ : HashKind) {Γ : Ctx} (ψ : Fml C Γ) : Bool :=
  match ψ.xk k₂ (XMap.extras (ψ.hLevels k₂).eraseDups Γ) with
  | none => false
  | some ψ₂ =>
    match Fml.sw k₁ ψ₂ with
    | none => false
    | some X => (ψ.tkDead k₁ k₂).all fun l => X.rl [l] []

/-- `Fml.tkBodyMove` past the prefix. -/
def _root_.Solidity.Fml.tkMove (k₁ k₂ : HashKind) : {Γ : Ctx} → Fml C Γ → Bool
  | _, .all _ _ φ => Fml.tkMove k₁ k₂ φ
  | _, .allocAll _ _ φ => Fml.tkMove k₁ k₂ φ
  | Γ, .tt => Fml.tkBodyMove k₁ k₂ (C := C) (Γ := Γ) .tt
  | _, .eq a b => Fml.tkBodyMove k₁ k₂ (.eq a b)
  | _, .wellFormed s => Fml.tkBodyMove k₁ k₂ (.wellFormed s)
  | _, .not φ => Fml.tkBodyMove k₁ k₂ (.not φ)
  | _, .and φ ψ => Fml.tkBodyMove k₁ k₂ (.and φ ψ)
  | _, .imp φ ψ => Fml.tkBodyMove k₁ k₂ (.imp φ ψ)
  | _, .upd m U φ => Fml.tkBodyMove k₁ k₂ (.upd m U φ)
  | _, _ => false

/-- `Fml.tkDead` past the prefix. -/
def _root_.Solidity.Fml.tkDeadP (k₁ k₂ : HashKind) : {Γ : Ctx} → Fml C Γ → List Nat
  | _, .all _ _ φ => Fml.tkDeadP k₁ k₂ φ
  | _, .allocAll _ _ φ => Fml.tkDeadP k₁ k₂ φ
  | Γ, .tt => Fml.tkDead k₁ k₂ (C := C) (Γ := Γ) .tt
  | _, .eq a b => Fml.tkDead k₁ k₂ (.eq a b)
  | _, .wellFormed s => Fml.tkDead k₁ k₂ (.wellFormed s)
  | _, .not φ => Fml.tkDead k₁ k₂ (.not φ)
  | _, .and φ ψ => Fml.tkDead k₁ k₂ (.and φ ψ)
  | _, .imp φ ψ => Fml.tkDead k₁ k₂ (.imp φ ψ)
  | _, .upd m U φ => Fml.tkDead k₁ k₂ (.upd m U φ)
  | _, _ => []

section Body

variable {Γ : Ctx}

theorem _root_.Solidity.Fml.tkBody_bound {k₁ k₂ : HashKind} {fix full : Bool} {ψ φ : Fml C Γ}
    (e : ψ.tkBody k₁ k₂ N fix full = some φ) :
    (ψ.hLevels k₂).eraseDups.length * ((ψ.hLevels k₂).eraseDups.length + 1) < 2 ^ 256 := by
  unfold Fml.tkBody at e
  dsimp only at e
  split at e
  · rename_i hcov
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcov
    exact hcov.1.2
  · cases e

theorem _root_.Solidity.Idx.level_sw {t : LTy} (i : Idx Γ t) : i.sw.level = i.level := by
  unfold Idx.level
  rw [Idx.toNat_sw]
  simp only [Ctx.sw, List.length_map]

theorem nodup_getElem_inj {L : List Nat} (h : L.Nodup) {a b : Fin L.length} (e : L[a] = L[b]) : a = b := by
  have hp := List.pairwise_iff_getElem.1 h
  rcases Nat.lt_trichotomy a.1 b.1 with hab | hab | hab
  · exact absurd e (hp a.1 b.1 a.2 b.2 hab)
  · exact Fin.ext hab
  · exact absurd e.symm (hp b.1 a.1 b.2 a.2 hab)

theorem _root_.Solidity.Fml.swPrefix_allN (k : HashKind) (x : Var) :
    (m : Nat) → (F : Fml C (List.replicate m (.val .uint) ++ Γ)) →
      (Fml.allN x m F).swPrefix k = (F.swPrefix k).map (Fml.allNsw x m)
  | 0, F => by simp only [Fml.allN, Fml.allNsw, Option.map_id']
  | m + 1, F => by
    show (Fml.allN x m (.all x .uint F)).swPrefix k = _
    rw [Fml.swPrefix_allN k x m (.all x .uint F)]
    show ((F.swPrefix k).map (Fml.all x .uint)).map (Fml.allNsw x m) = _
    rw [Option.map_map]
    rfl

/-- **The move at the body**: where the reading with every pair linked
holds at every state with the unlinked strings' words moved, the
decision's reading holds. -/
theorem _root_.Solidity.Fml.tkBody_move {k₁ k₂ : HashKind} (ψ : Fml C Γ) {φp φf : Fml C Γ}
    (ep : ψ.tkBody k₁ k₂ N false = some φp) (ef : ψ.tkBody k₁ k₂ N false true = some φf)
    {Bp Bf : Fml C (Ctx.sw Γ)} (sp : Fml.sw k₁ φp = some Bp) (sf : Fml.sw k₁ φf = some Bf)
    (hmv : ψ.tkBodyMove k₁ k₂ = true) (τ : State C (Ctx.sw Γ))
    (H : ∀ τ'', Moved (ψ.tkDead k₁ k₂) τ τ'' → holds τ'' Bf) : holds τ Bp := by
  have hbound := Fml.tkBody_bound ep
  obtain ⟨hstr, ψ₂, hψ₂, rfl⟩ := Fml.tkBody_eq ep
  obtain ⟨-, ψ₂', hψ₂', rfl⟩ := Fml.tkBody_eq ef
  rw [hψ₂] at hψ₂'
  cases hψ₂'
  unfold Fml.tkBodyMove at hmv
  rw [hψ₂] at hmv
  simp only at hmv
  split at hmv
  · cases hmv
  rename_i X hX
  have hfr : ∀ l ∈ ψ.tkDead k₁ k₂, X.rl [l] [] = true := fun l hl => List.all_eq_true.1 hmv l hl
  have hdead : ∀ (d : Fin (ψ.hLevels k₂).eraseDups.length), 1 < (ψ.hLevels k₂).eraseDups.length →
      (ψ.hLevels k₂).eraseDups[d] ∉ ψ.topLevels k₁ → (ψ.hLevels k₂).eraseDups[d] ∈ ψ.tkDead k₁ k₂ := by
    intro d h1 h2
    unfold Fml.tkDead
    rw [if_neg (by omega)]
    grind
  have hnd : (ψ.hLevels k₂).eraseDups.Nodup := List.nodup_eraseDups' _
  simp only [Bool.false_eq_true, ↓reduceIte, Fml.tkKeep] at sp sf
  generalize (ψ.hLevels k₂).eraseDups = L at *
  rw [Fml.sw_allN] at sp sf
  obtain ⟨Bp', hBp', rfl⟩ := Option.map_eq_some_iff.1 sp
  obtain ⟨Bf', hBf', rfl⟩ := Option.map_eq_some_iff.1 sf
  obtain ⟨T, hT, eBp⟩ := Option.bind_eq_some_iff.1 hBp'
  obtain ⟨Bpr, hBpr, rfl⟩ := Option.map_eq_some_iff.1 eBp
  obtain ⟨lp, hlp, eBpr⟩ := Option.bind_eq_some_iff.1 hBpr
  obtain ⟨X', hX', rfl⟩ := Option.map_eq_some_iff.1 eBpr
  rw [hX] at hX'
  cases hX'
  obtain ⟨T', hT', eBf⟩ := Option.bind_eq_some_iff.1 hBf'
  obtain ⟨Bfr, hBfr, rfl⟩ := Option.map_eq_some_iff.1 eBf
  obtain ⟨lf, hlf, eBfr⟩ := Option.bind_eq_some_iff.1 hBfr
  obtain ⟨X'', hX'', rfl⟩ := Option.map_eq_some_iff.1 eBfr
  rw [hX] at hX''
  cases hX''
  cases hT'
  rw [holds_allNsw]
  intro es _ hlinkp
  -- the strings and their words
  have hsome : ∀ d : Fin L.length, (strAt (Γ := Γ) L d).isSome := fun d => hstr _ (List.getElem_mem _)
  let str : Fin L.length → (R : RefTy) × Idx Γ (.mem R) := fun d => (strAt L d).get (hsome d)
  have hstrAt : ∀ d, strAt L d = some (str d) := fun d => (Option.some_get (hsome d)).symm
  have hlev : ∀ d, (str d).2.level = L[d] := fun d => Idx.memAtLevel?_level (hstrAt d)
  have hstrEq : ∀ d {R : RefTy} (i : Idx Γ (.mem R)), strAt L d = some ⟨R, i⟩ → str d = ⟨R, i⟩ :=
    fun d _ _ h => Option.some.inj ((hstrAt d).symm.trans h)
  let w : Fin L.length → PrimTy.uint.Denote := fun d => TEnv.get (str d).2.sw τ.env
  -- the pairs the decision links
  have hlk : ∀ a b : Fin L.length, a < b → L[a] ∈ ψ.topLevels k₁ → L[b] ∈ ψ.topLevels k₁ →
      (w a = w b ↔ es a = es b) := by
    intro a b hab ha hb
    have hm := linkE_mem' (C := C) (k₁ := k₁) (Γ := Γ) (keep := fun l => (ψ.topLevels k₁).contains l) hab
      (List.contains_iff_mem.2 ha) (List.contains_iff_mem.2 hb) (hstrAt a) (hstrAt b)
    have := (sw_conjL_holds _ _ hlp).1 hlinkp _ hm _ (sw_link_elem _ _ _ _)
    rw [holds_wordIff] at this
    simp only [State.withEnv] at this
    rw [get_wk_dropN_sw, get_wk_dropN_sw, get_topIdx_sw, get_topIdx_sw] at this
    exact this
  -- the words moved: those of strings the decision links kept, the others following their extra words
  let Q : Fin L.length → Prop := fun d => L.length ≤ 1 ∨ L[d] ∈ ψ.topLevels k₁
  have hQ : ∀ a b, Q a → Q b → (es a = es b ↔ w a = w b) := by
    intro a b ha hb
    rcases Nat.lt_trichotomy a.1 b.1 with h | h | h
    · have h2 : ¬ L.length ≤ 1 := by have := b.2; omega
      exact (hlk a b h (ha.resolve_left h2) (hb.resolve_left h2)).symm
    · obtain rfl : a = b := Fin.ext h
      exact ⟨fun _ => rfl, fun _ => rfl⟩
    · have h2 : ¬ L.length ≤ 1 := by have := a.2; omega
      have := hlk b a h (hb.resolve_left h2) (ha.resolve_left h2)
      exact ⟨fun e => (this.2 e.symm).symm, fun e => (this.1 e.symm).symm⟩
  classical
  obtain ⟨w', hw'Q, hw'⟩ := linkChoice hbound es w Q hQ
  let ps : List (Idx (Ctx.sw Γ) (.val .uint) × PrimTy.uint.Denote) :=
    ((List.finRange L.length).filter fun d => !decide (Q d)).map fun d => ((str d).2.sw, w' d)
  have hmemps : ∀ p ∈ ps, ∃ d, ¬ Q d ∧ p = ((str d).2.sw, w' d) := by
    intro p hp
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hp
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hd
    exact ⟨d, hd.2, rfl⟩
  have hdlev : ∀ d, ¬ Q d → L[d] ∈ ψ.tkDead k₁ k₂ := by
    intro d hd
    simp only [Q, not_or] at hd
    exact hdead d (by omega) hd.2
  have htoNat : ∀ a b : Fin L.length, ((str a).2.sw).toNat = ((str b).2.sw).toNat → a = b := by
    intro a b h
    rw [Idx.toNat_sw, Idx.toNat_sw] at h
    apply nodup_getElem_inj hnd
    rw [← hlev a, ← hlev b]
    unfold Idx.level
    rw [h]
  have hw'' : ∀ d, TEnv.get (str d).2.sw (setMany τ ps).env = w' d := by
    intro d
    by_cases hQd : Q d
    · have := getV_setMany_off τ (str d).2.sw ps fun p hp => by
        obtain ⟨d', hd', rfl⟩ := hmemps p hp
        intro h
        obtain rfl := htoNat d' d h
        exact hd' hQd
      exact this.trans (hw'Q d hQd).symm
    · refine getV_setMany_on τ (str d).2.sw (w' d) ps ?_ fun p hp hp' => ?_
      · refine List.mem_map.2 ⟨d, ?_, rfl⟩
        simp only [List.mem_filter, mem_finRange', true_and, Bool.not_eq_true',
          decide_eq_false_iff_not]
        exact hQd
      · obtain ⟨d', -, rfl⟩ := hmemps p hp
        obtain rfl := htoNat d' d hp'
        rfl
  have hmoved : Moved (ψ.tkDead k₁ k₂) τ (setMany τ ps) := moved_setMany τ ps fun p hp => by
    obtain ⟨d, hd, rfl⟩ := hmemps p hp
    show (str d).2.sw.level ∈ _
    rw [Idx.level_sw, hlev d]
    exact hdlev d hd
  have hB := (holds_allNsw _ _ _ _).1 (H _ hmoved) es
  -- every pair linked at the moved words
  have hlf' : holds ((setMany τ ps).withEnv (envOfSw L.length es (setMany τ ps).env)) lf := by
    refine (sw_conjL_holds _ _ hlf).2 fun f hf g hg => ?_
    obtain ⟨a, b, -, -, -, R₁, R₂, i, j, ha, hb, rfl⟩ := mem_linkE' hf
    rw [sw_link_elem] at hg
    cases hg
    rw [holds_wordIff]
    simp only [State.withEnv]
    rw [get_wk_dropN_sw, get_wk_dropN_sw, get_topIdx_sw, get_topIdx_sw]
    have ea := hw'' a
    have eb := hw'' b
    rw [hstrEq a i ha] at ea
    rw [hstrEq b j hb] at eb
    rw [ea, eb]
    exact (hw' a b).symm
  have hXm := hB trivial hlf'
  rw [setMany_envOfSw] at hXm
  refine (holds_setMany_frame X _ _ fun p hp => ?_).1 hXm
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  obtain ⟨d, hd, rfl⟩ := hmemps q hq
  show X.rl [(swUp L.length (str d).2.sw).level] [] = true
  rw [swUp_level, Idx.level_sw, hlev d]
  exact hfr _ (hdlev d hd)

end Body

/-- A layer's reading through the prefix is its swapped reading. -/
theorem swPrefix_tkBody {k₁ k₂ : HashKind} {fix full : Bool} {Γ : Ctx} {ψ φ : Fml C Γ}
    (e : ψ.tkBody k₁ k₂ N fix full = some φ) : φ.swPrefix k₁ = φ.sw k₁ := by
  obtain ⟨-, ψ₂, -, rfl⟩ := Fml.tkBody_eq e
  rw [Fml.swPrefix_allN, Fml.sw_allN]
  rfl

/-- **The move through the prefix.** -/
theorem _root_.Solidity.Fml.tk_move {k₁ k₂ : HashKind} {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {φp φf : Fml C Γ} {φp' φf' : Fml C (Ctx.sw Γ)},
      φ.tk k₁ k₂ N false = some φp → φ.tk k₁ k₂ N false true = some φf →
      φp.swPrefix k₁ = some φp' → φf.swPrefix k₁ = some φf' → φ.tkMove k₁ k₂ = true →
      ∀ τ : State C (Ctx.sw Γ), (∀ τ'', Moved (φ.tkDeadP k₁ k₂) τ τ'' → holds τ'' φf') → holds τ φp' := by
  induction φ with
  | all x p φ ih =>
    intro _ _ _ _ ep ef sp sf hmv τ H
    obtain ⟨φp, hp, rfl⟩ := Option.map_eq_some_iff.1 ep
    obtain ⟨φf, hf, rfl⟩ := Option.map_eq_some_iff.1 ef
    obtain ⟨φp', hp', rfl⟩ := Option.map_eq_some_iff.1 sp
    obtain ⟨φf', hf', rfl⟩ := Option.map_eq_some_iff.1 sf
    intro v
    refine ih hp hf hp' hf' hmv _ fun τ'' hm => ?_
    obtain ⟨σ'', v'', hm', rfl⟩ := Moved.push_inv hm
    exact H σ'' hm' v''
  | allocAll x R φ ih =>
    intro _ _ _ _ ep ef sp sf hmv τ H
    obtain ⟨φp, hp, rfl⟩ := Option.map_eq_some_iff.1 ep
    obtain ⟨φf, hf, rfl⟩ := Option.map_eq_some_iff.1 ef
    simp only [Fml.swPrefix] at sp sf
    split at sp
    · rename_i hR
      rw [if_pos hR] at sf
      obtain ⟨φp', hp', rfl⟩ := Option.map_eq_some_iff.1 sp
      obtain ⟨φf', hf', rfl⟩ := Option.map_eq_some_iff.1 sf
      intro v
      refine ih hp hf hp' hf' hmv _ fun τ'' hm => ?_
      obtain ⟨σ'', v'', hm', rfl⟩ := Moved.push_inv hm
      exact H σ'' hm' v''
    · cases sp
  | tt | eq | wellFormed | not | and | imp | upd =>
    intro _ _ _ _ ep ef sp sf hmv τ H
    rw [swPrefix_tkBody ep] at sp
    rw [swPrefix_tkBody ef] at sf
    exact Fml.tkBody_move _ ep ef sp sf hmv τ H
  | modal | havoc | bind | anon | grow => intro _ _ _ _ e; cases e

/-- **Where the reading with every pair linked is valid, the decision's
is.** -/
theorem _root_.Solidity.Fml.tk_valid_move {k₁ k₂ : HashKind} {φ φp φf φp' φf' : Fml C []}
    (ep : φ.tk k₁ k₂ N false = some φp) (ef : φ.tk k₁ k₂ N false true = some φf)
    (sp : φp.swPrefix k₁ = some φp') (sf : φf.swPrefix k₁ = some φf') (hmv : φ.tkMove k₁ k₂ = true)
    (hv : Fml.Valid φf') : Fml.Valid φp' :=
  fun σ => Fml.tk_move φ ep ef sp sf hmv σ fun τ'' _ => hv τ''

/-- **Completeness of the refutations with two kinds**, from the decision's
reading: a refutation of it moved to one of the reading with every pair
linked (`Fml.tk_valid_move`), which `Fml.tk_complete` takes. -/
theorem _root_.Solidity.Fml.tk_complete_move {k₁ k₂ : HashKind} (hk₁ : k₁ ≠ .ecrecover)
    (hk₂ : k₂ ≠ .ecrecover) (hokA : famOKAll N = true) {φ φ₂ φ₂' φ₂f φ₂f' : Fml C []}
    (e₂ : φ.tk k₁ k₂ N false = some φ₂) (e' : φ₂.swPrefix k₁ = some φ₂')
    (e₂f : φ.tk k₁ k₂ N false true = some φ₂f) (ef' : φ₂f.swPrefix k₁ = some φ₂f')
    (hmv : φ.tkMove k₁ k₂ = true) {V : List Nat} {K : List Name} (hK : KTyped C K)
    (hrl : φ₂f.swRL k₁ V K = true) (hpre : φ₂f.prefixOK V = true) (hn : φ₂f.allocCount ≤ N)
    (hrl₂ : φ.tkRL k₁ k₂ = true)
    (hinst : ∀ cs ∈ rgs φ₂f.allocCount, ∃ φF instF, φ.tk k₁ k₂ N true = some φF ∧
      φF.swInst k₁ cs = some instF)
    (hnv : ¬ Fml.Valid φ₂') :
    ∃ cs ∈ rgs φ₂f.allocCount, ∃ φF instF, φ.tk k₁ k₂ N true = some φF ∧ φF.swInst k₁ cs = some instF ∧
      ¬ Fml.Valid instF :=
  Fml.tk_complete hk₁ hk₂ hokA e₂f ef' hK hrl hpre hn hrl₂ hinst
    fun hv => hnv (Fml.tk_valid_move e₂ e₂f e' ef' hmv hv)

/-- info: 'Solidity.Fml.tk_complete_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.tk_complete_move

end Solidity.Decide
