import Solidity.Calculus.ArrayProperty
import Solidity.Calculus.ArrayCut
import Solidity.Calculus.FlattenTotality

/-! # Exact finite instances of a literal-bounded uint binder
This uses the actual LFml, guarded instantiation and substitution APIs. No
flooring, storage reconstruction, decision oracle or new semantic premise.
-/
namespace Solidity.Decide

/-- The ordinary strict comparison guard against true. -/
def uintBelow {C : Contract} (k : Nat) (bound : PrimTy.uint.Denote) : LFml C :=
  .eq (.app2 (.binop .lt (p := .uint) rfl) (.var k) (.app0 (.lit bound))) (.app0 (.lit true))

/-- Exactly the literal indices strictly below the canonical uint bound. -/
def uintSamples {C : Contract} (bound : PrimTy.uint.Denote) : List (LTm C (.val .uint)) :=
  (List.range bound.1.toNat).map (fun i => .app0 (.lit (uintOfNat i)))

theorem uintBelow_holds {C : Contract} (g : State C []) (ν : AEnv) (k : Nat)
    (bound : PrimTy.uint.Denote) : (uintBelow (C := C) k bound).holds g ν ↔ (ν.u k).1 < bound.1 := by
  change (decide ((ν.u k).1 < bound.1) = true) ↔ (ν.u k).1 < bound.1
  exact decide_eq_true_iff

theorem uintBelow_set_holds {C : Contract} (g : State C []) (ν : AEnv) (k : Nat)
    (bound v : PrimTy.uint.Denote) :
    (uintBelow (C := C) k bound).holds g (ν.set .uint k v) ↔ v.1.toNat < bound.1.toNat := by
  rw [uintBelow_holds]
  change (if k = k then v else ν.u k).1 < bound.1 ↔ v.1.toNat < bound.1.toNat
  rw [if_pos rfl]
  have hv : 0 ≤ v.1 := uint_nonneg v
  have hb : 0 ≤ bound.1 := uint_nonneg bound
  omega

theorem uintSamples_complete {C : Contract} (bound v : PrimTy.uint.Denote)
    (hv : v.1.toNat < bound.1.toNat) : (LTm.app0 (.lit v) : LTm C (.val .uint)) ∈ uintSamples bound := by
  apply List.mem_map.mpr
  exact ⟨v.1.toNat, List.mem_range.mpr hv, by rw [uintOfNat_toNatA]⟩

/-- A literal-bounded uint universal is equivalent to its actual finite guarded
instances, for every state and valuation. The body may contain arbitrary typed
storage/memory/ledger terms and partial operands; only quantifier-freedom is needed. -/
theorem boundedUInt_inst_iff {C : Contract} (g : State C []) (ν : AEnv) (k : Nat)
    (bound : PrimTy.uint.Denote) (φ : LFml C) (hq : φ.qfB = true) :
    ((LFml.all k .uint (.imp (uintBelow k bound) φ)).inst (uintSamples bound)).holds g ν ↔
      (LFml.all k .uint (.imp (uintBelow k bound) φ)).holds g ν := by
  have hbody : (LFml.imp (uintBelow (C := C) k bound) φ).qfB = true := by
    simp only [LFml.qfB, uintBelow, hq, Bool.true_and]
  constructor
  · intro hi v hg
    have hv : v.1.toNat < bound.1.toNat := (uintBelow_set_holds g ν k bound v).mp hg
    have hm : (LTm.app0 (.lit v) : LTm C (.val .uint)) ∈ uintSamples bound := uintSamples_complete bound v hv
    rw [LFml.inst_all] at hi
    change (LFml.conj ((uintSamples bound).map (fun u =>
      LFml.imp (.eq u u) ((LFml.imp (uintBelow k bound) φ).subst1 k u)))).holds g ν at hi
    have hinstance : ((LFml.imp (uintBelow k bound) φ).subst1 k (.app0 (.lit v))).holds g ν :=
      ((LFml.holds_conj g ν _).mp hi _ (List.mem_map_of_mem hm)) (by rfl)
    have hs : ((LFml.imp (uintBelow k bound) φ).subst1 k (.app0 (.lit v))).holds g ν ↔
        (LFml.imp (uintBelow k bound) φ).holds g (ν.set .uint k v) :=
      LFml.holds_subst1 g ν k (.app0 (.lit v)) (v := v) (by rfl) _ hbody
    exact (hs.mp hinstance) hg
  · intro h
    apply LFml.inst_sound g (uintSamples bound) _ ν _ h
    simp only [LFml.chainQF, hbody, decide_true, Bool.true_and]

/-- Substituting a literal for a uint atom preserves the actual term node count. -/
theorem subst_uint_literal_nodes {C : Contract} (k : Nat) (v : PrimTy.uint.Denote)
    {s : Srt} (t : LTm C s) : (LTm.subst1 k (.app0 (.lit v)) t).nodes = t.nodes := by
  induction t with
  | @var p j =>
    change (LTm.substVar k (.app0 (.lit v)) p j).nodes = 1
    unfold LTm.substVar
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · rfl
  | app0 | err => rfl
  | app1 o a ih | obsW a ih | obsL a ih | obsH a ih =>
    simp only [LTm.subst1, LTm.nodes, ih]
  | app2 o a b iha ihb | index o a b iha ihb | seq a b iha ihb | orElse a b iha ihb =>
    simp only [LTm.subst1, LTm.nodes, iha, ihb]
  | app3 o a b c iha ihb ihc => simp only [LTm.subst1, LTm.nodes, iha, ihb, ihc]
  | kite a b t e iha ihb iht ihe => simp only [LTm.subst1, LTm.nodes, iha, ihb, iht, ihe]

theorem subst_uint_literal_formula_nodes {C : Contract} (k : Nat) (v : PrimTy.uint.Denote)
    (φ : LFml C) : (φ.subst1 k (.app0 (.lit v))).nodes = φ.nodes := by
  induction φ with
  | tt | all => rfl
  | eq a b => simp only [LFml.subst1, LFml.nodes, subst_uint_literal_nodes]
  | not φ ih => simp only [LFml.subst1, LFml.nodes, ih]
  | and φ ψ iha ihb | imp φ ψ iha ihb => simp only [LFml.subst1, LFml.nodes, iha, ihb]

/-- The real conjunction builder has a linear structural node bound. -/
theorem conj_nodes_le {C : Contract} (fs : List (LFml C)) (N : Nat)
    (h : ∀ f ∈ fs, f.nodes ≤ N) : (LFml.conj fs).nodes ≤ fs.length * (N + 1) + 1 := by
  induction fs with
  | nil => simp only [LFml.conj, LFml.nodes, List.length_nil, Nat.zero_mul, Nat.zero_add, Nat.le_refl]
  | cons f fs ih =>
    cases fs with
    | nil =>
      have hf : f.nodes ≤ N := h f List.mem_cons_self
      change f.nodes ≤ 1 * (N + 1) + 1
      omega
    | cons g gs =>
      have hf : f.nodes ≤ N := h f List.mem_cons_self
      have ht : (LFml.conj (g :: gs)).nodes ≤ (g :: gs).length * (N + 1) + 1 :=
        ih (fun x hx => h x (List.mem_cons_of_mem f hx))
      change f.nodes + (LFml.conj (g :: gs)).nodes + 1 ≤ (g :: gs).length.succ * (N + 1) + 1
      rw [Nat.succ_mul]
      omega

/-- A computed formula bound is checked before allocating the finite instances. -/
def boundedUIntEstimate {C : Contract} (bound : PrimTy.uint.Denote) (body : LFml C) : Nat :=
  bound.1.toNat * (body.nodes + 5) + 1

/-- The estimate bounds the actual existing guarded-instantiation output. -/
theorem boundedUInt_inst_nodes {C : Contract} (k : Nat) (bound : PrimTy.uint.Denote)
    (φ : LFml C) :
    ((LFml.all k .uint (.imp (uintBelow k bound) φ)).inst (uintSamples bound)).nodes ≤
      boundedUIntEstimate bound (.imp (uintBelow k bound) φ) := by
  rw [LFml.inst_all]
  change (LFml.conj ((uintSamples bound).map (fun u =>
    LFml.imp (.eq u u) ((LFml.imp (uintBelow k bound) φ).subst1 k u)))).nodes ≤ _
  have hnodes : ∀ f ∈ (uintSamples (C := C) bound).map (fun u =>
      LFml.imp (.eq u u) ((LFml.imp (uintBelow k bound) φ).subst1 k u)),
      f.nodes ≤ (LFml.imp (uintBelow k bound) φ).nodes + 4 := by
    intro f hf
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
    simp only [LFml.nodes, LTm.nodes, subst_uint_literal_formula_nodes]
    omega
  have hb := conj_nodes_le _ _ hnodes
  simpa only [List.length_map, uintSamples, List.length_range, boundedUIntEstimate,
    Nat.add_assoc] using hb

/-- Candidate extraction uses generalized-index recursors; exact guard equality
is checked separately, so this data is never a semantic oracle. -/
def uintLtBinCandidate {C : Contract} {A B S : Srt} (o : Op2 C A B S) :
    LTm C A → LTm C B → Option PrimTy.uint.Denote := by
  apply @Op2.casesOn C (fun A B S o => LTm C A → LTm C B → Option PrimTy.uint.Denote) A B S o
  · intro op p _h _a b
    cases p with
    | bool | int => exact none
    | uint =>
      cases op with
      | lt => exact b.litV?
      | _ => exact none
  all_goals intros; exact none

def uintLtBoundCandidate {C : Contract} {s : Srt} (t : LTm C s) : Option PrimTy.uint.Denote := by
  apply @LTm.casesOn C (fun s t => Option PrimTy.uint.Denote) s t
  · intros; exact none
  · intros; exact none
  · intros; exact none
  · intro A B S o a b
    exact uintLtBinCandidate o a b
  all_goals intros; exact none

/-- A recognized guard carries equality with the actual existing formula. -/
def boundedUIntGuard? {C : Contract} (k : Nat) (G : LFml C) :
    Option {bound : PrimTy.uint.Denote // G = uintBelow k bound} :=
  let candidate : Option PrimTy.uint.Denote := match G with
    | .eq a _ => uintLtBoundCandidate a
    | _ => none
  match candidate with
  | none => none
  | some bound =>
    if h : G.same (uintBelow k bound) = true then
      some (⟨bound, LFml.eq_of_same G (uintBelow k bound) h⟩ : {b // G = uintBelow k b})
    else none

/-- A concrete reduction on the existing formula with pointwise meaning. -/
structure BoundedUIntEquiv {C : Contract} (B : LFml C) where
  body : LFml C
  meaning : ∀ (g : State C []) (ν : AEnv), body.holds g ν ↔ B.holds g ν

def BoundedUIntEquiv.id {C : Contract} (B : LFml C) : BoundedUIntEquiv B := ⟨B, fun _ _ => Iff.rfl⟩

/-- Expand only an actually recognized quantifier-free literal-bounded binder.
Each selected expansion is checked against the original 511-node limit BEFORE
sample allocation. The whole result remains subject to all original pipeline checks. -/
def boundedUIntStep {C : Contract} (B : LFml C) : BoundedUIntEquiv B :=
  match B with
  | .all k .uint (.imp G φ) =>
    if hq : φ.qfB = true then
      match boundedUIntGuard? k G with
      | some ⟨bound, hG⟩ =>
        if _hbudget : boundedUIntEstimate bound (.imp G φ) ≤ 511 then
          ⟨(LFml.all k .uint (.imp G φ)).inst (uintSamples bound), by
            intro g ν
            subst G
            exact boundedUInt_inst_iff g ν k bound φ hq⟩
        else BoundedUIntEquiv.id _
      | none => BoundedUIntEquiv.id _
    else BoundedUIntEquiv.id _
  | B => BoundedUIntEquiv.id B

/-- Bottom-up exact expansion prepares children first; an unsupported/over-budget
quantifier is retained with its prepared body. -/
def boundedUIntExpand {C : Contract} : (B : LFml C) → BoundedUIntEquiv B
  | .tt => BoundedUIntEquiv.id .tt
  | .eq a b => BoundedUIntEquiv.id (.eq a b)
  | .not φ =>
    let r := boundedUIntExpand φ
    ⟨.not r.body, fun g ν => not_congr (r.meaning g ν)⟩
  | .and φ ψ =>
    let r := boundedUIntExpand φ
    let s := boundedUIntExpand ψ
    ⟨.and r.body s.body, fun g ν => and_congr (r.meaning g ν) (s.meaning g ν)⟩
  | .imp φ ψ =>
    let r := boundedUIntExpand φ
    let s := boundedUIntExpand ψ
    ⟨.imp r.body s.body, fun g ν => imp_congr (r.meaning g ν) (s.meaning g ν)⟩
  | .all k p φ =>
    let r := boundedUIntExpand φ
    let s := boundedUIntStep (.all k p r.body)
    ⟨s.body, fun g ν => (s.meaning g ν).trans (forall_congr' fun v => r.meaning g (ν.set p k v))⟩

/-- Exact preparation, with the original refuting state preserved unchanged. -/
def boundedUIntPrep {C : Contract} (B : LFml C) : Prep B :=
  let r := boundedUIntExpand B
  ⟨r.body, fun h g ν => (r.meaning g ν).mp (h g ν),
    fun g ν h => ⟨g, fun hb => h ((r.meaning g ν).mpr hb)⟩⟩

theorem boundedUInt_inst_fits {C : Contract} (k : Nat) (bound : PrimTy.uint.Denote) (φ : LFml C)
    (h : boundedUIntEstimate bound (.imp (uintBelow k bound) φ) ≤ 511) :
    ((LFml.all k .uint (.imp (uintBelow k bound) φ)).inst (uintSamples bound)).nodes ≤ 511 :=
  Nat.le_trans (boundedUInt_inst_nodes k bound φ) h

end Solidity.Decide
