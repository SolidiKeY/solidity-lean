import Solidity.Goals.Plan

/-! Plan step k1-lean-inventory: every valid certificate over adequate inputs is sound
(`Solidity.Goals.leanInventorySound`), and a small census exhibits every boundary case.

Standalone on purpose (`Solidity/Goals/Plan.lean`): no library root imports this file, so
the shared guard in `Solidity/Examples/Goals/Plan.lean` keeps reading `open`, while the
guard at the end of this file reads `proved`.

Boundary: the theorem certifies the finite abstract certificate reasoning only. It says
nothing about the Python extraction (`inventory.py`), the completeness of the real census
in `scripts/lean-inventory.json`, any measured time, Git recovery or deletion safety. -/

namespace Solidity.LeanInventory

open Solidity.Goals.Inventory

variable {M D C F : Type}

section Soundness

variable {W : World M D C F} {K : Census M D C F} {X : Certificate D C F}

theorem reach_of_chain (h : ∀ x y, K.Edge x y → W.uses x y) :
    ∀ {a b : D} (path : List D), Chain K.Edge a path b → Reach W.uses a b
  | a, b, [], hc => by cases hc; exact .refl a
  | _, _, _ :: xs, ⟨he, hc⟩ => .step (h _ _ he) (reach_of_chain h xs hc)

/-- A recorded-closed set contains everything recorded edges reach from it. -/
theorem recClosed_reach {p : ConsumerKind F → Bool} {S : List D} (hS : K.RecClosed p S) :
    ∀ {a b : D}, Reach K.Edge a b → a ∈ S → b ∈ S := by
  intro a b h
  induction h with
  | refl => exact id
  | step he _ ih => exact fun ha => ih (hS.2 _ he ha)

/-- A live gap's covered target lies in a closed set. -/
theorem gap_mem {p : ConsumerKind F → Bool} {S : List D} (hS : K.Closed p S) {g : Gap D C}
    (hg : g ∈ K.gaps) (hlive : K.GapLive p S g) {y : D}
    (ht : g.target = none ∨ g.target = some y) : y ∈ S := by
  obtain ⟨y', hy', hyS⟩ := hS.2 g hg hlive
  rcases ht with h | h <;> rw [h] at hy' <;> cases hy'
  exact hyS

/-- A closed set contains everything the world's uses reach from it. -/
theorem closed_reach (hA : Adequate W K) {p : ConsumerKind F → Bool} {S : List D}
    (hS : K.Closed p S) : ∀ {a b : D}, Reach W.uses a b → a ∈ S → b ∈ S := by
  intro a b h
  induction h with
  | refl => exact id
  | @step x y _ hu _ ih =>
    intro hx
    apply ih
    rcases hA.2.2.2.2.2.2.2.2 x y hu with he | ⟨g, hg, hsrc, htgt⟩
    · exact hS.1.2 _ he hx
    · refine gap_mem hS hg ?_ htgt
      rcases hsrc with h | h <;> simp only [Census.GapLive, h, hx]

/-- A closed set holds every actual root of a non-blanket consumer whose kind meets `p`. -/
theorem closed_root (hA : Adequate W K) (hV : K.Valid X) {p : ConsumerKind F → Bool}
    {S : List D} (hS : K.Closed p S) {c : C} {e : D} (hu : W.rootUse c e)
    (hb : W.kind c ≠ .blanket) (hp : p (W.kind c) = true) : e ∈ S := by
  rcases hA.2.2.2.2.2.2.1 c e hu hb with ⟨hc, hr⟩ | ⟨g, hg, hsrc, htgt⟩
  · exact hS.1.1 _ hr (by rw [hA.2.2.2.2.1 c hc]; exact hp)
  · refine gap_mem hS hg ?_ htgt
    rcases hsrc with h | h <;> simp only [Census.GapLive, h]
    have hc := (hV.2.2.2.2.2.1 g hg).2
    simp only [h] at hc
    rw [hA.2.2.2.2.1 c hc]; exact hp

theorem primary_not_blanket {k : ConsumerKind F} (h : k.primary = true) : k ≠ .blanket := by
  cases k <;> simp_all [ConsumerKind.primary]

theorem primary_demands {k : ConsumerKind F} (h : k.primary = true) : k.demands = true := by
  cases k <;> simp_all [ConsumerKind.primary, ConsumerKind.demands]

/-- Independently reachable declarations lie in every primary-closed set. -/
theorem indep_mem (hA : Adequate W K) (hV : K.Valid X) {p : ConsumerKind F → Bool}
    (hp : ∀ k, k.primary = true → p k = true) {S : List D} (hS : K.Closed p S) {d : D}
    (hd : W.IndepReach d) : d ∈ S := by
  obtain ⟨c, e, hk, hu, hr⟩ := hd
  exact closed_reach hA hS hr (closed_root hA hV hS hu (primary_not_blanket hk) (hp _ hk))

/-- A listed declaration's module is in scope and agrees with the world. -/
theorem listed_inScope (hA : Adequate W K) (hV : K.Valid X) {d : D} (hd : d ∈ K.decls) :
    K.declModule d ∈ K.modules ∧ K.declModule d = W.moduleOf d ∧ W.InScope (W.moduleOf d) := by
  have hm := hV.2.2.2.1 d hd
  have he := hA.2.2.2.1 d hd
  exact ⟨hm, he, (hA.1 _).2 (he ▸ hm)⟩

theorem seed_controlSeed (hA : Adequate W K) (hV : K.Valid X) {f : F} {via : Option C}
    {s : D} (h : K.Seed f via s) : W.ControlSeed f s := by
  have hs : s ∈ K.decls := by cases via <;> exact h.1
  obtain ⟨hm, he, hin⟩ := listed_inScope hA hV hs
  have hw := hA.2.1 _ hm
  refine ⟨hin, ?_, ?_⟩
  · rw [← he, hw.2.1]; cases via <;> exact h.2.1
  · cases via with
    | none => left; rw [← he, hw.2.2]; exact h.2.2
    | some c =>
      right
      obtain ⟨_, _, hc, hk, hr⟩ := h
      exact ⟨c, (hA.2.2.2.2.1 c hc) ▸ hk, hA.2.2.2.2.2.1 c s hr⟩

/-- Every listed declaration's witness means what its verdict says. -/
theorem meaning_of_listed (hA : Adequate W K) (hV : K.Valid X) {d : D} (hd : d ∈ K.decls) :
    Meaning W K d (X.entry d).evidence := by
  have hok := (hV.2.2.2.2.2.2.1 d hd).2
  generalize (X.entry d).evidence = ev at hok ⊢
  cases ev with
  | keep c e path =>
    obtain ⟨hc, hk, hr, hch⟩ := hok
    exact ⟨c, e, (hA.2.2.2.2.1 c hc) ▸ hk, hA.2.2.2.2.2.1 c e hr,
      reach_of_chain hA.2.2.2.2.2.2.2.1 path hch⟩
  | ownerNeeded f via s path S =>
    obtain ⟨hs, hch, hS, hdS⟩ := hok
    exact ⟨fun hi => hdS (indep_mem hA hV (fun _ h => h) hS hi),
      s, seed_controlSeed hA hV hs, reach_of_chain hA.2.2.2.2.2.2.2.1 path hch⟩
  | orphan S =>
    obtain ⟨hS, hctl, hdS⟩ := hok
    refine ⟨fun hi => hdS (indep_mem hA hV (fun _ h => primary_demands h) hS hi), ?_⟩
    rintro ⟨f, s, ⟨hin, _, hrole⟩, hr⟩
    apply hdS
    refine closed_reach hA hS hr ?_
    have hs := hA.2.2.1 s hin
    have hm := (hA.1 _).1 hin
    have he := hA.2.2.2.1 s hs
    rcases hrole with hrole | ⟨c, hk, hu⟩
    · exact hctl s hs (by rw [he, ← (hA.2.1 _ hm).2.2]; exact hrole)
    · exact closed_root hA hV hS hu (by rw [hk]; simp) (by rw [hk]; rfl)
  | unresolved g lead path S =>
    obtain ⟨hg, hlive, _, hS, hdS⟩ := hok
    refine ⟨hg, hlive, ?_⟩
    rintro ⟨c, e, _, hk, hr, hreach⟩
    exact hdS (recClosed_reach hS hreach (hS.1 _ hr hk))

/-- What a listed declaration's verdict alone says about the world. -/
def VerdictMeaning (W : World M D C F) (K : Census M D C F) (d : D) : Verdict → Prop
  | .keep => W.IndepReach d
  | .ownerNeeded => ¬ W.IndepReach d ∧ W.ControlDemand d
  | .orphan => ¬ W.IndepReach d ∧ ¬ W.ControlDemand d
  | .unresolved => K.gaps ≠ []

theorem verdict_meaning (hA : Adequate W K) (hV : K.Valid X) {d : D} (hd : d ∈ K.decls)
    {v : Verdict} (hv : (X.entry d).evidence.verdict = v) : VerdictMeaning W K d v := by
  have hm := meaning_of_listed hA hV hd
  subst hv
  generalize (X.entry d).evidence = ev at hm
  cases ev with
  | keep | orphan => exact hm
  | ownerNeeded => exact ⟨hm.1, _, hm.2⟩
  | unresolved => exact List.ne_nil_of_mem hm.1

theorem member_listed (hA : Adequate W K) (hV : K.Valid X) {f : F} {d : D}
    (h : W.Member f d) : d ∈ K.decls ∧ K.family (K.declModule d) = f := by
  have hd := hA.2.2.1 d h.1
  obtain ⟨hm, he, _⟩ := listed_inScope hA hV hd
  refine ⟨hd, ?_⟩
  rw [← (hA.2.1 _ hm).2.1, he]; exact h.2

theorem listed_member (hA : Adequate W K) (hV : K.Valid X) {f : F} {d : D}
    (hd : d ∈ K.decls) (hf : K.family (K.declModule d) = f) : W.Member f d := by
  obtain ⟨hm, he, hin⟩ := listed_inScope hA hV hd
  refine ⟨hin, ?_⟩
  rw [← he, (hA.2.1 _ hm).2.1]; exact hf

theorem family_sound (hA : Adequate W K) (hV : K.Valid X) {f : F} (hf : f ∈ K.families) :
    (X.family f = .keep → ∃ d, W.Member f d ∧ W.IndepReach d) ∧
    (X.family f = .ownerNeeded →
      (∀ d, W.Member f d → ¬ W.IndepReach d) ∧
      ∃ d, W.Member f d ∧ W.ControlDemand d) ∧
    (X.family f = .orphan → (∃ d, W.Member f d) ∧
      ∀ d, W.Member f d → ¬ W.IndepReach d ∧ ¬ W.ControlDemand d) ∧
    (X.family f = .unresolved → K.gaps ≠ [] ∨ ¬ ∃ d, W.Member f d) ∧
    ∀ d, W.Member f d → W.IndepReach d →
      X.family f = .keep ∨ X.family f = .unresolved := by
  have hok := hV.2.2.2.2.2.2.2.1 f hf
  have ownerCase : X.family f = .ownerNeeded →
      (∀ d, W.Member f d → ¬ W.IndepReach d) ∧ ∃ d, W.Member f d ∧ W.ControlDemand d := by
    intro h
    rw [h] at hok
    obtain ⟨hnk, hnu, d, hd, hfd, hv⟩ := hok
    refine ⟨fun d' hm' => ?_, d, listed_member hA hV hd hfd, (verdict_meaning hA hV hd hv).2⟩
    obtain ⟨hd', hf'⟩ := member_listed hA hV hm'
    cases hv' : (X.entry d').evidence.verdict
    · exact absurd ⟨d', hd', hf', hv'⟩ hnk
    · exact (verdict_meaning hA hV hd' hv').1
    · exact (verdict_meaning hA hV hd' hv').1
    · exact absurd ⟨d', hd', hf', hv'⟩ hnu
  have orphanCase : X.family f = .orphan → (∃ d, W.Member f d) ∧
      ∀ d, W.Member f d → ¬ W.IndepReach d ∧ ¬ W.ControlDemand d := by
    intro h
    rw [h] at hok
    obtain ⟨⟨d, hd, hfd⟩, hall⟩ := hok
    refine ⟨⟨d, listed_member hA hV hd hfd⟩, fun d' hm' => ?_⟩
    obtain ⟨hd', hf'⟩ := member_listed hA hV hm'
    exact verdict_meaning hA hV hd' (hall d' hd' hf')
  refine ⟨fun h => ?_, ownerCase, orphanCase, fun h => ?_, fun d hm hi => ?_⟩
  · rw [h] at hok
    obtain ⟨d, hd, hfd, hv⟩ := hok
    exact ⟨d, listed_member hA hV hd hfd, verdict_meaning hA hV hd hv⟩
  · rw [h] at hok
    rcases hok.2 with ⟨d, hd, _, hv⟩ | hne
    · exact .inl (verdict_meaning hA hV hd hv)
    · exact .inr fun ⟨d, hm⟩ => hne ⟨d, member_listed hA hV hm⟩
  · cases hfam : X.family f with
    | keep => exact .inl rfl
    | unresolved => exact .inr rfl
    | ownerNeeded => exact absurd hi ((ownerCase hfam).1 d hm)
    | orphan => exact absurd hi ((orphanCase hfam).2 d hm).1

/-- The first conjunct of the goal: adequate inputs and a valid certificate are sound. -/
theorem sound (hA : Adequate W K) (hV : K.Valid X) : Sound W K X := by
  refine ⟨fun d hd => meaning_of_listed hA hV (hA.2.2.1 d hd), ?_,
    fun f hf => family_sound hA hV hf, ?_⟩
  · exact fun hnil d hd hv => verdict_meaning hA hV (hA.2.2.1 d hd) hv hnil
  · intro m hm
    have hmm := (hA.1 m).1 hm
    have hpin := hV.2.2.2.2.2.2.2.2.2.2 (K.family m) (hV.1 m hmm)
    exact ⟨hmm, hV.1 m hmm, hV.2.2.2.2.2.2.2.2.1, hV.2.2.2.2.2.2.2.2.2.1 m hmm,
      hpin.2 m hmm rfl⟩

end Soundness

/-! A census exhibiting every boundary case at once: a module per area, an outside
module on the keep path, a mixed keep family, an own-controls cycle, a blanket-reached
orphan cycle, a live gap, declaration-empty families, and both timing records. -/
section Instance

inductive Mod where
  | be | yu | yuC | lo | fe | sv | so | op | out
deriving DecidableEq

inductive Decl where
  | ext | a1 | a2 | own | ctl | p | q | u
deriving DecidableEq

inductive Cons where
  | cKeep | cOwn | cBl
deriving DecidableEq

inductive Fam where
  | be | yu | lo | fe | sv | so | op
deriving DecidableEq

def Mod.area : Mod → Area
  | .be | .out => .backend | .yu | .yuC => .yul | .lo => .lowering | .fe => .frontend
  | .sv => .solcValidation | .so => .source | .op => .optimizer

def Mod.fam : Mod → Fam
  | .be | .out => .be | .yu | .yuC => .yu | .lo => .lo | .fe => .fe | .sv => .sv
  | .so => .so | .op => .op

def Mod.role : Mod → Role
  | .yuC => .controls
  | _ => .member

def Decl.mod : Decl → Mod
  | .ext => .out | .a1 | .a2 => .be | .own => .yu | .ctl => .yuC | .p | .q => .lo | .u => .fe

def Cons.kind : Cons → ConsumerKind Fam
  | .cKeep => .test | .cOwn => .ownControls | .cBl => .blanket

def exProv : Provenance :=
  ⟨"lake lean", "leanprover/lean4:v4.24.0", "lake lean Be.lean", "warm cache", "ok"⟩

def exGap : Gap Decl Cons := ⟨.use none, some .u, "elaborator-only use"⟩

def exModules : List Mod := [.be, .yu, .yuC, .lo, .fe, .sv, .so, .op]

def exCensus : Census Mod Decl Cons Fam where
  modules := exModules
  area := Mod.area
  family := Mod.fam
  role := Mod.role
  families := [.be, .yu, .lo, .fe, .sv, .so, .op]
  decls := [.a1, .a2, .own, .ctl, .p, .q, .u]
  declModule := Decl.mod
  consumers := [.cKeep, .cOwn, .cBl]
  kind := Cons.kind
  roots := [(.cKeep, .ext), (.cOwn, .own), (.cBl, .p)]
  edges := [(.ext, .a1), (.own, .ctl), (.ctl, .own), (.p, .q), (.q, .p)]
  gaps := [exGap]
  lineBasis := "physical lines"
  lines := fun _ => 1
  checkTime := fun m => if m = .be then .measured 1 exProv else .unavailable "not measured"
  pin := fun _ => ⟨"rev", exModules⟩

def exWorld : World Mod Decl Cons Fam where
  area m := if m = .out then none else some m.area
  family := Mod.fam
  role := Mod.role
  moduleOf := Decl.mod
  uses a b := (a, b) ∈ exCensus.edges
  rootUse c d := (c, d) ∈ exCensus.roots
  kind := Cons.kind

/-- Closed over primary roots: holds every independently reachable declaration and the
live gap's target. -/
def exIndep : List Decl := [.ext, .a1, .u]

/-- Closed over every demanding root and every Controls/Pins declaration. -/
def exDemand : List Decl := [.ext, .a1, .own, .ctl, .u]

def exEvidence : Decl → Evidence Decl Cons Fam
  | .ext | .a1 => .keep .cKeep .ext [.a1]
  | .own => .ownerNeeded .yu none .ctl [.own] exIndep
  | .ctl => .ownerNeeded .yu none .ctl [] exIndep
  | .u => .unresolved exGap (.u, []) [] [.ext, .a1]
  | _ => .orphan exDemand

def exCert : Certificate Decl Cons Fam where
  entry d := ⟨exEvidence d, "witness"⟩
  family
    | .be => .keep | .yu => .ownerNeeded | .lo => .orphan
    | .fe | .sv | .so | .op => .unresolved

theorem ex_adequate : Adequate exWorld exCensus := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m; cases m <;> simp [World.InScope, exWorld, exCensus, exModules]
  · intro m hm; simp [exCensus, exModules] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [exWorld, exCensus]
  · intro d hd; cases d <;> simp_all [World.InScope, exWorld, exCensus, Decl.mod]
  · intro d _; rfl
  · intro c _; rfl
  · intro c d h; exact h
  · intro c d h _; exact .inl ⟨by cases c <;> simp [exCensus], h⟩
  · intro x y h; exact h
  · intro x y h; exact .inl h

theorem ex_valid : exCensus.Valid exCert := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (simp [exCensus, exCert, exModules, exEvidence, Census.EvidenceOk,
    Census.FamilyOk, Certificate.Has, Census.Closed, Census.RecClosed, Census.GapLive,
    Census.Seed, Census.Edge, Census.GapSourceLive, Chain, exIndep, exDemand, exGap,
    Measured.Recorded, exProv, Decl.mod, Mod.fam, Mod.role, Cons.kind, ConsumerKind.primary,
    ConsumerKind.demands, Evidence.verdict, Mod.area] <;> decide)

theorem ex_exhibits : Exhibits exCensus exCert := by
  refine ⟨?_, ⟨.a1, ?_, .a2, ?_⟩, ⟨.own, ?_, .ctl, ?_⟩, ⟨.p, ?_, .q, ?_⟩, ⟨.u, ?_⟩, ⟨.be, ?_⟩,
    ⟨.yu, ?_⟩⟩
  all_goals (simp [Area.all, exCensus, exCert, exModules, exEvidence, Census.Edge, exGap,
    Evidence.verdict, Evidence.owner, Decl.mod, Mod.fam, Mod.role, Cons.kind, Mod.area,
    Measured.isMeasured] <;> decide)

/-- Adequate inputs, a valid certificate and every boundary case at once. -/
theorem ex_instance : ∃ (M D C F : Type) (W : World M D C F) (K : Census M D C F)
    (X : Certificate D C F), Adequate W K ∧ K.Valid X ∧ Exhibits K X :=
  ⟨Mod, Decl, Cons, Fam, exWorld, exCensus, exCert, ex_adequate, ex_valid, ex_exhibits⟩

end Instance

theorem inventory_sound : Solidity.Goals.leanInventorySound :=
  ⟨fun _ _ _ _ _ _ _ hA hV => sound hA hV, ex_instance⟩

end Solidity.LeanInventory

namespace Solidity.Goals

/--
info: proved Solidity.Goals.leanInventorySound ← Solidity.LeanInventory.inventory_sound plan k1-lean-inventory
-/
#guard_msgs in
#roadmap_goal leanInventorySound

end Solidity.Goals

/-- info: 'Solidity.LeanInventory.inventory_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.LeanInventory.inventory_sound
