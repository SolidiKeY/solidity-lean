import Solidity.Frontend.QualifiedUnits.SignatureHiding

/-! Identity-based inherited overload collection. The bounded owner merge
uses Source.Resolve's C3 equations with original DeclIds instead of names.
This does not validate inheritance/override legality (G14). Comparison
failures propagate as none; no unresolved type is treated as a distinct
signature. The declarative walk below is independent of the executable walk.
-/
namespace Solidity.Frontend.QualifiedUnits.SignatureMembers
open Solidity.Source SignatureHiding

/-- C3 merge on original declaration identities; no copied Env or name join. -/
def mergeOwners : Nat → List (List DeclId) → Option (List DeclId)
  | 0,_ => none
  | fuel + 1,lists =>
    let lists := lists.filter (· ≠ [])
    if lists.isEmpty then some [] else
      match lists.findSome? fun list => list.head?.filter fun h => lists.all fun other => !(other.drop 1).contains h with
      | none => none
      | some h => (mergeOwners fuel (lists.map fun list => list.filter (· ≠ h))).map (h :: ·)

/-- Every written base must resolve. Missing/ambiguous bases cannot vanish
through the legacy graph's filterMap. Roots must be original containers. -/
def bases (P : UnitSet) (R : List Remapping) (owner : DeclId) : Option (List DeclId) :=
  match P.decl? owner with
  | none => none
  | some d => if Container d.kind then (basePaths d).mapM (unitBase P R owner.unit) else none

def linearize (P : UnitSet) (R : List Remapping) (bound : Nat) : Nat → DeclId → Option (List DeclId)
  | 0,_ => none
  | fuel + 1,owner =>
    (bases P R owner).bind fun bs =>
      let bs := bs.reverse
      match bs.mapM (linearize P R bound fuel) with
      | none => none
      | some lists => (mergeOwners (bound * bound + 2) (lists ++ [bs])).map (owner :: ·)

/-- Finite graph depth bound matches the existing Source linearization. -/
def order (P : UnitSet) (R : List Remapping) (root : DeclId) : Option (List DeclId) :=
  let bound := (idUniverse P root).length
  linearize P R bound (bound + 1) root

def overload (P : UnitSet) (i : DeclId) : Bool :=
  match P.decl? i with
  | none => false
  | some d => d.kind.overloads

def group (P : UnitSet) (root owner : DeclId) (x : String) : List DeclId :=
  (visibleMembers P root owner x).filter (overload P)

/-- No earlier owner hides this candidate. Same-owner declarations are not
put in seen until the whole owner's group has been considered. -/
inductive Unhidden (P : UnitSet) (R : List Remapping) (target : DeclId) : List DeclId → Prop where
  | nil : Unhidden P R target []
  | cons {i : DeclId} {seen : List DeclId} : hides P R i target = some false →
      Unhidden P R target seen → Unhidden P R target (i :: seen)

def unhidden (P : UnitSet) (R : List Remapping) (target : DeclId) : List DeclId → Option Bool
  | [] => some true
  | i :: seen =>
    match hides P R i target with
    | none => none
    | some true => some false
    | some false => unhidden P R target seen

theorem unhidden_iff {P : UnitSet} {R : List Remapping} {target : DeclId} {seen : List DeclId} :
    unhidden P R target seen = some true ↔ Unhidden P R target seen := by
  induction seen with
  | nil => exact ⟨fun _ => .nil,fun _ => rfl⟩
  | cons i seen ih =>
    cases hd : hides P R i target with
    | none =>
      constructor
      · intro h; simp only [unhidden,hd] at h; cases h
      · intro h; cases h with | cons he _ => rw [hd] at he; cases he
    | some answer =>
      cases answer with
      | false =>
        constructor
        · intro h; simp only [unhidden,hd] at h; exact .cons hd (ih.mp h)
        · intro h; cases h with | cons _ hs => simpa only [unhidden,hd] using ih.mpr hs
      | true =>
        constructor
        · intro h; simp only [unhidden,hd] at h; cases h
        · intro h; cases h with | cons he _ => rw [hd] at he; cases he

def select (P : UnitSet) (R : List Remapping) (seen : List DeclId) : List DeclId → Option (List DeclId)
  | [] => some []
  | i :: rest =>
    match unhidden P R i seen, select P R seen rest with
    | some keep,some selected => some (if keep then i :: selected else selected)
    | _,_ => none

theorem mem_select {P : UnitSet} {R : List Remapping} {seen candidates out : List DeclId}
    (h : select P R seen candidates = some out) (j : DeclId) :
    j ∈ out ↔ j ∈ candidates ∧ Unhidden P R j seen := by
  induction candidates generalizing out with
  | nil =>
    cases h
    constructor
    · intro hm; cases hm
    · intro hm; cases hm.1
  | cons i rest ih =>
    unfold select at h
    split at h
    · rename_i keep selected hk hs
      cases keep with
      | false =>
        cases Option.some.inj h
        change j ∈ selected ↔ _
        rw [ih hs]
        constructor
        · intro ⟨hj,hu⟩; exact ⟨List.mem_cons_of_mem _ hj,hu⟩
        · intro ⟨hj,hu⟩
          rcases List.mem_cons.mp hj with he | hj
          · subst j
            rw [unhidden_iff.mpr hu] at hk
            cases hk
          · exact ⟨hj,hu⟩
      | true =>
        cases Option.some.inj h
        change j ∈ i :: selected ↔ _
        rw [List.mem_cons,ih hs]
        constructor
        · intro hj
          rcases hj with he | ⟨hj,hu⟩
          · subst j; exact ⟨List.mem_cons_self,unhidden_iff.mp hk⟩
          · exact ⟨List.mem_cons_of_mem _ hj,hu⟩
        · intro ⟨hj,hu⟩
          rcases List.mem_cons.mp hj with he | hj
          · exact Or.inl he
          · exact Or.inr ⟨hj,hu⟩
    · cases h

inductive WalkMember (P : UnitSet) (R : List Remapping) (root : DeclId) (x : String) :
    List DeclId → List DeclId → DeclId → Prop where
  | here {owner j : DeclId} {rest seen : List DeclId} : j ∈ group P root owner x →
      Unhidden P R j seen → WalkMember P R root x (owner :: rest) seen j
  | next {owner j : DeclId} {rest seen : List DeclId} :
      WalkMember P R root x rest (seen ++ group P root owner x) j →
      WalkMember P R root x (owner :: rest) seen j

def walk (P : UnitSet) (R : List Remapping) (root : DeclId) (x : String) :
    List DeclId → List DeclId → Option (List DeclId)
  | [],_ => some []
  | owner :: rest,seen =>
    let current := group P root owner x
    match select P R seen current, walk P R root x rest (seen ++ current) with
    | some selected,some tail => some (selected ++ tail)
    | _,_ => none

theorem mem_walk {P : UnitSet} {R : List Remapping} {root : DeclId} {x : String}
    {owners seen out : List DeclId} (h : walk P R root x owners seen = some out) (j : DeclId) :
    j ∈ out ↔ WalkMember P R root x owners seen j := by
  induction owners generalizing seen out with
  | nil =>
    cases h
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons owner rest ih =>
    unfold walk at h
    dsimp only at h
    split at h
    · rename_i selected tail hs ht
      cases Option.some.inj h
      rw [List.mem_append,mem_select hs,ih ht]
      constructor
      · intro hj
        rcases hj with ⟨hm,hu⟩ | hr
        · exact .here hm hu
        · exact .next hr
      · intro hj
        cases hj with
        | here hm hu => exact Or.inl ⟨hm,hu⟩
        | next hr => exact Or.inr hr
    · cases h

theorem WalkMember.owner {P : UnitSet} {R : List Remapping} {root j : DeclId} {x : String}
    {owners seen : List DeclId} (h : WalkMember P R root x owners seen j) :
    ∃ owner, owner ∈ owners ∧ j ∈ group P root owner x := by
  induction h with
  | here hm _ => exact ⟨_,List.mem_cons_self,hm⟩
  | next _ ih =>
    obtain ⟨owner,ho,hm⟩ := ih
    exact ⟨owner,List.mem_cons_of_mem _ ho,hm⟩

def ready (P : UnitSet) (R : List Remapping) (root : DeclId) (x : String) (owners : List DeclId) : Bool :=
  (owners.flatMap (group P root · x)).all fun i => (SignatureNormalization.normalize P R i).isSome

/-- Actual inherited overload collection. All candidates normalize, including
first-owner declarations that require no hiding comparison. Failed bases,
roots, normalization or ordering are explicit and cannot cause global fallback. -/
def collect (P : UnitSet) (R : List Remapping) (root : DeclId) (x : String) : Option (List DeclId) :=
  (order P R root).bind fun owners =>
    if ready P R root x owners then walk P R root x owners [] else none

theorem collect_iff {P : UnitSet} {R : List Remapping} {root : DeclId} {x : String} {out : List DeclId} :
    collect P R root x = some out ↔ ∃ owners, order P R root = some owners ∧
      ready P R root x owners = true ∧ walk P R root x owners [] = some out := by
  simp only [collect,Option.bind_eq_some_iff]
  constructor
  · rintro ⟨owners,ho,hw⟩
    split at hw
    · rename_i hr; exact ⟨owners,ho,hr,hw⟩
    · cases hw
  · rintro ⟨owners,ho,hr,hw⟩
    exact ⟨owners,ho,by rw [hr]; exact hw⟩

theorem collect_identity {P : UnitSet} {R : List Remapping} {root j : DeclId} {x : String}
    {out : List DeclId} (h : collect P R root x = some out) (hj : j ∈ out) :
    ∃ d, P.decl? j = some d := by
  obtain ⟨owners,_,_,hw⟩ := collect_iff.mp h
  obtain ⟨owner,_,hm⟩ := ((mem_walk hw j).mp hj).owner
  have hv := (mem_visibleMembers.mp (List.mem_filter.mp hm).1).1
  cases hv with
  | intro _ _ hd _ _ _ _ _ _ => exact ⟨_,hd⟩

abbrev Normalized (P : UnitSet) (R : List Remapping) (ids : List DeclId) : Prop :=
  ∀ i, i ∈ ids → ∃ sig, SignatureNormalization.normalize P R i = some sig

theorem ready_iff {P : UnitSet} {R : List Remapping} {root : DeclId} {x : String} {owners : List DeclId} :
    ready P R root x owners = true ↔ ∀ owner, owner ∈ owners → Normalized P R (group P root owner x) := by
  simp only [ready,List.all_eq_true,Option.isSome_iff_exists]
  constructor
  · intro h owner ho j hj
    exact h j (List.mem_flatMap.mpr ⟨owner,ho,hj⟩)
  · intro h j hj
    obtain ⟨owner,ho,hm⟩ := List.mem_flatMap.mp hj
    exact h owner ho j hm

theorem unhidden_total {P : UnitSet} {R : List Remapping} {target : DeclId} {seen : List DeclId}
    (ht : ∃ sig, SignatureNormalization.normalize P R target = some sig) (hs : Normalized P R seen) :
    ∃ answer, unhidden P R target seen = some answer := by
  induction seen with
  | nil => exact ⟨true,rfl⟩
  | cons i seen ih =>
    cases hd : hides P R i target with
    | none =>
      rcases hides_none_iff.mp hd with hn | hn
      · obtain ⟨sig,hi⟩ := hs i List.mem_cons_self
        rw [hi] at hn; cases hn
      · obtain ⟨sig,hi⟩ := ht
        rw [hi] at hn; cases hn
    | some answer =>
      cases answer with
      | true => exact ⟨false,by simp only [unhidden,hd]⟩
      | false =>
        obtain ⟨result,hr⟩ := ih (fun j hj => hs j (List.mem_cons_of_mem _ hj))
        exact ⟨result,by simpa only [unhidden,hd] using hr⟩

theorem select_total {P : UnitSet} {R : List Remapping} {seen candidates : List DeclId}
    (hs : Normalized P R seen) (hc : Normalized P R candidates) :
    ∃ out, select P R seen candidates = some out := by
  induction candidates with
  | nil => exact ⟨[],rfl⟩
  | cons i rest ih =>
    obtain ⟨keep,hk⟩ := unhidden_total (hc i List.mem_cons_self) hs
    obtain ⟨out,ho⟩ := ih (fun j hj => hc j (List.mem_cons_of_mem _ hj))
    exact ⟨if keep then i :: out else out,by simp only [select,hk,ho]⟩

theorem walk_total {P : UnitSet} {R : List Remapping} {root : DeclId} {x : String}
    {owners seen : List DeclId} (ho : ∀ owner, owner ∈ owners → Normalized P R (group P root owner x))
    (hs : Normalized P R seen) : ∃ out, walk P R root x owners seen = some out := by
  induction owners generalizing seen with
  | nil => exact ⟨[],rfl⟩
  | cons owner rest ih =>
    have hc := ho owner List.mem_cons_self
    obtain ⟨selected,hselected⟩ := select_total hs hc
    have hseen : Normalized P R (seen ++ group P root owner x) := by
      intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact hs j hj
      · exact hc j hj
    obtain ⟨tail,htail⟩ := ih (fun o hm => ho o (List.mem_cons_of_mem _ hm)) hseen
    exact ⟨selected ++ tail,by simp only [walk,hselected,htail]⟩

/-- Independent collection judgment: original visible declarations, prior
owner hiding and successful normalization; no executable walk occurs here. -/
def Collected (P : UnitSet) (R : List Remapping) (root : DeclId) (x : String) (j : DeclId) : Prop :=
  ∃ owners, order P R root = some owners ∧ ready P R root x owners = true ∧
    WalkMember P R root x owners [] j

/-- Unconditional soundness and completeness, including the readiness needed
for every comparison. A desired collection run is not an input premise. -/
theorem collected_iff {P : UnitSet} {R : List Remapping} {root j : DeclId} {x : String} :
    (∃ out, collect P R root x = some out ∧ j ∈ out) ↔ Collected P R root x j := by
  constructor
  · rintro ⟨out,hc,hj⟩
    obtain ⟨owners,ho,hr,hw⟩ := collect_iff.mp hc
    exact ⟨owners,ho,hr,(mem_walk hw j).mp hj⟩
  · rintro ⟨owners,ho,hr,hm⟩
    have empty : Normalized P R [] := fun _ hi => nomatch hi
    obtain ⟨out,hw⟩ := walk_total (ready_iff.mp hr) empty
    exact ⟨out,collect_iff.mpr ⟨owners,ho,hr,hw⟩,(mem_walk hw j).mpr hm⟩

theorem collect_normalizes {P : UnitSet} {R : List Remapping} {root j : DeclId} {x : String}
    {out : List DeclId} (h : collect P R root x = some out) (hj : j ∈ out) :
    ∃ sig, SignatureNormalization.normalize P R j = some sig := by
  obtain ⟨owners,_,hr,hw⟩ := collect_iff.mp h
  obtain ⟨owner,ho,hm⟩ := ((mem_walk hw j).mp hj).owner
  exact ready_iff.mp hr owner ho j hm

end Solidity.Frontend.QualifiedUnits.SignatureMembers
