import Solidity.Backend.StorageOps.ClearDemands
import Solidity.Semantics.RecursiveStorage.Admission

/-! Default observation demands for fresh copy destinations. These are existing
owner queries over the published default, not another default value algorithm.
The private bound is the existing inline rank, never runtime depth or length.
Mappings remain barriers; complete coverage uses the existing CopyPermit. -/
namespace Solidity.Backend.StorageOps.CopyDefaults
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

private def below {n : Nat} (G : Schema n) : Nat → (T : TypeGraph.Ty n) → List (Query G T)
  | 0, _ => []
  | fuel + 1, T =>
    TypeGraph.Ty.casesOn (motive := fun T => List (Query G T)) T
      (fun _ => [.word .nil])
      (fun i => (ClearDemands.positions (G.fields i)).flatMap (fun p =>
        (below G fuel p.1).map (Query.prefix (.cons (.field p.2) .nil))))
      (fun _ => [.length .nil])
      (fun E m => (List.finRange m.val).flatMap (fun i =>
        (below G fuel E).map (Query.prefix
          (.cons (.fixed ⟨i.val, Nat.lt_trans i.isLt m.property.2⟩) .nil))))
      (fun _ _ => [])

private theorem below_stable {n : Nat} (G : Schema n) (a : Nat) :
    ∀ (b : Nat) (T : TypeGraph.Ty n), T.inlineRank G.rank < a →
      T.inlineRank G.rank < b → below G a T = below G b T := by
  induction a with
  | zero => intro b T ha _; omega
  | succ a ih =>
    intro b T ha hb
    cases b with
    | zero => omega
    | succ b =>
      cases T with
      | prim p => rfl
      | array E => rfl
      | mapping K V => rfl
      | node i =>
        simp only [below]
        apply congrArg (fun f => (ClearDemands.positions (G.fields i)).flatMap f)
        funext p
        have ra : p.1.inlineRank G.rank < a := p.2.rank_lt
          (fun f hf => Nat.lt_of_lt_of_le (G.guarded i f hf) (Nat.le_of_lt_succ ha))
        have rb : p.1.inlineRank G.rank < b := p.2.rank_lt
          (fun f hf => Nat.lt_of_lt_of_le (G.guarded i f hf) (Nat.le_of_lt_succ hb))
        rw [ih b p.1 ra rb]
      | fixed E m =>
        have ra : E.inlineRank G.rank < a := by change E.inlineRank G.rank + 1 < a + 1 at ha; omega
        have rb : E.inlineRank G.rank < b := by change E.inlineRank G.rank + 1 < b + 1 at hb; omega
        simp only [below, ih b E ra rb]

/-- Every observable inline default cell, including absent fixed slots.
Dynamic defaults demand only their zero header. -/
def demands {n : Nat} (G : Schema n) (T : TypeGraph.Ty n) : List (Query G T) :=
  below G (T.inlineRank G.rank + 1) T

theorem demands_prim {n : Nat} (G : Schema n) (p : PrimTy) :
    demands G (.prim p) = [.word .nil] := rfl

theorem demands_array {n : Nat} (G : Schema n) (E : TypeGraph.Ty n) :
    demands G (.array E) = [.length .nil] := rfl

theorem demands_mapping {n : Nat} (G : Schema n) (K : PrimTy) (V : TypeGraph.Ty n) :
    demands G (.mapping K V) = [] := rfl

theorem demands_fixed {n : Nat} (G : Schema n) (E : TypeGraph.Ty n) (m : FixedSize) :
    demands G (.fixed E m) = (List.finRange m.val).flatMap (fun i =>
      (demands G E).map (Query.prefix
        (.cons (.fixed ⟨i.val, Nat.lt_trans i.isLt m.property.2⟩) .nil))) := rfl

theorem demands_node {n : Nat} (G : Schema n) (i : Fin n) :
    demands G (.node i) = (ClearDemands.positions (G.fields i)).flatMap (fun p =>
      (demands G p.1).map (Query.prefix (.cons (.field p.2) .nil))) := by
  change (ClearDemands.positions (G.fields i)).flatMap (fun p =>
    (below G (G.rank i) p.1).map (Query.prefix (.cons (.field p.2) .nil))) = _
  apply congrArg (fun f => (ClearDemands.positions (G.fields i)).flatMap f)
  funext p
  exact congrArg (List.map (Query.prefix (.cons (.field p.2) .nil)))
    (below_stable G (G.rank i) (p.1.inlineRank G.rank + 1) p.1
      (p.2.rank_lt (G.guarded i)) (Nat.lt_succ_self _))

private theorem listed_below {n : Nat} (G : Schema n) (a : Nat) :
    ∀ (T : TypeGraph.Ty n) (b : Nat) (hb : T.inlineRank G.rank < b),
      ∀ q ∈ below G a T, q.read (Value.defaultBelow b T hb) = some ClearDemands.zero := by
  induction a with
  | zero => intro T b hb q member; cases member
  | succ a ih =>
    intro T b hb q member
    cases b with
    | zero => exact False.elim ((Nat.not_lt_zero _) hb)
    | succ b =>
      cases T with
      | prim p =>
        simp only [below, List.mem_singleton] at member
        subst q
        exact congrArg some (ClearDemands.default_zero p)
      | array E =>
        simp only [below, List.mem_singleton] at member
        subst q
        rfl
      | mapping K V => cases member
      | node i =>
        simp only [below, List.mem_flatMap] at member
        obtain ⟨p, _, childMember⟩ := member
        obtain ⟨child, inside, same⟩ := List.mem_map.mp childMember
        subst q
        rw [Query.read_prefix _ _ (.cons (.field p.2) .nil) child rfl]
        exact ih p.1 b _ child inside
      | fixed E m =>
        simp only [below, List.mem_flatMap] at member
        obtain ⟨i, _, childMember⟩ := member
        obtain ⟨child, inside, same⟩ := List.mem_map.mp childMember
        subst q
        have found : (Value.defaultBelow (b+1) (.fixed E m) hb).find
            (.cons (.fixed ⟨i.val, Nat.lt_trans i.isLt m.property.2⟩) .nil) =
            some (Value.dflt E) := by
          simp only [Value.defaultBelow, Value.find, Path.read, Step.get,
            dif_pos i.isLt, Slot.getD, Option.bind_some]
        rw [Query.read_prefix _ _ _ child found]
        exact ih E (E.inlineRank G.rank + 1) (Nat.lt_succ_self _) child inside

/-- Every generated cell has the published default's actual zero read. -/
theorem listed_zero {n : Nat} (G : Schema n) (T : TypeGraph.Ty n) :
    ∀ q ∈ demands G T, q.read (Value.dflt T) = some ClearDemands.zero :=
  listed_below G _ T _ _

private theorem complete_below {n : Nat} (G : Schema n) (a : Nat) :
    ∀ (T : TypeGraph.Ty n) (_ha : T.inlineRank G.rank < a), CopyPermit G T →
      ∀ (b : Nat) (hb : T.inlineRank G.rank < b) (q : Query G T) (word : Semantics.Word),
        q.read (Value.defaultBelow b T hb) = some word → q ∈ below G a T := by
  induction a with
  | zero => intro T ha; exact False.elim ((Nat.not_lt_zero _) ha)
  | succ a ih =>
    intro T ha permit b hb q word observed
    cases b with
    | zero => exact False.elim ((Nat.not_lt_zero _) hb)
    | succ b =>
      cases T with
      | prim p =>
        cases q with
        | word path => cases path with
          | nil => exact List.mem_cons_self
          | cons step rest => cases step
        | length path => cases path with | cons step rest => cases step
      | mapping K V => exact False.elim permit.no_mapping
      | array E =>
        cases q with
        | word path => cases path with | cons step rest => cases step with
          | index i =>
            simp only [Query.read, Value.observe, Value.find, Path.read, Value.defaultBelow,
              Step.get, Nat.not_lt_zero] at observed
            cases observed
        | length path => cases path with
          | nil => exact List.mem_cons_self
          | cons step rest => cases step with
            | index i =>
              simp only [Query.read, Value.observe, Value.find, Path.read, Value.defaultBelow,
                Step.get, Nat.not_lt_zero] at observed
              cases observed
      | node i =>
        have childComplete : ∀ {U : TypeGraph.Ty n} (position : Field (G.fields i) U)
            (child : Query G U),
            (child.prefix (.cons (.field position) .nil)).read
              (Value.defaultBelow (b+1) (.node i) hb) = some word →
            child.prefix (.cons (.field position) .nil) ∈ below G (a+1) (.node i) := by
          intro U position child read
          rw [Query.read_prefix _ _ (.cons (.field position) .nil) child rfl] at read
          have ra : U.inlineRank G.rank < a := position.rank_lt
            (fun f hf => Nat.lt_of_lt_of_le (G.guarded i f hf) (Nat.le_of_lt_succ ha))
          have member := ih U ra (permit.step (.field position)) b _ child word read
          exact List.mem_flatMap.mpr ⟨⟨U,position⟩, ClearDemands.positions_mem position,
            List.mem_map.mpr ⟨child,member,rfl⟩⟩
        cases q with
        | word path => cases path with | cons step rest => cases step with
          | field position => exact childComplete position (.word rest) observed
        | length path => cases path with | cons step rest => cases step with
          | field position => exact childComplete position (.length rest) observed
      | fixed E m =>
        have childComplete : ∀ (i : Index) (child : Query G E),
            (child.prefix (.cons (.fixed i) .nil)).read
              (Value.defaultBelow (b+1) (.fixed E m) hb) = some word →
            child.prefix (.cons (.fixed i) .nil) ∈ below G (a+1) (.fixed E m) := by
          intro i child read
          by_cases inside : i.val < m.val
          · have found : (Value.defaultBelow (b+1) (.fixed E m) hb).find
                (.cons (.fixed i) .nil) = some (Value.dflt E) := by
              simp only [Value.defaultBelow, Value.find, Path.read, Step.get,
                dif_pos inside, Slot.getD, Option.bind_some]
            rw [Query.read_prefix _ _ _ child found] at read
            have ra : E.inlineRank G.rank < a := by
              change E.inlineRank G.rank + 1 < a+1 at ha; omega
            have member := ih E ra (permit.step (.fixed i)) _ (Nat.lt_succ_self _) child word read
            exact List.mem_flatMap.mpr ⟨⟨i.val,inside⟩, ClearDemands.fin_mem _,
              List.mem_map.mpr ⟨child,member,rfl⟩⟩
          · have missing : (Value.defaultBelow (b+1) (.fixed E m) hb).find
                (.cons (.fixed i) .nil) = none := by
              simp only [Value.defaultBelow, Value.find, Path.read, Step.get, dif_neg inside,
                Option.bind_none]
            cases child <;> simp only [Query.read, Query.prefix, Value.observe_append,
              missing, Option.bind_none, Option.map_none] at read <;> cases read
        cases q with
        | word path => cases path with | cons step rest => cases step with
          | fixed i => exact childComplete i (.word rest) observed
        | length path => cases path with | cons step rest => cases step with
          | fixed i => exact childComplete i (.length rest) observed

/-- Complete default visibility uses the already checked mapping-free source
copy permit; no new exclusion, value representation or source restriction. -/
theorem complete {n : Nat} (G : Schema n) (T : TypeGraph.Ty n)
    (permit : CopyPermit G T) (q : Query G T) (word : Semantics.Word)
    (observed : q.read (Value.dflt T) = some word) : q ∈ demands G T :=
  complete_below G _ T (Nat.lt_succ_self _) permit _ (Nat.lt_succ_self _) q word observed

/-- Exact successful-query coverage, including defaulted absent fixed cells. -/
theorem mem_iff {n : Nat} (G : Schema n) (T : TypeGraph.Ty n)
    (permit : CopyPermit G T) (q : Query G T) :
    q ∈ demands G T ↔ q.read (Value.dflt T) = some ClearDemands.zero :=
  ⟨listed_zero G T q,complete G T permit q ClearDemands.zero⟩

private theorem properties_below {n : Nat} (G : Schema n) (a : Nat) :
    ∀ (T : TypeGraph.Ty n) (b : Nat) (hb : T.inlineRank G.rank < b),
      ∀ q ∈ below G a T, q.compatible (Value.defaultBelow b T hb) ∧ q.supported := by
  induction a with
  | zero => intro T b hb q member; cases member
  | succ a ih =>
    intro T b hb q member
    cases b with
    | zero => exact False.elim ((Nat.not_lt_zero _) hb)
    | succ b =>
      cases T with
      | prim p =>
        simp only [below, List.mem_singleton] at member
        subst q
        exact ⟨True.intro,True.intro⟩
      | array E =>
        simp only [below, List.mem_singleton] at member
        subst q
        exact ⟨⟨Nat.zero_le _,Nat.zero_le _⟩,True.intro⟩
      | mapping K V => cases member
      | node i =>
        simp only [below, List.mem_flatMap] at member
        obtain ⟨p, _, childMember⟩ := member
        obtain ⟨child, inside, same⟩ := List.mem_map.mp childMember
        subst q
        rw [Query.compatible_prefix _ _ (.cons (.field p.2) .nil) child rfl,
          Query.supported_prefix]
        have childBound : p.1.inlineRank G.rank < b := p.2.rank_lt
          (fun f hf => Nat.lt_of_lt_of_le (G.guarded i f hf) (Nat.le_of_lt_succ hb))
        have props := ih p.1 b childBound child inside
        exact ⟨props.1,⟨⟨True.intro,True.intro⟩,props.2⟩⟩
      | fixed E m =>
        simp only [below, List.mem_flatMap] at member
        obtain ⟨i, _, childMember⟩ := member
        obtain ⟨child, inside, same⟩ := List.mem_map.mp childMember
        subst q
        have found : (Value.defaultBelow (b+1) (.fixed E m) hb).find
            (.cons (.fixed ⟨i.val, Nat.lt_trans i.isLt m.property.2⟩) .nil) =
            some (Value.dflt E) := by
          simp only [Value.defaultBelow, Value.find, Path.read, Step.get,
            dif_pos i.isLt, Slot.getD, Option.bind_some]
        rw [Query.compatible_prefix _ _ _ child found,Query.supported_prefix]
        have props := ih E (E.inlineRank G.rank+1) (Nat.lt_succ_self _) child inside
        exact ⟨props.1,⟨⟨i.isLt,True.intro⟩,props.2⟩⟩

/-- Support and terminal-header bounds are derived for the generated defaults,
rather than assumed as a desired postrepresentation premise. -/
theorem listed_properties {n : Nat} (G : Schema n) (T : TypeGraph.Ty n) :
    ∀ q ∈ demands G T, q.compatible (Value.dflt T) ∧ q.supported :=
  properties_below G _ T _ _

noncomputable def updates {n : Nat} (G : Schema n) (T : TypeGraph.Ty n)
    (base : Solidity.Storage.Loc) : List (Solidity.Storage.Loc × Semantics.Word) :=
  (demands G T).map (fun q => (q.location base,ClearDemands.zero))

/-- A finite query-generated initialization sequence, not a new implementation
of the published default value or emitted runtime traversal. -/
noncomputable def numericInit {n N : Nat} (G : Schema n) (T : TypeGraph.Ty n)
    (base : Solidity.Storage.Loc) (hash : Solidity.Storage.Pre → Nat)
    (machine : WordStore) : WordStore :=
  (updates G T base).foldl (fun m op => writeWord m (op.1.word N hash) op.2) machine

/-- Every chosen default query is represented after the actual generated zero
writes, even when its old graph read failed and numeric cell held garbage. -/
theorem represented {n : Nat} (G : Schema n) (T : TypeGraph.Ty n)
    (permit : CopyPermit G T) (queries : List (Query G T))
    (supported : ∀ q ∈ queries, q.supported)
    (base : Solidity.Storage.Loc) (store : Store) :
    Represented (Value.dflt T) queries base
      ((updates G T base).foldl (fun w op => write w op.1 op.2) store) := by
  intro q member
  refine ⟨supported q member,?_,?_⟩
  · cases read : q.read (Value.dflt T) with
    | none =>
      cases q with
      | word path => exact True.intro
      | length path =>
        simp only [Query.read,Option.map_eq_none_iff] at read
        simp only [Query.compatible,read]
    | some word => exact (listed_properties G T q (complete G T permit q word read)).1
  · intro word observed
    have inside := complete G T permit q word observed
    have same : word = ClearDemands.zero :=
      Option.some.inj (observed.symm.trans (listed_zero G T q inside))
    subst word
    simp only [updates,List.foldl_map]
    exact ClearDemands.fold_zero_member (demands G T) base store q inside

/-- Numeric execution is tied to the exact finite per-run hash/region premise
and actual generated writes; no global injectivity or old cell assumption. -/
theorem numeric_transport {n N L R : Nat} (G : Schema n) (T : TypeGraph.Ty n)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (initial : Transport N hash locations store machine)
    (covered : ∀ q ∈ demands G T, q.location base ∈ locations) :
    Transport N hash locations
      ((updates G T base).foldl (fun w op => write w op.1 op.2) store)
      (numericInit (N := N) G T base hash machine) := by
  apply transport_sequence run initial (updates G T base)
  intro op member
  obtain ⟨q,inside,same⟩ := List.mem_map.mp member
  subst op
  exact covered q inside

theorem numeric_outside {n N : Nat} (G : Schema n) (T : TypeGraph.Ty n)
    (base : Solidity.Storage.Loc) (hash : Solidity.Storage.Pre → Nat)
    (machine : WordStore) (address : Nat)
    (outside : ∀ q ∈ demands G T, address ≠ (q.location base).word N hash) :
    numericInit (N := N) G T base hash machine address = machine address := by
  apply sequence_outside_frame N hash machine (updates G T base) address
  intro op member
  obtain ⟨q,inside,same⟩ := List.mem_map.mp member
  subst op
  exact outside q inside

/-- Complete selected owner representation and actual numeric read agreement
for generated initialization, from only OLD symbolic/numeric transport. -/
theorem complete_numeric {n N L R : Nat} (G : Schema n) (T : TypeGraph.Ty n)
    (permit : CopyPermit G T) (queries : List (Query G T))
    (supported : ∀ q ∈ queries, q.supported)
    (base : Solidity.Storage.Loc) (hash : Solidity.Storage.Pre → Nat)
    (preimages : List Solidity.Storage.Pre) (store : Store) (machine : WordStore)
    (run : FiniteRun N L R hash preimages
      (((demands G T) ++ queries).map (fun q => q.location base)))
    (initial : Transport N hash (((demands G T) ++ queries).map (fun q => q.location base))
      store machine) :
    let afterStore := (updates G T base).foldl (fun w op => write w op.1 op.2) store
    let afterMachine := numericInit (N := N) G T base hash machine
    Represented (Value.dflt T) queries base afterStore ∧
    Transport N hash (((demands G T) ++ queries).map (fun q => q.location base))
      afterStore afterMachine ∧
    ∀ q ∈ queries, ∀ word, q.read (Value.dflt T) = some word →
      afterMachine ((q.location base).word N hash) = word := by
  have related := represented G T permit queries supported base store
  have transported := numeric_transport G T run base store machine initial (fun q member =>
    List.mem_map.mpr ⟨q,List.mem_append.mpr (Or.inl member),rfl⟩)
  refine ⟨related,transported,?_⟩
  intro q member word observed
  exact related.numeric transported q member
    (List.mem_map.mpr ⟨q,List.mem_append.mpr (Or.inr member),rfl⟩) word observed

/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.demands' does not depend on any axioms -/
#guard_msgs in #print axioms demands
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.demands_prim' does not depend on any axioms -/
#guard_msgs in #print axioms demands_prim
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.demands_array' does not depend on any axioms -/
#guard_msgs in #print axioms demands_array
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.demands_mapping' does not depend on any axioms -/
#guard_msgs in #print axioms demands_mapping
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.demands_fixed' does not depend on any axioms -/
#guard_msgs in #print axioms demands_fixed
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.demands_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms demands_node
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.listed_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms listed_zero
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mem_iff
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.listed_properties' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms listed_properties
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.updates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updates
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.numericInit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numericInit
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.numeric_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numeric_transport
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.numeric_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numeric_outside
/-- info: 'Solidity.Backend.StorageOps.CopyDefaults.complete_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete_numeric

end Solidity.Backend.StorageOps.CopyDefaults
