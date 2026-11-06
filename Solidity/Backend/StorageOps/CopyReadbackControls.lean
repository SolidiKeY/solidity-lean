import Solidity.Backend.StorageOps.CopyReadback
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Actual generated readback and discriminating numeric/symbolic alias
controls. Failed malformed queries are never interpreted as numeric zero. -/
namespace Solidity.Backend.StorageOps.CopyReadbackControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open CopyReadback
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def seven : Semantics.Word := ⟨7,by decide⟩
private abbrev Arr : TypeGraph.Ty 0 := .array (.prim .bool)
private def value (flag : Bool) : Value CopyDemandControls.graph Arr :=
  .array ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .present (.prim (p := .bool) flag))
private def query : Query CopyDemandControls.graph Arr := .word (.cons (.index ⟨0,by decide⟩) .nil)
private def header : Query CopyDemandControls.graph Arr := .length .nil
private def hash (p : Solidity.Storage.Pre) := if p = .data 0 then 8 else if p = .data 1 then 16 else 0
private def initial : WordStore := fun a => if a = 0 ∨ a = 1 ∨ a = 8 ∨ a = 9 ∨ a = 17 then one else if a = 16 then zero else seven
private def locations : List Solidity.Storage.Loc := [.data (.root 0) 0,.root 0,.data (.root 1) 0,.root 1,.data (.root 0) 1]
private theorem run : FiniteRun 128 2 2 hash [.data 0,.data 1] locations := by
  constructor
  · intro p; simp only [hash]; split <;> (first | decide | (split <;> decide))
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
private theorem before_src : Represented (value false) (ClearDemands.demands (value false)) (.root 1)
    (fun l => initial (l.word 128 hash)) := by
  intro q member
  change q ∈ [query,header] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [query,header,Query.supported,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some zero = some word at observed; cases observed; rfl)
    | (intro word observed; change some one = some word at observed; cases observed; rfl)

/-- Inhabited application with BOTH generated destination writes, actual
SOURCE owner evidence and GOOD numeric regions. -/
theorem represented_readback :
    CopyWrites.numericCopy (N := 128) (value true) (value false) (.root 0) (.root 1) hash initial 8 =
    traceWord query (CopyWrites.queryWrites (value true) (value false)
      (fun d => (d.read (value false)).getD zero)) (initial 8) := by
  apply represented_copy_trace (value true) (value false) query (.root 0) (.root 1)
    (fun l => initial (l.word 128 hash)) initial run before_src (fun _ _ => rfl)
  · intro d member
    change d ∈ [query,header] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp only [locations,List.mem_cons,List.not_mem_nil,or_false] <;> first | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact List.mem_cons_self
  · intro d member
    change d ∈ [query,header] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  · intro d member same
    change d ∈ [query,header] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · rfl
    · cases same

private def numericView (m : WordStore) := (m 0,m 8,m 9,m 1,m 16,m 17,m 127)
private def badHash (p : Solidity.Storage.Pre) := if p = .data 1 then 16 else 0

/-- Complete initial/correct/bad-region numeric vectors. With a bad region,
the last header overwrites the payload address; the typed trace still says0. -/
theorem actual_and_bad_region :
    (numericView initial,numericView (CopyWrites.numericCopy (N := 128) (value true) (value false)
      (.root 0) (.root 1) hash initial),
     numericView (CopyWrites.numericCopy (N := 128) (value true) (value false)
      (.root 0) (.root 1) badHash initial),
     traceWord query (CopyWrites.queryWrites (value true) (value false)
       (fun d => initial ((d.location (.root 1)).word 128 badHash))) (initial 0),
     query.read (recursiveCopy (value true) (value false))) =
    ((one,one,one,one,zero,one,seven),(one,zero,one,one,zero,one,seven),
     (one,one,one,one,zero,one,seven),zero,some zero) := by
  have trace : traceWord query (CopyWrites.queryWrites (value true) (value false)
       (fun d => initial ((d.location (.root 1)).word 128 badHash))) (initial 0) = zero := by
    change traceWord query [(query,zero),(header,one)] one = zero
    have different : header ≠ query := by intro same; cases same
    simp only [traceWord,List.foldl_cons,List.foldl_nil,ite_true,if_neg different]
  rw [trace]
  rfl

private def sizeOne : FixedSize := ⟨1,by decide⟩
private def aliasGraph : Schema 1 where
  origin := "v10-copy-readback-alias"
  declId := fun _ => 0
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "Pair"
  fields := fun _ => [("fixed",.fixed (.prim .bool) sizeOne),("flag",.prim .bool)]
  rank := fun _ => 2
  nonempty := by intro i; rfl
  distinct := by intro i; decide
  guarded := by
    intro i f member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
private abbrev Node : TypeGraph.Ty 1 := .node 0
private def node (flag : Bool) : Value aliasGraph Node :=
  .node (Fields.set (Fields.set (fun {_} _ => Value.dflt _)
    .here (.fixed (fun _ => .present (.prim (p := .bool) false)))) (.there .here) (.prim (p := .bool) flag))
private def malformed : Query aliasGraph Node :=
  .word (.cons (.field .here) (.cons (.fixed ⟨1,by decide⟩) .nil))
private def scalar : Query aliasGraph Node := .word (.cons (.field (.there .here)) .nil)
private def aliasHash : Solidity.Storage.Pre → Nat := fun _ => 0
private def aliasInitial : WordStore := fun a => if a = 3 then one else zero
private theorem alias_run : FiniteRun 4 4 4 aliasHash [] [.root 0,.root 1] := by
  constructor
  · intro _; change 0 < 4; decide
  · decide
  · decide
  · decide
  · intro l member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> intro p inside <;> cases inside

/-- GOOD finite regions do not equate distinct typed queries. A malformed fixed
index aliases a valid sibling symbolically. Its graph read fails; its numeric
cell changes. The explicit finite query-separation premise is indispensable. -/
theorem symbolic_alias_boundary :
    FiniteRun 4 4 4 aliasHash [] [.root 0,.root 1] ∧
    malformed.location (.root 0) = scalar.location (.root 0) ∧
    malformed ≠ scalar ∧ ¬ malformed.supported ∧
    (malformed.read (node false),malformed.read (recursiveCopy (node false) (node true)),
     aliasInitial 1,CopyWrites.numericCopy (N := 4) (node false) (node true) (.root 0) (.root 2) aliasHash aliasInitial 1,
     traceWord malformed (CopyWrites.queryWrites (node false) (node true)
       (fun d => aliasInitial ((d.location (.root 2)).word 4 aliasHash))) (aliasInitial 1)) =
      (none,none,zero,one,zero) := by
  have trace : traceWord malformed (CopyWrites.queryWrites (node false) (node true)
       (fun d => aliasInitial ((d.location (.root 2)).word 4 aliasHash))) (aliasInitial 1) = zero := by
    apply traceWord_outside
    intro op member
    change op ∈ [(.word (.cons (.field .here) (.cons (.fixed ⟨0,by decide⟩) .nil)),zero),(scalar,one)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals intro same
    all_goals have observed := congrArg (Query.read (node false)) same
    all_goals change some zero = none at observed
    all_goals cases observed
  refine ⟨alias_run,rfl,?_,?_,?_⟩
  · intro same
    cases same
  · simp only [malformed,Query.supported,PathSupported,StepSupported]
    decide
  · rw [trace]
    rfl

private abbrev Fresh : TypeGraph.Ty 0 := .fixed (.prim .bool) sizeOne
private def freshSource : Value CopyDemandControls.graph Fresh := .fixed (fun _ => .present (.prim true))
private def freshQuery : Query CopyDemandControls.graph Fresh := .word (.cons (.fixed ⟨0,by decide⟩) .nil)
private def freshPermit : CopyPermit CopyDemandControls.graph Fresh :=
  CopyPermit.checked (fun i => nomatch i) (by decide)
private def freshReader (q : Query CopyDemandControls.graph Fresh) := (q.read freshSource).getD zero

/-- The actual fresh slot initializes before present-copy overwrite. Reversing
those two phases erases the successful payload. Old cell garbage is7. -/
theorem fresh_initialization_order :
    (traceWord freshQuery (CopyWrites.slotWrites .absent (.present freshSource) freshReader) seven,
     traceWord freshQuery (CopyWrites.queryWrites (Value.dflt Fresh) freshSource freshReader ++
       CopyWrites.zeros (CopyDefaults.demands CopyDemandControls.graph Fresh)) seven,
     freshQuery.read ((recursiveSlot Slot.absent (.present freshSource)).getD (Value.dflt Fresh))) =
      (one,zero,some one) := by
  have correct := fresh_slot freshSource freshPermit freshQuery freshReader seven zero rfl
  have copied : traceWord freshQuery (CopyWrites.queryWrites (Value.dflt Fresh) freshSource freshReader) zero = one := by
    change traceWord freshQuery [(freshQuery,zero),(freshQuery,one)] zero = one
    simp only [traceWord,List.foldl_cons,List.foldl_nil,ite_true]
  have wrong : traceWord freshQuery (CopyWrites.queryWrites (Value.dflt Fresh) freshSource freshReader ++
       CopyWrites.zeros (CopyDefaults.demands CopyDemandControls.graph Fresh)) seven = zero := by
    rw [traceWord_append]
    exact default_readback freshPermit freshQuery _ zero rfl
  rw [correct,copied,wrong]
  rfl

private def twoSize : FixedSize := ⟨2,by decide⟩
private def nestedType : Nat → TypeGraph.Ty 0
  | 0 => .prim .bool
  | d + 1 => .fixed (nestedType d) twoSize
private def nestedPath : (d : Nat) → TypeGraph.Path CopyDemandControls.graph (nestedType d) (.prim .bool)
  | 0 => .nil
  | d + 1 => .cons (.fixed ⟨0,by decide⟩) (nestedPath d)

/-- Arbitrary finite typed common prefixes transport BOTH overwrite phases;
the distinct fixed sibling query retains its initial scalar word. No depth cap is admitted. -/
theorem arbitrary_prefix (depth : Nat) :
    let leaf : Query CopyDemandControls.graph (.prim .bool) := .word .nil
    let child := leaf.prefix (nestedPath depth)
    let childLog := CopyWrites.prefixWrites (nestedPath depth) [(leaf,zero),(leaf,one)]
    let first : TypeGraph.Path CopyDemandControls.graph (.fixed (nestedType depth) twoSize) (nestedType depth) := .cons (.fixed ⟨0,by decide⟩) .nil
    let second : TypeGraph.Path CopyDemandControls.graph (.fixed (nestedType depth) twoSize) (nestedType depth) := .cons (.fixed ⟨1,by decide⟩) .nil
    (traceWord (child.prefix first) (CopyWrites.prefixWrites first childLog) seven,
     traceWord (child.prefix second) (CopyWrites.prefixWrites first childLog) seven) = (one,seven) := by
  dsimp only
  rw [prefix_trace,prefix_trace]
  have outside := fixed_trace (G := CopyDemandControls.graph) (m := twoSize)
    ⟨1,by decide⟩ ⟨0,by decide⟩ (by decide)
    ((Query.word .nil).prefix (nestedPath depth))
    (CopyWrites.prefixWrites (nestedPath depth) [(.word .nil,zero),(.word .nil,one)]) seven
  rw [outside]
  simp only [traceWord,List.foldl_cons,List.foldl_nil,ite_true]

/-- info: 'Solidity.Backend.StorageOps.CopyReadbackControls.represented_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_readback
/-- info: 'Solidity.Backend.StorageOps.CopyReadbackControls.actual_and_bad_region' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_and_bad_region
/-- info: 'Solidity.Backend.StorageOps.CopyReadbackControls.symbolic_alias_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms symbolic_alias_boundary
/-- info: 'Solidity.Backend.StorageOps.CopyReadbackControls.fresh_initialization_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_initialization_order
/-- info: 'Solidity.Backend.StorageOps.CopyReadbackControls.arbitrary_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms arbitrary_prefix

end Solidity.Backend.StorageOps.CopyReadbackControls
