import Solidity.Lowering.V07.RecursiveGraph
import Solidity.Lowering.V07.GraphAdmissionBoundary
import Solidity.Lowering.V07.PrimitiveGraphControls

namespace Solidity.Lowering.V07.RecursiveGraphControls
open RecursiveGraph

def refDecl (s to : String) : Source.Decl :=
  ⟨.struct,s,none,true,.struct s (.structMember (.userType ⟨to,[]⟩) "next") .nil⟩
def chain : Source.Env := ⟨[PrimitiveGraphControls.skip,refDecl "A" "B",refDecl "B" "C",
  GraphIdentityControls.declaration "C"]⟩

theorem chain_resolved (loc : Source.DataLoc) :
    chain.structFields ⟨none,"A"⟩ loc = some [("next",.struct loc ⟨none,"B"⟩)] := rfl

theorem chain_success (loc : Source.DataLoc) :
    (produce "actual-three-inline-chain" chain loc).isSome = true := by
  cases loc <;> decide

def chainResult (loc : Source.DataLoc) :=
  (produce "actual-three-inline-chain" chain loc).get (chain_success loc)

theorem chain_ranks (loc : Source.DataLoc) :
    (chainResult loc).1.rank ⟨0,by decide⟩ = 3 ∧
    (chainResult loc).1.rank ⟨1,by decide⟩ = 2 ∧
    (chainResult loc).1.rank ⟨2,by decide⟩ = 1 := by
  cases loc <;> decide

theorem chain_source_identity (loc : Source.DataLoc) :
    (chainResult loc).1.declId ⟨0,by decide⟩ = 1 ∧
    (chainResult loc).1.declId ⟨1,by decide⟩ = 2 ∧
    (chainResult loc).1.declId ⟨2,by decide⟩ = 3 := by
  cases loc <;> decide

theorem chain_typed_edge (loc : Source.DataLoc) :
    (chainResult loc).1.fields ⟨0,by decide⟩ = [("next",.node ⟨1,by decide⟩)] ∧
    (chainResult loc).1.fields ⟨1,by decide⟩ = [("next",.node ⟨2,by decide⟩)] := by
  cases loc <;> decide

theorem guarded_self_success (loc : Source.DataLoc) :
    (produce "actual-guarded-self" GraphAdmissionBoundary.guardedEnv loc).isSome = true := by
  cases loc <;> decide

theorem inline_self_failure (loc : Source.DataLoc) :
    (produce "inline-self" GraphAdmissionBoundary.directEnv loc).isNone = true := by
  cases loc <;> decide

def mutualEnv : Source.Env := ⟨[refDecl "A" "B",refDecl "B" "A"]⟩

theorem inline_mutual_failure (loc : Source.DataLoc) :
    (produce "inline-mutual" mutualEnv loc).isNone = true := by
  cases loc <;> decide

def guardDecl (s to : String) : Source.Decl :=
  ⟨.struct,s,none,true,.struct s (.structMember (.array (.userType ⟨to,[]⟩) .none) "next") .nil⟩
def guardedMutual : Source.Env := ⟨[guardDecl "A" "B",refDecl "B" "A"]⟩

theorem guarded_mutual_success (loc : Source.DataLoc) :
    (produce "one-guard-breaks-inline-cycle" guardedMutual loc).isSome = true := by
  cases loc <;> decide

def fixedGuardDecl : Source.Decl :=
  ⟨.struct,"Loop",none,true,.struct "Loop"
    (.structMember (.array (.array (.userType ⟨"Loop",[]⟩) .none)
      (.some (.lit (.num (.dec 2 0 0))))) "next") .nil⟩
def fixedGuard : Source.Env := ⟨[fixedGuardDecl]⟩

theorem fixed_guard_success (loc : Source.DataLoc) :
    (produce "fixed-array-around-guard" fixedGuard loc).isSome = true := by
  cases loc <;> decide

theorem fixed_guard_weight : ranks fixedGuard .storage ⟨0,by decide⟩ = 2 := by decide

def fixedInlineDecl : Source.Decl :=
  ⟨.struct,"Loop",none,true,.struct "Loop"
    (.structMember (.array (.userType ⟨"Loop",[]⟩) (.some (.lit (.num (.dec 2 0 0))))) "next") .nil⟩
def fixedInline : Source.Env := ⟨[fixedInlineDecl]⟩

theorem fixed_inline_failure : (produce "fixed-inline-self" fixedInline .storage).isNone = true := by decide

def mapDecl : Source.Decl :=
  ⟨.struct,"Loop",none,true,.struct "Loop"
    (.structMember (.mapping (.elem (.int false 8 (by decide)) (by decide)) none
      (.userType ⟨"Loop",[]⟩) none) "next") .nil⟩
def mappingEnv : Source.Env := ⟨[mapDecl]⟩

theorem mapping_storage_success : (produce "mapping-guard" mappingEnv .storage).isSome = true := by decide

theorem mapping_memory_resolution_failure :
    mappingEnv.structFields GraphAdmissionBoundary.loopName .memory = none ∧
    (produce "mapping-memory-component" mappingEnv .memory).isNone = true := by decide

/-- Stronger than a checker failure: the existing source resolution and
certificate interface admit NO graph at this location, for ANY graph size. -/
theorem mapping_memory_not_certifiable {n : Nat} (G : TypeGraph.Schema n) :
    ¬ Nonempty (DeclarationGraph mappingEnv .memory G) := by
  intro ⟨c⟩
  obtain ⟨i,hi⟩ := c.complete ⟨0,by decide⟩ rfl
  have hn := c.source_name i
  have hs := c.source_scope i
  rw [hi] at hn hs
  change "Loop" = (c.sourceName i).name at hn
  change none = (c.sourceName i).scope at hs
  have ni : c.sourceName i = GraphAdmissionBoundary.loopName := by
    change Source.DeclName.mk (c.sourceName i).scope (c.sourceName i).name =
      Source.DeclName.mk none "Loop"
    exact congr (congrArg Source.DeclName.mk hs.symm) hn.symm
  have fields := c.fields_resolve i
  rw [ni,mapping_memory_resolution_failure.1] at fields
  cases fields

def mappingUnit : Source.Syn .unit := .unit (.cons (.topPart mapDecl.node) .nil)

/-- Current published metadata admits this storage-capable declaration for
both pipelines. This is not a fabricated frozen P8 Producer inhabitant. -/
theorem mapping_metadata_accepts (s : Source.Settings) :
    Source.WellFormed (Source.resolveUnit s mappingUnit) ∧
    Source.InProfileSyntax (Source.resolveUnit s mappingUnit) ∧
    Frontend.Static.strictMetadataChecker.check (Source.resolveUnit s mappingUnit) () () = true := by
  have hd : (Source.resolveUnit s mappingUnit).unit.decls = [mapDecl] := rfl
  refine ⟨⟨rfl,?_,?_,?_,show 0 ≤ 1 from by decide,?_,?_,?_,?_,?_⟩,rfl,rfl⟩
  · rw [hd]
    intro d hm hk
    cases List.mem_singleton.mp hm
    rcases hk with hk | hk <;> cases hk
  · rw [hd]
    exact .cons (by intro d hm; nomatch hm) .nil
  · intro ws hw; nomatch hw
  · change ∀ d ∈ [mapDecl], d.typesOK mappingEnv = true
    decide
  · change ∀ d ∈ [mapDecl], d.placementOK mappingEnv = true
    decide
  · change ∀ d ∈ [mapDecl], d.isConst = true → d.init?.isSome = true
    decide
  · intro d hm e he
    rw [hd] at hm
    cases List.mem_singleton.mp hm
    cases he
  · intro d hm hb
    rw [hd] at hm
    cases List.mem_singleton.mp hm
    cases hb

theorem mapping_no_all_locations :
    ¬ (∀ loc : Source.DataLoc, ∃ n, ∃ G : TypeGraph.Schema n,
      Nonempty (DeclarationGraph mappingEnv loc G)) := by
  intro all
  obtain ⟨n,G,c⟩ := all .memory
  exact mapping_memory_not_certifiable G c

theorem wrong_constant_rank :
    ¬ ((TypeGraph.Ty.node ⟨1,by decide⟩ : TypeGraph.Ty 3).inlineRank (fun _ => 1) < 1) := by decide

theorem collapsed_declaration_wrong : (chainResult .storage).1.declId ⟨0,by decide⟩ ≠ 0 := by decide

theorem unresolved_field_failure :
    (produce "unresolved" PrimitiveGraphControls.unresolvedEnv .storage).isNone = true := by decide

theorem duplicate_identity_failure :
    (produce "duplicate" PrimitiveGraphControls.duplicated .storage).isNone = true := by decide

theorem unsupported_bytes_still_open :
    (produce "bytes-not-a-profile-exclusion" PrimitiveGraphControls.byteEnv .storage).isNone = true := by decide

def enumDecl : Source.Decl := ⟨.enum,"Choice",none,true,.enum "Choice" "One" ["Two"]⟩
def udvtDecl : Source.Decl := ⟨.udvt,"Distance",none,true,.udvt "Distance" (.int false 16 (by decide))⟩
def wrappedDecl : Source.Decl :=
  ⟨.struct,"Wrapped",none,true,.struct "Wrapped"
    (.structMember (.userType ⟨"Choice",[]⟩) "choice")
    (.cons (.structMember (.userType ⟨"Distance",[]⟩) "distance") .nil)⟩
def wrappedEnv : Source.Env := ⟨[enumDecl,udvtDecl,wrappedDecl]⟩

theorem enum_udvt_source_fields (loc : Source.DataLoc) :
    wrappedEnv.structFields ⟨none,"Wrapped"⟩ loc =
      some [("choice",.enum ⟨none,"Choice"⟩),("distance",.udvt ⟨none,"Distance"⟩)] := rfl

theorem enum_udvt_computed_success (loc : Source.DataLoc) :
    (produce "enum-udvt" wrappedEnv loc).isSome = true ∧
    targetFields wrappedEnv loc ⟨0,by decide⟩ = [("choice",.prim .uint),("distance",.prim .uint)] := by
  cases loc <;> decide

theorem fixed_zero_capacity_failure :
    (lowerType chain.layout (PrimitiveGraph.name chain)
      (.array .memory .bool (some 0))).isNone = true := by decide

theorem fixed_word_capacity_failure :
    (lowerType chain.layout (PrimitiveGraph.name chain)
      (.array .storage .bool (some (2^256)))).isNone = true := by decide

theorem fixed_positive_capacity_success :
    ((lowerType chain.layout (PrimitiveGraph.name chain)
      (.array .memory .bool (some 3))).map Subtype.val) =
      some (.fixed (.prim .bool) ⟨3,by decide⟩) := by decide

def excessiveEnumLayout : Source.Layout :=
  { chain.layout with enumSize := fun _ => 2^256+1 }

theorem excessive_enum_capacity_failure :
    (lowerType excessiveEnumLayout (PrimitiveGraph.name chain) (.enum ⟨none,"TooLarge"⟩)).isNone = true := by decide

theorem empty_environment_success :
    (produce "zero-actual-declarations" (Source.Env.mk []) .storage).isSome = true := by decide

end Solidity.Lowering.V07.RecursiveGraphControls
