import Solidity.Lowering.V07.DeclarationGraph
import Solidity.Source.WellFormed
import Solidity.Frontend.Static.Certificates

/-! Exact admission boundary over existing Source syntax/typing and TypeGraph.
A countermodel to using current WellFormed alone is not a Source exclusion or
permission to weaken accepted-source admission. No owner implementation edited. -/
namespace Solidity.Lowering.V07.GraphAdmissionBoundary

def loopName : Source.DeclName := ⟨none,"Loop"⟩
def directNode : Source.Syn (.part true) :=
  .struct "Loop" (.structMember (.userType ⟨"Loop",[]⟩) "next") .nil

def directUnit : Source.Syn .unit := .unit (.cons (.topPart directNode) .nil)
def directDecl : Source.Decl := ⟨.struct,"Loop",none,true,directNode⟩
def directEnv : Source.Env := directUnit.env

theorem direct_declarations : directUnit.decls = [directDecl] := rfl

theorem direct_fields (loc : Source.DataLoc) :
    directEnv.structFields loopName loc = some [("next",.struct loc loopName)] := rfl

theorem direct_well_formed (s : Source.Settings) :
    Source.WellFormed (Source.resolveUnit s directUnit) ∧
    Source.InProfileSyntax (Source.resolveUnit s directUnit) := by
  have hd : (Source.resolveUnit s directUnit).unit.decls = [directDecl] := rfl
  refine ⟨⟨rfl,?_,?_,?_,show 0 ≤ 1 from by decide,?_,?_,?_,?_,?_⟩,rfl⟩
  · rw [hd]
    intro d hm hk
    cases List.mem_singleton.mp hm
    rcases hk with hk | hk <;> cases hk
  · rw [hd]
    exact .cons (by intro d hm; nomatch hm) .nil
  · intro ws hw; nomatch hw
  · change ∀ d ∈ [directDecl], d.typesOK directEnv = true
    decide
  · change ∀ d ∈ [directDecl], d.placementOK directEnv = true
    decide
  · change ∀ d ∈ [directDecl], d.isConst = true → d.init?.isSome = true
    decide
  · intro d hm e he
    rw [hd] at hm
    have h := List.mem_singleton.mp hm
    cases h
    cases he
  · intro d hm hb
    rw [hd] at hm
    have h := List.mem_singleton.mp hm
    cases h
    cases hb

/-- Inversion is over the existing intrinsically indexed type relation. -/
theorem struct_type_inv {D : Source.Layout} {n : Nat} {names : Fin n → Source.DeclName}
    {loc : Source.DataLoc} {dn : Source.DeclName} {T : TypeGraph.Ty n}
    (h : GraphTypeRel D names (.struct loc dn) T) :
    ∃ j : Fin n, names j = dn ∧ T = .node j := by
  cases h with
  | node loc j => exact ⟨j,rfl,rfl⟩

theorem singleton_fields_inv {D : Source.Layout} {n : Nat} {names : Fin n → Source.DeclName}
    {s : String} {τ : Source.STy} {ts : List (Name × TypeGraph.Ty n)}
    (h : GraphFieldsRel D names [(s,τ)] ts) :
    ∃ f T, ts = [(f,T)] ∧ s = f ∧ GraphTypeRel D names τ T := by
  cases h with
  | cons hn ht rest =>
    cases rest
    exact ⟨_,_,rfl,hn,ht⟩

theorem direct_not_certifiable (loc : Source.DataLoc) {n : Nat} (G : TypeGraph.Schema n) :
    ¬ Nonempty (DeclarationGraph directEnv loc G) := by
  intro ⟨c⟩
  obtain ⟨i,hi⟩ := c.complete ⟨0,by decide⟩ rfl
  have hn := c.source_name i
  have hs := c.source_scope i
  rw [hi] at hn hs
  change "Loop" = (c.sourceName i).name at hn
  change none = (c.sourceName i).scope at hs
  have ni : c.sourceName i = loopName := by
    change Source.DeclName.mk (c.sourceName i).scope (c.sourceName i).name =
      Source.DeclName.mk none "Loop"
    exact congr (congrArg Source.DeclName.mk hs.symm) hn.symm
  have hr := c.fields_resolve i
  rw [ni,direct_fields] at hr
  have rel := c.fields_relate i
  rw [← Option.some.inj hr] at rel
  obtain ⟨f,T,hfs,_,ht⟩ := singleton_fields_inv rel
  obtain ⟨j,hj,hT⟩ := struct_type_inv ht
  have ji : j = i := c.sourceName_injective (hj.trans ni.symm)
  have mem : (f,TypeGraph.Ty.node i) ∈ G.fields i := by
    rw [hfs,hT,ji]
    exact List.mem_cons_self
  exact G.no_inline_self mem .node

/-- Current S01 metadata plus syntax-profile membership is insufficient for
this graph certificate, for ANY graph size. This does not refute a stronger
future accepted-source/G15 judgment or propose a new exclusion. -/
theorem no_total_from_current_metadata (loc : Source.DataLoc) :
    ¬ (∀ (s : Source.Settings) (u : Source.Syn .unit),
      Source.WellFormed (Source.resolveUnit s u) →
      Source.InProfileSyntax (Source.resolveUnit s u) →
      ∃ (n : Nat) (G : TypeGraph.Schema n), Nonempty (DeclarationGraph u.env loc G)) := by
  intro all
  let s : Source.Settings := ⟨.legacy,[]⟩
  obtain ⟨n,G,h⟩ := all s directUnit (direct_well_formed s).1 (direct_well_formed s).2
  exact direct_not_certifiable loc G h

/-- A dynamic-array edge is a genuine guarded recursive declaration. -/
def guardedNode : Source.Syn (.part true) :=
  .struct "Loop" (.structMember (.array (.userType ⟨"Loop",[]⟩) .none) "next") .nil

def guardedUnit : Source.Syn .unit := .unit (.cons (.topPart guardedNode) .nil)
def guardedDecl : Source.Decl := ⟨.struct,"Loop",none,true,guardedNode⟩
def guardedEnv : Source.Env := guardedUnit.env

theorem guarded_fields (loc : Source.DataLoc) :
    guardedEnv.structFields loopName loc =
      some [("next",.array loc (.struct loc loopName) none)] := rfl

theorem guarded_well_formed (s : Source.Settings) :
    Source.WellFormed (Source.resolveUnit s guardedUnit) ∧
    Source.InProfileSyntax (Source.resolveUnit s guardedUnit) := by
  have hd : (Source.resolveUnit s guardedUnit).unit.decls = [guardedDecl] := rfl
  refine ⟨⟨rfl,?_,?_,?_,show 0 ≤ 1 from by decide,?_,?_,?_,?_,?_⟩,rfl⟩
  · rw [hd]
    intro d hm hk
    cases List.mem_singleton.mp hm
    rcases hk with hk | hk <;> cases hk
  · rw [hd]
    exact .cons (by intro d hm; nomatch hm) .nil
  · intro ws hw; nomatch hw
  · change ∀ d ∈ [guardedDecl], d.typesOK guardedEnv = true
    decide
  · change ∀ d ∈ [guardedDecl], d.placementOK guardedEnv = true
    decide
  · change ∀ d ∈ [guardedDecl], d.isConst = true → d.init?.isSome = true
    decide
  · intro d hm e he
    rw [hd] at hm
    cases List.mem_singleton.mp hm
    cases he
  · intro d hm hb
    rw [hd] at hm
    cases List.mem_singleton.mp hm
    cases hb

def schema : TypeGraph.Schema 1 where
  origin := "v07-guarded-recursive-control"
  declId := fun _ => 0
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "Loop"
  fields := fun _ => [("next",.array (.node ⟨0,by decide⟩))]
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    cases h
    exact Nat.zero_lt_succ 0

def certificate (loc : Source.DataLoc) : DeclarationGraph guardedEnv loc schema where
  sourceName := fun _ => loopName
  sourceName_injective := by intro i j _; apply Fin.ext; omega
  sourceIndex := fun _ => ⟨0,by decide⟩
  identity := fun _ => rfl
  source_kind := fun _ => rfl
  source_scope := fun _ => rfl
  source_name := fun _ => rfl
  source_resolves := fun _ => rfl
  target_name := fun _ => rfl
  sourceFields := fun _ => [("next",.array loc (.struct loc loopName) none)]
  fields_resolve := fun _ => rfl
  fields_relate := fun _ => .cons rfl (.array loc (.node loc ⟨0,by decide⟩)) .nil
  complete := by
    intro j _
    have hj : j = ⟨0,by decide⟩ := by
      apply Fin.ext
      change j.val = 0
      have h : j.val < 1 := j.isLt
      omega
    exact ⟨⟨0,by decide⟩,hj.symm⟩

theorem guarded_inhabited (loc : Source.DataLoc) :
    Nonempty (DeclarationGraph guardedEnv loc schema) := ⟨certificate loc⟩

theorem actual_recursive_edge :
    schema.fields ⟨0,by decide⟩ = [("next",.array (.node ⟨0,by decide⟩))] := rfl

theorem guarded_rank_zero :
    (TypeGraph.Ty.array (.node ⟨0,by decide⟩)).inlineRank schema.rank = 0 := rfl

theorem same_edge_inline_not_guarded :
    ¬ ((TypeGraph.Ty.node ⟨0,by decide⟩).inlineRank schema.rank < schema.rank ⟨0,by decide⟩) := by decide

/-- Even the currently published G13 checker adds only constant/operator
conditions here; it does not supply inline struct acyclicity. -/
theorem direct_strict_metadata_accepts (s : Source.Settings) :
    Frontend.Static.strictMetadataChecker.check (Source.resolveUnit s directUnit) () () = true := rfl

theorem guarded_strict_metadata_accepts (s : Source.Settings) :
    Frontend.Static.strictMetadataChecker.check (Source.resolveUnit s guardedUnit) () () = true := rfl

theorem no_total_from_strict_metadata (loc : Source.DataLoc) :
    ¬ (∀ (s : Source.Settings) (u : Source.Syn .unit),
      Frontend.Static.strictMetadataChecker.check (Source.resolveUnit s u) () () = true →
      ∃ (n : Nat) (G : TypeGraph.Schema n), Nonempty (DeclarationGraph u.env loc G)) := by
  intro all
  let s : Source.Settings := ⟨.legacy,[]⟩
  obtain ⟨n,G,h⟩ := all s directUnit (direct_strict_metadata_accepts s)
  exact direct_not_certifiable loc G h

end Solidity.Lowering.V07.GraphAdmissionBoundary
