import Solidity.Lowering.V07.LocationGraphInterface
import Solidity.Lowering.V07.LocationGraphLaws

/-!
# H15 Source refusal: exact characterization on the current Source typing

`LocationGraphInterface.SourceRefusesNonAdmissible E` asks that every local
declaration `T loc x [= e];` admitted by `Source.StmtD` names a location at
which solc admits `T` (mappings, and aggregates containing one, only in
`storage`). `LocationGraphLaws.refusal_missing` refutes it for one environment.

This module locates the gap exactly. `refuses_iff`: on the current Source
typing, refusal holds for `E` iff every struct a type path names (in any
scope) is mapping-free. The reverse direction is a structural induction on
type names: `Syn.tys` refuses a `mapping` outside `storage` at every depth,
so the only way a mapping reaches a non-storage local is through a named
struct, which `Source.locOK` (environment-free) does not inspect.

`envLocOK` is the environment-aware check a Source repair would use in
`StmtD.declVar`/`declInit` (`Solidity/Source/**` is VY5-owned, H16; the patch
is recorded in `docs/feature-work/roadmap-v07-lowering.md`, CP75;
`envLocOK_eq_patch` equates it with the patch formula). It admits only
H15-admissible explicit locations (`envLocOK_sound`), refuses every
non-admissible one (`envLocOK_refuses`) and equals `locOK` wherever the
location is admissible (`envLocOK_conservative`), so the repair removes
nothing the H15 policy `AdmissibleLocation` admits (agreement of that policy
with solc is a separate obligation). `decl_inversion` is the current-Source
fact the repaired proof would strengthen: a local declaration's derivation
carries `locOK τ (some loc) b` for some initialization flag `b`.

Refusal is quantified per context (`∀ C, C.env = E`, every scope), as in the
interface, not per program. After the repair, the forward witnesses here
(`not_refuses_of_mapping_struct`, the forward half of `refuses_iff`, and
`LocationGraphLaws.refusal_missing`) no longer hold and are to be retired.

Local declarations only: parameters, returns and state variables are
separate obligations, as in the interface.
-/
namespace Solidity.Lowering.V07.SourceRefusal
open Solidity Solidity.Lowering.V07 LocationGraphInterface

/-- Every struct a type path names, in any scope, contains no mapping at the
H15 policy's depth. -/
def NameableStructsMappingFree (E : Source.Env) : Prop :=
  ∀ (scope : Option String) (p : Source.IdPath) (d : Source.Decl),
    E.lookupPath scope p = [d] → d.kind = .struct →
      E.hasMapping (E.structCount + 1) (.struct .storage ⟨d.scope, d.name⟩) = false

/-- Elementary types contain no mapping. -/
theorem elem_maps_free (g : Source.DeclName → Bool) (loc : Source.DataLoc) (e : Source.Elem) :
    (e.ty loc).mapsWith g = false := by
  cases e with
  | fixed s d => cases d <;> rfl
  | _ => rfl

/-- A type name elaborated outside `storage` reaches a mapping only through a
named struct: if `g` is false at every struct a path names, the elaborated
type is `g`-mapping-free. -/
theorem tys_maps_free (E : Source.Env) (scope : Option String) (g : Source.DeclName → Bool)
    (hg : ∀ (p : Source.IdPath) (d : Source.Decl), E.lookupPath scope p = [d] →
      d.kind = .struct → g ⟨d.scope, d.name⟩ = false)
    (loc : Source.DataLoc) (hloc : loc ≠ .storage) :
    ∀ (t : Source.Syn .typeName) (τs : List Source.STy), t.tys E scope loc = some τs →
      ∀ τ ∈ τs, τ.mapsWith g = false
  | .elem e, τs, h, τ, hτ => by
    simp only [Source.Syn.tys, Option.some.injEq] at h
    subst h
    simp only [List.mem_singleton] at hτ
    subst hτ
    exact elem_maps_free g loc e
  | .fnType ps vis mu rs, τs, h, τ, hτ => by
    simp only [Source.Syn.tys] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [List.mem_singleton] at hτ
      subst hτ
      rfl
    · cases h
  | .mapping k kn v vn, τs, h, τ, hτ => by
    simp only [Source.Syn.tys, if_neg hloc] at h
    cases h
  | .userType p, τs, h, τ, hτ => by
    simp only [Source.Syn.tys, Source.Env.userTy] at h
    split at h
    · rename_i d hd
      split at h <;> simp only [Option.map_some, Option.map_none, Option.some.injEq,
        reduceCtorEq] at h <;> subst h <;> simp only [List.mem_singleton] at hτ <;> subst hτ
      · rename_i hk
        exact hg p d hd hk
      all_goals rfl
    · cases h
  | .array t len, τs, h, τ, hτ => by
    simp only [Source.Syn.tys] at h
    split at h
    · rename_i τ' n ht _
      simp only [Option.some.injEq] at h
      subst h
      simp only [List.mem_singleton] at hτ
      subst hτ
      exact tys_maps_free E scope g hg loc hloc t [τ'] ht τ' (List.mem_singleton.mpr rfl)
    · cases h

/-- Reverse direction: mapping-free nameable structs give actual refusal.
The `StmtD` derivation is not used: refusal is decided by `Syn.ty` alone;
`locOK` matters only for the forward witness. -/
theorem refuses_of_mapping_free (E : Source.Env) (h : NameableStructsMappingFree E) :
    SourceRefusesNonAdmissible E := by
  intro C hC k L L' t τ loc x init ht _
  subst hC
  by_cases hloc : loc = .storage
  · exact Or.inl hloc
  · refine Or.inr ?_
    simp only [Source.Syn.ty] at ht
    split at ht
    · rename_i τ' hτs
      simp only [Option.some.injEq] at ht
      subst ht
      exact tys_maps_free C.env C.scope _ (fun p d hd hk => h C.scope p d hd hk) loc hloc t [τ']
        hτs τ' (List.mem_singleton.mpr rfl)
    · cases ht

/-- Forward direction: a nameable mapping-containing struct is admitted as a
`memory` local by the actual `StmtD.declVar` rule. -/
theorem not_refuses_of_mapping_struct (E : Source.Env) (scope : Option String)
    (p : Source.IdPath) (d : Source.Decl) (hd : E.lookupPath scope p = [d])
    (hk : d.kind = .struct)
    (hm : E.hasMapping (E.structCount + 1) (.struct .storage ⟨d.scope, d.name⟩) = true) :
    ¬ SourceRefusesNonAdmissible E := by
  intro refuses
  have hty : (Source.Syn.userType p).ty E scope .memory = some (.struct .memory ⟨d.scope, d.name⟩) := by
    simp only [Source.Syn.ty, Source.Syn.tys, Source.Env.userTy, hd, hk, Option.map_some]
  have derivation : Source.StmtD ({env := E, scope := scope, locals := []} : Source.Ctx)
      (k := ⟨false, false⟩) []
      (.simpleStmt (.declVar (.varDecl (.userType p) (some .memory) "x") .none))
      [("x", .struct .memory ⟨d.scope, d.name⟩)] :=
    .declVar hty rfl
  have adm := refuses {env := E, scope := scope, locals := []} rfl ⟨false, false⟩ [] _
    (.userType p) _ .memory "x" .none hty derivation
  rcases adm with hs | hf
  · cases hs
  · have : E.hasMapping (E.structCount + 1) (.struct .memory ⟨d.scope, d.name⟩) = true := hm
    rw [this] at hf
    cases hf

/-- **Exact characterization** on the current Source typing. -/
theorem refuses_iff (E : Source.Env) :
    SourceRefusesNonAdmissible E ↔ NameableStructsMappingFree E := by
  constructor
  · intro refuses scope p d hd hk
    cases hm : E.hasMapping (E.structCount + 1) (.struct .storage ⟨d.scope, d.name⟩)
    · rfl
    · exact absurd refuses (not_refuses_of_mapping_struct E scope p d hd hk hm)
  · exact refuses_of_mapping_free E

/-- Every declaration a path resolves to is one of the environment's. -/
theorem lookupPath_mem (E : Source.Env) (scope : Option String) (p : Source.IdPath)
    (d : Source.Decl) (h : d ∈ E.lookupPath scope p) : d ∈ E.decls := by
  simp only [Source.Env.lookupPath] at h
  split at h
  · simp only [Source.Env.lookup] at h
    split at h
    · simp only [Source.Env.visible, Source.Env.declared, List.mem_filter] at h
      exact h.1.1
    · simp only [Source.Env.declared, List.mem_filter] at h
      exact h.1
  · simp only [Source.Env.declared, List.mem_filter] at h
    exact h.1
  · cases h

/-- Decidable sufficient condition over the declaration list. -/
def DeclsMappingFree (E : Source.Env) : Prop :=
  ∀ d ∈ E.decls, d.kind = .struct →
    E.hasMapping (E.structCount + 1) (.struct .storage ⟨d.scope, d.name⟩) = false

instance (E : Source.Env) : Decidable (DeclsMappingFree E) :=
  inferInstanceAs (Decidable (∀ d ∈ E.decls, d.kind = .struct →
    E.hasMapping (E.structCount + 1) (.struct .storage ⟨d.scope, d.name⟩) = false))

theorem nameable_of_decls (E : Source.Env) (h : DeclsMappingFree E) :
    NameableStructsMappingFree E := fun scope p d hd hk =>
  h d (lookupPath_mem E scope p d (by rw [hd]; exact List.mem_singleton.mpr rfl)) hk

theorem refuses_of_decls (E : Source.Env) (h : DeclsMappingFree E) :
    SourceRefusesNonAdmissible E :=
  refuses_of_mapping_free E (nameable_of_decls E h)

/-! ## The environment-aware repair -/

/-- `Source.locOK` plus the H15 location policy for an explicit location. -/
def envLocOK (E : Source.Env) (τ : Source.STy) (l : Option Source.DataLoc) (init : Bool) : Bool :=
  Source.locOK τ l init &&
    match l with
    | some loc => decide (AdmissibleLocation E τ loc)
    | none => true

/-- `envLocOK` is exactly the Boolean formula of the recorded Source patch
(`Ctx.locOK` in the feature document), so the patch's premise is this check. -/
theorem envLocOK_eq_patch (E : Source.Env) (τ : Source.STy) (l : Option Source.DataLoc) (init : Bool) :
    envLocOK E τ l init = (Source.locOK τ l init &&
      (l.isNone || l == some .storage || !E.hasMapping (E.structCount + 1) τ)) := by
  cases l with
  | none => simp only [envLocOK, Option.isNone_none, Bool.true_or]
  | some loc =>
    cases loc <;> cases h : E.hasMapping (E.structCount + 1) τ <;>
      simp only [envLocOK, AdmissibleLocation, h, Option.isNone_some, Bool.false_or, Bool.not_true,
        Bool.not_false, Bool.or_false, Bool.or_true, decide_eq_true_eq, decide_eq_false_iff_not,
        reduceCtorEq, false_or, true_or, or_false, or_true, decide_true, decide_false,
        beq_self_eq_true, Option.some.injEq] <;> rfl

/-- The repaired check admits only solc-admissible locations. -/
theorem envLocOK_sound (E : Source.Env) (τ : Source.STy) (loc : Source.DataLoc) (init : Bool)
    (h : envLocOK E τ (some loc) init = true) : AdmissibleLocation E τ loc := by
  simp only [envLocOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- The repair removes nothing solc admits: on admissible locations (and with
no location) it is `locOK`. -/
theorem envLocOK_conservative (E : Source.Env) (τ : Source.STy) (l : Option Source.DataLoc)
    (init : Bool) (h : ∀ loc, l = some loc → AdmissibleLocation E τ loc) :
    envLocOK E τ l init = Source.locOK τ l init := by
  cases l with
  | none => simp only [envLocOK, Bool.and_true]
  | some loc =>
    simp only [envLocOK, decide_eq_true (h loc rfl), Bool.and_true]

/-- The repair refuses exactly the non-admissible explicit locations. -/
theorem envLocOK_refuses (E : Source.Env) (τ : Source.STy) (loc : Source.DataLoc) (init : Bool)
    (h : ¬ AdmissibleLocation E τ loc) : envLocOK E τ (some loc) init = false := by
  simp only [envLocOK, decide_eq_false h, Bool.and_false]

/-- Current-Source inversion: a local declaration at an explicit location is
admitted only through `declVar`/`declInit`, whose premise is `locOK` of the
declared type. Replacing that premise by `envLocOK C.env` (the recorded
repair) makes this inversion end in `envLocOK_sound`, i.e. refusal. -/
theorem decl_inversion {C : Source.Ctx} {k : Source.SCtx} {L L' : List (String × Source.STy)}
    {t : Source.Syn .typeName} {loc : Source.DataLoc} {x : String} {init : Source.Syn (.opt .expr)}
    {τ : Source.STy} (ht : t.ty C.env C.scope loc = some τ)
    (d : Source.StmtD C (k := k) L (.simpleStmt (.declVar (.varDecl t (some loc) x) init)) L') :
    ∃ b, Source.locOK τ (some loc) b = true := by
  cases d with
  | declVar ht' hl =>
    rw [Option.getD_some, ht] at ht'
    cases ht'
    exact ⟨false, hl⟩
  | declInit ht' hl _ _ =>
    rw [Option.getD_some, ht] at ht'
    cases ht'
    exact ⟨true, hl⟩

/-! ## Controls -/

/-- The existing mapping-struct environment: the characterization reproduces
`LocationGraphLaws.refusal_missing` from its nameable `Loop` struct. -/
theorem mapping_env_not_nameable_free :
    ¬ NameableStructsMappingFree LocationGraphLaws.E := by
  intro h
  exact LocationGraphLaws.refusal_missing ((refuses_iff _).mpr h)

/-- The repaired check refuses that very declaration (`Loop memory x;`). -/
theorem mapping_env_repair_refuses :
    envLocOK LocationGraphLaws.E (.struct .memory LocationGraphLaws.loop) (some .memory) false = false ∧
    Source.locOK (.struct .memory LocationGraphLaws.loop) (some .memory) false = true := by
  decide

/-- ... while keeping the storage pointer form of the same type. -/
theorem mapping_env_repair_keeps_storage :
    envLocOK LocationGraphLaws.E (.struct .storage LocationGraphLaws.loop) (some .storage) true = true := by
  decide

/-- A struct-only environment without mappings: refusal holds outright on the
current Source typing. -/
theorem plain_env_refuses :
    SourceRefusesNonAdmissible ⟨[GraphIdentityControls.declaration "Plain"]⟩ :=
  refuses_of_decls _ (by decide)

/-- info: 'Solidity.Lowering.V07.SourceRefusal.tys_maps_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tys_maps_free
/-- info: 'Solidity.Lowering.V07.SourceRefusal.refuses_of_mapping_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms refuses_of_mapping_free
/-- info: 'Solidity.Lowering.V07.SourceRefusal.not_refuses_of_mapping_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_refuses_of_mapping_struct
/-- info: 'Solidity.Lowering.V07.SourceRefusal.refuses_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms refuses_iff
/-- info: 'Solidity.Lowering.V07.SourceRefusal.refuses_of_decls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms refuses_of_decls
/-- info: 'Solidity.Lowering.V07.SourceRefusal.envLocOK_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms envLocOK_sound
/-- info: 'Solidity.Lowering.V07.SourceRefusal.envLocOK_eq_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms envLocOK_eq_patch
/-- info: 'Solidity.Lowering.V07.SourceRefusal.envLocOK_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms envLocOK_conservative
/-- info: 'Solidity.Lowering.V07.SourceRefusal.envLocOK_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms envLocOK_refuses
/-- info: 'Solidity.Lowering.V07.SourceRefusal.decl_inversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decl_inversion
/-- info: 'Solidity.Lowering.V07.SourceRefusal.mapping_env_not_nameable_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapping_env_not_nameable_free
/-- info: 'Solidity.Lowering.V07.SourceRefusal.mapping_env_repair_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapping_env_repair_refuses
/-- info: 'Solidity.Lowering.V07.SourceRefusal.plain_env_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms plain_env_refuses

end Solidity.Lowering.V07.SourceRefusal
