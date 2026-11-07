import Solidity.Source.TypingV2
import Solidity.Lowering.V07.SourceRefusal

/-! H57/H125 mapping-bearing named-struct regression.
The frozen v1 memory-local witness and negative refusal theorem remain valid.
V2 refuses that exact witness, admits an initialized storage pointer, and
satisfies H24's local-declaration admission obligation in every environment.
This is not global frontend/compiler adequacy or a v1 retirement decision. -/
namespace H125.TypingV2Controls
open Solidity Solidity.Source
open Solidity.Lowering.V07

theorem promoted_formula (E : Env) (ty : STy) (loc : Option DataLoc) (initialized : Bool) :
    Source.envLocOK E ty loc initialized =
      SourceRefusal.envLocOK E ty loc initialized :=
  (SourceRefusal.envLocOK_eq_patch E ty loc initialized).symm

theorem h24_v2 (E : Env) (C : Source.Ctx) (same : C.env = E) (k : SCtx)
    (L L' : List (String × STy)) (t : Syn .typeName) (ty : STy)
    (loc : DataLoc) (name : String) (init : Syn (.opt .expr))
    (typed : t.ty C.env C.scope loc = some ty)
    (derivation : Source.V2.StmtD C (k := k) L
      (.simpleStmt (.declVar (.varDecl t (some loc) name) init)) L') :
    LocationGraphInterface.AdmissibleLocation E ty loc := by
  have admitted := Source.V2.declaration_admissible C k L L' t loc name init ty typed derivation
  rw [same] at admitted
  exact admitted

theorem v1_negative_preserved :
    ¬ LocationGraphInterface.SourceRefusesNonAdmissible LocationGraphLaws.E :=
  LocationGraphLaws.refusal_missing

theorem v2_memory_refused :
    ¬ Nonempty (Source.V2.StmtD LocationGraphLaws.C (k := .body) []
      (.simpleStmt (.declVar (.varDecl (.userType ⟨"Loop", []⟩) (some .memory) "x") .none))
      [("x", .struct .memory LocationGraphLaws.loop)]) := by
  intro ⟨derivation⟩
  have admitted := h24_v2 LocationGraphLaws.E LocationGraphLaws.C rfl .body [] _
    (.userType ⟨"Loop", []⟩) (.struct .memory LocationGraphLaws.loop) .memory "x" .none
    LocationGraphLaws.user_type_memory derivation
  exact LocationGraphLaws.struct_memory_bad admitted

def storageCtx : Source.Ctx :=
  { env := LocationGraphLaws.E, scope := none,
    locals := [("original", .struct .storage LocationGraphLaws.loop)] }

def v2_storage_admitted : Source.V2.StmtD storageCtx (k := .body) storageCtx.locals
    (.simpleStmt (.declVar (.varDecl (.userType ⟨"Loop", []⟩) (some .storage) "x")
      (.some (.ident "original"))))
    (("x", .struct .storage LocationGraphLaws.loop) :: storageCtx.locals) :=
  Source.V2.StmtD.declInit rfl rfl (.loc rfl rfl) rfl

theorem storage_to_v1 :
    Nonempty (Source.StmtD storageCtx (k := .body) storageCtx.locals
      (.simpleStmt (.declVar (.varDecl (.userType ⟨"Loop", []⟩) (some .storage) "x")
        (.some (.ident "original"))))
      (("x", .struct .storage LocationGraphLaws.loop) :: storageCtx.locals)) :=
  ⟨v2_storage_admitted.toV1⟩

/-- info: 'Solidity.Source.envLocOK_implies_locOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.envLocOK_implies_locOK
/-- info: 'Solidity.Source.envLocOK_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.envLocOK_sound
/-- info: 'Solidity.Source.V2.checkStmt_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.V2.checkStmt_valid
/-- info: 'Solidity.Source.V2.checkItems_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.V2.checkItems_valid
/-- info: 'Solidity.Source.V2.StmtD.ofV1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.V2.StmtD.ofV1
/-- info: 'Solidity.Source.V2.declaration_location' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.V2.declaration_location
/-- info: 'Solidity.Source.V2.declaration_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.V2.declaration_admissible

/-- Mapping-free nameable structs inhabit the exact conservative bridge premise. -/
theorem mapping_free_compatible :
 ∀ (C : Solidity.Source.Ctx),
Solidity.Lowering.V07.SourceRefusal.NameableStructsMappingFree C.env →
Solidity.Source.V2.CompatibleAt C := by
  intro C free t ty loc initialized typed old
  unfold Solidity.Source.envLocOK
  rw [old]
  cases loc with
  | none => rfl
  | some loc =>
    by_cases storage : loc = .storage
    · subst loc; rfl
    · have mapfree : C.env.hasMapping (C.env.structCount + 1) ty = false := by
        simp only [Solidity.Source.Syn.ty] at typed
        split at typed
        · rename_i actual many
          simp only [Option.some.injEq] at typed
          subst typed
          exact Solidity.Lowering.V07.SourceRefusal.tys_maps_free C.env C.scope _
            (fun path decl found kind => free C.scope path decl found kind)
            loc storage t [actual] many actual (List.mem_singleton.mpr rfl)
        · cases typed
      simp only [Option.isNone_some, Bool.false_or, mapfree, Bool.not_false, Bool.or_true,
        Bool.true_and]


/-- A genuine joint witness for the conservative environment bridge. -/
def plainCtx : Source.Ctx := { env := ⟨[]⟩, scope := none, locals := [] }

def v1_bool_decl : Source.StmtD plainCtx (k := .body) []
    (.simpleStmt (.declVar (.varDecl (.elem .bool) none "flag") .none)) [("flag", .bool)] :=
  .declVar rfl rfl

def v2_bool_lifted : Source.V2.StmtD plainCtx (k := .body) []
    (.simpleStmt (.declVar (.varDecl (.elem .bool) none "flag") .none)) [("flag", .bool)] :=
  Source.V2.StmtD.ofV1 v1_bool_decl
    (mapping_free_compatible plainCtx (SourceRefusal.nameable_of_decls _ (by decide)))


end H125.TypingV2Controls
