import Solidity.Lowering.V07.RecursiveGraphControls
import Solidity.Lowering.V07.LocationGraphInterface
/-! H15 location witnesses and actual Source declaration-admission gap.
This does not provide
an Admission inhabitant or complete Source/solc location adequacy. -/
namespace Solidity.Lowering.V07.LocationGraphLaws
open Solidity Solidity.Lowering.V07
open LocationGraphInterface
abbrev E := RecursiveGraphControls.mappingEnv
abbrev loop := GraphAdmissionBoundary.loopName
abbrev C : Source.Ctx := {env := E,scope := none,locals := []}

theorem mapping_iff (E : Source.Env) (κ τ : Source.STy) (loc : Source.DataLoc) :
    AdmissibleLocation E (.mapping κ τ) loc ↔ loc = .storage := by
  simp only [AdmissibleLocation,Source.Env.hasMapping,Source.STy.mapsWith,Bool.true_eq_false,or_false]

theorem direct_mapping_refused (E : Source.Env) (scope : Option String) (loc : Source.DataLoc)
    (h : loc ≠ .storage) (key : Source.MapKey) (keyName valueName : Option String)
    (value : Source.Syn .typeName) :
    (Source.Syn.mapping key keyName value valueName).tys E scope loc = none := by
  simp only [Source.Syn.tys,if_neg h]

theorem struct_memory_bad : ¬ StructAdmissible E loop .memory := by decide

theorem user_type_memory :
    (Source.Syn.userType ⟨"Loop",[]⟩).ty E none .memory = some (.struct .memory loop) := by decide

theorem local_memory_flag : Source.locOK (.struct .memory loop) (some .memory) false = true := by decide

def typed_local (k : Source.SCtx) :
    Source.StmtD C (k := k) []
      (.simpleStmt (.declVar (.varDecl (.userType ⟨"Loop",[]⟩) (some .memory) "x") .none))
      [("x",.struct .memory loop)] := by
  exact .declVar rfl rfl

theorem refusal_missing : ¬ SourceRefusesNonAdmissible E := by
  intro refuses
  have admitted := refuses C rfl .body [] [("x",.struct .memory loop)]
    (.userType ⟨"Loop",[]⟩) (.struct .memory loop) .memory "x" .none rfl (typed_local .body)
  exact struct_memory_bad admitted

-- Mixed-environment certificate attempts: automate before hand steps.
def plain : Source.Decl := GraphIdentityControls.declaration "Plain"
def mixed : Source.Env := ⟨[RecursiveGraphControls.mapDecl,plain]⟩

def memorySchema : TypeGraph.Schema 1 where
  origin := "h15-mixed-memory"
  declId := fun _ => 1
  declId_injective := by decide
  name := fun _ => "Plain"
  fields := fun _ => [("value",.prim .uint)]
  rank := fun _ => 1
  nonempty := by decide
  distinct := by decide
  guarded := by decide

def memoryCertificate : LocationDeclarationGraph mixed .memory memorySchema where
  sourceName := fun _ => ⟨none,"Plain"⟩
  sourceName_injective := by
    intro i j _
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  sourceIndex := fun _ => ⟨1,by decide⟩
  identity := by decide
  source_kind := by decide
  source_scope := by decide
  source_name := by decide
  source_resolves := fun _ => rfl
  source_admissible := by decide
  target_name := by decide
  sourceFields := fun _ => [("value",.int .u8)]
  fields_resolve := by decide
  fields_relate := fun _ => .cons rfl (.int .u8) .nil
  complete := by decide

def storageResult :=
  (RecursiveGraph.produce "mapping-guard" E .storage).get RecursiveGraphControls.mapping_storage_success

def storageCertificate := LocationGraphInterface.ofStorage storageResult.2

theorem memory_plain_physical_id : (memoryCertificate.sourceIndex ⟨0,by decide⟩).val = 1 := by
  decide

theorem memory_excludes_storage_only : ∀ i : Fin 1, (memoryCertificate.sourceName i).name ≠ "Loop" := by
  decide

theorem mixed_location_policy : StructAdmissible mixed ⟨none,"Plain"⟩ .memory ∧
    ¬ StructAdmissible mixed loop .memory ∧ StructAdmissible mixed loop .storage := by
  decide

theorem storage_original_preserved : storageResult.1.declId ⟨0,by decide⟩ = 0 ∧
    (storageCertificate.sourceIndex ⟨0,by decide⟩).val = 0 := by
  decide

end Solidity.Lowering.V07.LocationGraphLaws
