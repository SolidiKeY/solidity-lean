import Solidity.Yul.Views.DeclarationBoundary
import Solidity.Yul.Views.DeclarationJournalControls

namespace Solidity.Yul.Views.Controls

def declBoundaryEnv : Source.Env := ⟨[
  ⟨.struct,"Inner",none,true,.struct "Inner" (.structMember (.elem .bool) "flag")
    (.cons (.structMember (.elem (.int false 16 (by decide))) "small")
    (.cons (.structMember (.elem (.fixedBytes 3 (by decide))) "data")
    (.cons (.structMember (.elem .address) "who") .nil)))⟩,
  ⟨.struct,"Composite",none,true,.struct "Composite"
    (.structMember (.array (.elem (.int false 24 (by decide))) (.some (.lit (.num (.dec 12 0 0))))) "values")
    (.cons (.structMember (.userType ⟨"Inner",[]⟩) "inner") .nil)⟩,
  ⟨.stateVar,"composite",none,true,.stateVar (.userType ⟨"Composite",[]⟩) none none none false "composite" .none⟩]⟩

def declBoundaryRoot : Source.DeclName := ⟨none,"composite"⟩
def declBoundary := (prepareDeclaredArrayStruct declBoundaryEnv declBoundaryRoot 4).get (by rfl)

theorem decl_array_struct_boundaries :
    declBoundary.first.endByte (4*32) = 166 ∧ declBoundary.nextByte = 192 ∧
    declBoundary.members.endByte declBoundary.nextByte = 218 ∧ declBoundary.endByte = 224 := by decide

theorem decl_array_struct_disjoint : ComponentsDisjoint declBoundary.first (4*32) declBoundary.members declBoundary.nextByte :=
  declBoundary.disjoint

theorem decl_array_padding_preserved (ds : Source.DataList declBoundaryEnv.layout (List.replicate declBoundary.count declBoundary.element))
    (m out : ByteView) (encoded : declBoundary.first.encode ds (4*32) m = some out) : out 158 = m 158 := by
  letI := declBoundary.first.ownsDecidable (4*32) 158
  exact declBoundary.first.encode_residual ds _ _ out encoded 158 (by decide)

theorem decl_unchanged_written_default :
    let s := (Source.Storage.empty (D := declPackingEnv.layout) (L := declPackingEnv.lay account)).write
      (declarationFieldPath declPackingRoot 0) (.bool false)
    finiteWriteback [((declPackingRegistry account).get ⟨0,by decide⟩)] (fun _ => packedZeroRaw) s = some s := by rfl

end Solidity.Yul.Views.Controls
