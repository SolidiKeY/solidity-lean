import Solidity.Yul.Views.PathIntValues
import Solidity.Yul.Views.PathScalarValues
import Solidity.Yul.Views.MemberComputedStorage

namespace Solidity.Yul.Views

/-- Typed primitive families; this indexes certificates, never source state or
an alternate execution language. Integer and scalar source types stay distinct. -/
inductive PathPrimitiveKind where
  | integer (t : Source.IntTy)
  | scalar (k : DynamicScalarKind)
  deriving DecidableEq

def PathPrimitiveHeader (E : Source.Env) (p : Source.SPath) (k : PathPrimitiveKind) (cursor : Nat) : Prop :=
  match k with
  | .integer t => PathIntHeader E p t cursor
  | .scalar k => PathScalarHeader E p k cursor

def PathPrimitiveHeader.registration {E p k cursor} (h : PathPrimitiveHeader E p k cursor)
    (a : Roadmap.Address) : ScalarPath E.layout (E.lay a) :=
  match k,h with
  | .integer _,h => PathIntHeader.registration h a
  | .scalar _,h => PathScalarHeader.registration h a

def PathPrimitiveHeader.elements {E p k cursor} (h : PathPrimitiveHeader E p k cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (n : Roadmap.Word) : List (ScalarPath E.layout (E.lay a)) :=
  match k,h with
  | .integer _,h => PathIntHeader.elements h fixed a n
  | .scalar _,h => PathScalarHeader.elements h fixed a n

def StorageDeclaration.pathPrimitive? {E τ} (d : StorageDeclaration E τ) : Option PathPrimitiveKind :=
  StorageDeclaration.casesOn (motive := fun _ _ => Option PathPrimitiveKind) d
    (fun _ => none) (some (.integer .u256)) (fun t _ _ => some (.integer t))
    (fun t _ => some (.integer t)) (fun k => some (.scalar k))

theorem StorageDeclaration.pathPrimitive_sound {E τ} (d : StorageDeclaration E τ)
    (p a cursor cs stop k) (typed : E.pathTy p = some τ)
    (success : d.pack p a cursor = .ok (cs,stop)) (selected : d.pathPrimitive? = some k) :
    ∃ h : PathPrimitiveHeader E p k cursor, cs = [h.registration a] := by
  cases d with
  | fixed fixed => cases selected
  | uintArray =>
    cases selected
    obtain ⟨h,same,_⟩ := path_integer_header_of_packed typed success
    exact ⟨h,same⟩
  | packedUnsignedArray t unsigned packed =>
    cases selected
    obtain ⟨h,same,_⟩ := path_integer_header_of_packed typed success
    exact ⟨h,same⟩
  | signedArray t signed =>
    cases selected
    obtain ⟨h,same,_⟩ := path_integer_header_of_packed typed success
    exact ⟨h,same⟩
  | scalarArray kind =>
    cases selected
    obtain ⟨h,same,_⟩ := path_scalar_header_of_packed typed success
    exact ⟨h,same⟩

theorem PathPrimitiveHeader.proof_irrel {E p k cursor} (h g : PathPrimitiveHeader E p k cursor) : h = g := by
  cases k with
  | integer t => cases h; cases g; rfl
  | scalar k => cases h; cases g; rfl

theorem PathPrimitiveHeader.registration_path {E p k cursor} (h : PathPrimitiveHeader E p k cursor)
    (a : Roadmap.Address) : (h.registration a).path = p := by
  cases k <;> rfl

end Solidity.Yul.Views
