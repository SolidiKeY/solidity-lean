import Solidity.Yul.Views.FixedNominalMemory

/-! Fixed and declared nominal values compose with the existing pointer member
lookup. The actual Source.Val indices and pointer candidates are retained; the
support predicate is only this additive decoder's profile, not admission. -/
namespace Solidity.Yul.Views.FixedNominalMember
open Solidity.Yul.Views

def Supported (E : Source.Env) : Source.STy → Prop
  | .fixed _ => True
  | .udvt name => NominalMemory.declaredUDVT E name=true ∧
      FixedNominalMemory.ScalarSupported E.layout (E.layout.underlying name)
  | τ => ExtendedMemberType E.layout τ

def decode {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (w : Roadmap.Word) : Option (Source.Val E.layout τ) :=
  match τ with
  | .fixed f => FixedMemory.decode E.layout f w
  | .udvt name => FixedNominalMemory.decodeDeclared E name w
  | σ => decodeExtendedMemoryMember p es σ w

theorem sound {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τ : Source.STy) (w : Roadmap.Word)
    (v : Source.Val E.layout τ) (decoded : decode p es τ w=some v) :
    Source.Val.RefOK E h.ty v ∧ MemoryElement p v w := by
  first | solve | simp only [decode] at decoded ⊢
        | cases τ with
          | fixed f => exact ⟨Source.Val.refOK_of_loc rfl v,.scalar _ _ (FixedMemory.word E.layout f w v decoded)⟩
          | udvt name =>
            change FixedNominalMemory.decodeDeclared E name w=some v at decoded
            unfold FixedNominalMemory.decodeDeclared at decoded
            split at decoded
            · exact ⟨Source.Val.refOK_of_loc rfl v,.scalar _ _ (FixedNominalMemory.word E.layout name w v decoded)⟩
            · cases decoded
          | _ => exact decodeExtendedMemoryMember_sound p es _ w v decoded

theorem encode {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (τ : Source.STy)
    (supported : Supported E τ) (v : Source.Val E.layout τ) (w : Roadmap.Word)
    (encoded : MemoryElement p v w) : decode p es τ w=some v := by
  first | solve | simp only [decode]
        | cases τ with
          | fixed f =>
            have word : v.word=some w := by
              cases encoded with
              | scalar _ _ eq => exact eq
              | pointer loc _ _ _ _ => cases loc
            exact FixedMemory.decode_encode E.layout f v w word
          | udvt name =>
            have word : v.word=some w := by
              cases encoded with
              | scalar _ _ eq => exact eq
              | pointer loc _ _ _ _ => cases loc
            change FixedNominalMemory.decodeDeclared E name w=some v
            unfold FixedNominalMemory.decodeDeclared
            rw [supported.1,if_pos rfl,FixedNominalMemory.decode_encode E.layout name supported.2 v w word]
          | _ => exact decodeExtendedMemoryMember_encode p es coverage _ supported v w encoded

end Solidity.Yul.Views.FixedNominalMember
