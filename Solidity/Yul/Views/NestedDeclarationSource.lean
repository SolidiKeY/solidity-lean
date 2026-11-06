import Solidity.Yul.Views.NestedDeclaration
import Solidity.Yul.Views.PackedResidualFrame

namespace Solidity.Yul.Views

/-- Source.Env.lay is the actual uniform path typing for each account. The
transient companion shares this finite registry only as an explicit adapter,
not an inferred Solidity transient declaration layout. -/
def NestedDeclaration.registry {E root base d a} (r : @NestedDeclaration E root base d a)
    (_ : Roadmap.Address) : List (ScalarPath E.layout (E.lay a)) := r.registrations

theorem NestedDeclaration.padding_unowned {E root base d a} (r : @NestedDeclaration E root base d a)
    (q : Roadmap.Word) (i : Fin 32)
    (padding : r.arrayEnd ≤ q.val*32+i.val ∧ q.val*32+i.val < roundSlot r.arrayEnd) :
    packedOwnsByte r.registrations q i = false := by
  cases owned : packedOwnsByte r.registrations q i with
  | false => rfl
  | true =>
    obtain ⟨c,member,same,inside⟩ := (packedOwnsByte_iff r.registrations q i).mp owned
    have spans := r.owned_spans c member
    unfold declarationEnd declarationStart at spans
    rw [same] at spans
    omega

theorem NestedDeclaration.padding_encode {E root base d a} (r : @NestedDeclaration E root base d a)
    (s : Source.Storage E.layout (E.lay a)) (m out : SlotView)
    (encoded : finiteEncode r.registrations s m = some out) (q : Roadmap.Word) (i : Fin 32)
    (padding : r.arrayEnd ≤ q.val*32+i.val ∧ q.val*32+i.val < roundSlot r.arrayEnd) :
    slotBytes out (q.val*32+i.val) = slotBytes m (q.val*32+i.val) :=
  finiteEncode_residual _ _ _ _ encoded _ (by have := q.isLt; have := i.isLt; omega)
    (unowned_coordinates _ _ _ (r.padding_unowned q i padding))

theorem NestedDeclaration.encode_writeback {E root base d a} (r : @NestedDeclaration E root base d a)
    (s : Source.Storage E.layout (E.lay a)) (m out : SlotView)
    (encoded : finiteEncode r.registrations s m = some out) : finiteWriteback r.registrations out s = some s :=
  finiteWriteback_encode _ _ _ _ r.separated encoded

theorem NestedDeclaration.unchanged {E root base d a} (r : @NestedDeclaration E root base d a)
    (s : Source.Storage E.layout (E.lay a)) (m : SlotView) (view : finiteView r.registrations s m) :
    finiteWriteback r.registrations m s = some s := finiteWriteback_unchanged _ _ _ view

def NestedDeclaration.storeWriteback {E root base d a} (r : @NestedDeclaration E root base d a)
    (m : SlotView) (s : Source.Storage E.layout (E.lay a)) := packedStoreWriteback r.registrations m s

theorem NestedDeclaration.store_reencode {E root base d a} (r : @NestedDeclaration E root base d a)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) : finiteEncode r.registrations out residual = some m :=
  packedStoreWriteback_reencode _ _ _ _ _ r.separated step

theorem NestedDeclaration.store_view {E root base d a} (r : @NestedDeclaration E root base d a)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) : finiteView r.registrations out m := by
  obtain ⟨written,decoded,same⟩ := Option.map_eq_some_iff.mp step
  cases same
  exact finiteWriteback_result_view _ _ _ _ r.separated decoded

theorem NestedDeclaration.store_unchanged {E root base d a} (r : @NestedDeclaration E root base d a)
    (m : SlotView) (s : Source.Storage E.layout (E.lay a)) (view : finiteView r.registrations s m) :
    r.storeWriteback m s = some (s,packedMask r.registrations m) :=
  packedStoreWriteback_unchanged _ _ _ _ view rfl

theorem NestedDeclaration.store_other {E root base d a} (r : @NestedDeclaration E root base d a)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) (p : Source.SPath)
    (unselected : ∀ c ∈ r.registrations, p ≠ c.path) : out.cell p = s.cell p :=
  packedStoreWriteback_other _ _ _ _ _ step p unselected

/-- Concrete existing frame preparation plus actual applyOp. None is not a
source/Yul verdict. Successful canonical source operations reconstruct the
ENTIRE raw word using the computed nested fields plus exact complement. -/
def NestedDeclaration.frameWrite? {E root base d a Γ} (r : @NestedDeclaration E root base d a)
    (F : Source.Fr) (transient : Bool) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (residual : ResidualJournal complementCarrierOwnership) :=
  packedFrameWrite? (ps := r.registry) (ts := r.registry) F transient slot raw s residual

theorem NestedDeclaration.frame_persistent_reencode {E root base d a Γ} (r : @NestedDeclaration E root base d a)
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (residual : ResidualJournal complementCarrierOwnership) (result)
    (step : r.frameWrite? F false slot raw s residual = some result) (static : F.static = false) :
    reencodePersistentSlot r.registry ⟨result.1.2.2.ex,result.2⟩ F.this slot = some raw :=
  packedFrameWrite_persistent_reencode _ _ _ _ _ _ step static r.separated

theorem NestedDeclaration.frame_transient_reencode {E root base d a Γ} (r : @NestedDeclaration E root base d a)
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (residual : ResidualJournal complementCarrierOwnership) (result)
    (step : r.frameWrite? F true slot raw s residual = some result) (static : F.static = false) :
    reencodeTransientSlot r.registry ⟨result.1.2.2.ex,result.2⟩ F.this slot = some raw :=
  packedFrameWrite_transient_reencode _ _ _ _ _ _ step static r.separated

theorem NestedDeclaration.frame_MemOK {E root base d a Γ} (r : @NestedDeclaration E root base d a)
    (H : Source.HeapTy) (F : Source.Fr) (transient : Bool) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (residual : ResidualJournal complementCarrierOwnership) (result)
    (step : r.frameWrite? F transient slot raw s residual = some result) (ok : Source.MemOK E H s) :
    Source.MemOK E H result.1.2 := packedFrameWrite_MemOK H _ _ _ _ _ _ _ step ok

end Solidity.Yul.Views
