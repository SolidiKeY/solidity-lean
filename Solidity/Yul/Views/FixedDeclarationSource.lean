import Solidity.Yul.Views.FixedDeclarationChecked

namespace Solidity.Yul.Views

/-- Source.Env.lay is the actual uniform path typing for each account. The
transient companion shares this finite registry only as an explicit adapter,
not an inferred Solidity transient declaration layout. -/
def CheckedFixedDeclaration.registry {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base)
    (_ : Roadmap.Address) : List (ScalarPath E.layout (E.lay a)) := r.registrations

theorem CheckedFixedDeclaration.encode_writeback {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base)
    (s : Source.Storage E.layout (E.lay a)) (m out : SlotView)
    (encoded : finiteEncode r.registrations s m = some out) : finiteWriteback r.registrations out s = some s :=
  finiteWriteback_encode _ _ _ _ r.separated encoded

theorem CheckedFixedDeclaration.unchanged {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base)
    (s : Source.Storage E.layout (E.lay a)) (m : SlotView) (view : finiteView r.registrations s m) :
    finiteWriteback r.registrations m s = some s := finiteWriteback_unchanged _ _ _ view

def CheckedFixedDeclaration.storeWriteback {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base)
    (m : SlotView) (s : Source.Storage E.layout (E.lay a)) := packedStoreWriteback r.registrations m s

theorem CheckedFixedDeclaration.store_reencode {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) : finiteEncode r.registrations out residual = some m :=
  packedStoreWriteback_reencode _ _ _ _ _ r.separated step

theorem CheckedFixedDeclaration.store_view {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) : finiteView r.registrations out m := by
  obtain ⟨written,decoded,same⟩ := Option.map_eq_some_iff.mp step
  cases same
  exact finiteWriteback_result_view _ _ _ _ r.separated decoded

theorem CheckedFixedDeclaration.store_unchanged {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base)
    (m : SlotView) (s : Source.Storage E.layout (E.lay a)) (view : finiteView r.registrations s m) :
    r.storeWriteback m s = some (s,packedMask r.registrations m) :=
  packedStoreWriteback_unchanged _ _ _ _ view rfl

theorem CheckedFixedDeclaration.store_other {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) (p : Source.SPath)
    (unselected : ∀ c ∈ r.registrations, p ≠ c.path) : out.cell p = s.cell p :=
  packedStoreWriteback_other _ _ _ _ _ step p unselected

/-- Concrete existing frame preparation plus actual applyOp. None is not a
source/Yul verdict. Successful canonical source operations reconstruct the
ENTIRE raw word using the computed nested fields plus exact complement. -/
def CheckedFixedDeclaration.frameWrite? {E τ d root a base Γ} (r : @CheckedFixedDeclaration E τ d root a base)
    (F : Source.Fr) (transient : Bool) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (residual : ResidualJournal complementCarrierOwnership) :=
  packedFrameWrite? (ps := r.registry) (ts := r.registry) F transient slot raw s residual

theorem CheckedFixedDeclaration.frame_persistent_reencode {E τ d root a base Γ} (r : @CheckedFixedDeclaration E τ d root a base)
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (residual : ResidualJournal complementCarrierOwnership) (result)
    (step : r.frameWrite? F false slot raw s residual = some result) (static : F.static = false) :
    reencodePersistentSlot r.registry ⟨result.1.2.2.ex,result.2⟩ F.this slot = some raw :=
  packedFrameWrite_persistent_reencode _ _ _ _ _ _ step static r.separated

theorem CheckedFixedDeclaration.frame_transient_reencode {E τ d root a base Γ} (r : @CheckedFixedDeclaration E τ d root a base)
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (residual : ResidualJournal complementCarrierOwnership) (result)
    (step : r.frameWrite? F true slot raw s residual = some result) (static : F.static = false) :
    reencodeTransientSlot r.registry ⟨result.1.2.2.ex,result.2⟩ F.this slot = some raw :=
  packedFrameWrite_transient_reencode _ _ _ _ _ _ step static r.separated

theorem CheckedFixedDeclaration.frame_MemOK {E τ d root a base Γ} (r : @CheckedFixedDeclaration E τ d root a base)
    (H : Source.HeapTy) (F : Source.Fr) (transient : Bool) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (residual : ResidualJournal complementCarrierOwnership) (result)
    (step : r.frameWrite? F transient slot raw s residual = some result) (ok : Source.MemOK E H s) :
    Source.MemOK E H result.1.2 := packedFrameWrite_MemOK H _ _ _ _ _ _ _ step ok


end Solidity.Yul.Views
