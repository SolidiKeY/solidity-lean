import Solidity.Yul.Views.RootDeclarationChecked

namespace Solidity.Yul.Views

theorem CheckedRootDeclarations.encode_writeback {E ds d scope tr a origin} (r : @CheckedRootDeclarations E ds d scope tr a origin)
    (s : Source.Storage E.layout (E.lay a)) (m out : SlotView)
    (encoded : finiteEncode r.registrations s m = some out) : finiteWriteback r.registrations out s = some s :=
  finiteWriteback_encode _ _ _ _ r.separated encoded

theorem CheckedRootDeclarations.unchanged {E ds d scope tr a origin} (r : @CheckedRootDeclarations E ds d scope tr a origin)
    (s : Source.Storage E.layout (E.lay a)) (m : SlotView) (view : finiteView r.registrations s m) :
    finiteWriteback r.registrations m s = some s := finiteWriteback_unchanged _ _ _ view

def CheckedRootDeclarations.storeWriteback {E ds d scope tr a origin} (r : @CheckedRootDeclarations E ds d scope tr a origin)
    (m : SlotView) (s : Source.Storage E.layout (E.lay a)) := packedStoreWriteback r.registrations m s

theorem CheckedRootDeclarations.store_reencode {E ds d scope tr a origin} (r : @CheckedRootDeclarations E ds d scope tr a origin)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) : finiteEncode r.registrations out residual = some m :=
  packedStoreWriteback_reencode _ _ _ _ _ r.separated step

theorem CheckedRootDeclarations.store_view {E ds d scope tr a origin} (r : @CheckedRootDeclarations E ds d scope tr a origin)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) : finiteView r.registrations out m := by
  obtain ⟨written,decoded,same⟩ := Option.map_eq_some_iff.mp step
  cases same
  exact finiteWriteback_result_view _ _ _ _ r.separated decoded

theorem CheckedRootDeclarations.store_unchanged {E ds d scope tr a origin} (r : @CheckedRootDeclarations E ds d scope tr a origin)
    (m : SlotView) (s : Source.Storage E.layout (E.lay a)) (view : finiteView r.registrations s m) :
    r.storeWriteback m s = some (s,packedMask r.registrations m) :=
  packedStoreWriteback_unchanged _ _ _ _ view rfl

theorem CheckedRootDeclarations.store_other {E ds d scope tr a origin} (r : @CheckedRootDeclarations E ds d scope tr a origin)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) (p : Source.SPath)
    (unselected : ∀ c ∈ r.registrations, p ≠ c.path) : out.cell p = s.cell p :=
  packedStoreWriteback_other _ _ _ _ _ step p unselected


end Solidity.Yul.Views
