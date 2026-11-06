import Solidity.Yul.Views.InheritedDeclarations

namespace Solidity.Yul.Views

theorem inheritedRootNames_lookup {E order tr} (unique : ∀ scope ∈ order, (allScopeRootNames E (some scope)).Nodup)
    (root : Source.DeclName) (member : root ∈ inheritedRootNames E order tr) :
    ∃ scope, scope ∈ order ∧ root.scope = some scope ∧
      ∃ d, d ∈ E.decls ∧ E.declOf .stateVar root = some d ∧
        ordinaryRootName? (some scope) tr d = some root ∧ plainStateVariable d = true ∧ d.isTransient = tr := by
  obtain ⟨scope,inOrder,selected⟩ := List.mem_flatMap.mp member
  obtain ⟨d,inEnv,found,ordinary,plain,bank⟩ := ordinaryRootNames_lookup (unique scope inOrder) root selected
  exact ⟨scope,inOrder,(ordinaryRootName_facts ordinary).1,d,inEnv,found,ordinary,plain,bank⟩

namespace CheckedInheritedDeclarations

theorem separated {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin) :
    finiteSeparated r.registrations := (d.pack_spec r.distinct _ _ _ _ r.packed).2.2.1

theorem coverage {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin) :
    r.registrations.map ScalarPath.path = d.paths := d.pack_paths _ _ _ _ r.packed

theorem unique {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin) :
    (r.registrations.map ScalarPath.path).Nodup := List.pairwise_map.mpr (r.separated.imp (fun h => h.1))

theorem extent {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin) :
    r.endByte = d.endByte (origin.val*32) := d.pack_end _ _ _ _ r.packed

theorem nonwrapping {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin) :
    origin.val*32 ≤ r.endByte ∧ r.endByte ≤ (2^256)*32 := by
  have spec := d.pack_spec r.distinct _ _ _ _ r.packed
  exact ⟨spec.1,spec.2.1 (Nat.mul_le_mul_right 32 (Nat.le_of_lt origin.isLt))⟩

theorem paths_typed {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin)
    (c : ScalarPath E.layout (E.lay a)) (member : c ∈ r.registrations) : (E.pathTy c.path).isSome :=
  d.pack_typed _ _ _ _ r.packed c member

/-- Completeness at the actual source-qualified root identity, with no visibility
filter; the same private base member remains eligible in derived storage. -/
theorem root_inventory {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin)
    (root : Source.DeclName) : root ∈ ds.map Prod.fst ↔
      ∃ scope ∈ r.hierarchy.order, root ∈ ordinaryRootNames E (some scope) tr := by
  rw [r.ordered]
  exact List.mem_flatMap

theorem bank_agreement {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin)
    (c : ScalarPath E.layout (E.lay a)) (member : c ∈ r.registrations) : E.transientRoot c.path = tr := by
  have rootMember := ((d.pack_spec r.distinct _ _ _ _ r.packed).2.2.2 c member).2.2
  rw [r.ordered] at rootMember
  obtain ⟨scope,inOrder,selected⟩ := List.mem_flatMap.mp rootMember
  exact ordinaryRootNames_bank (r.sourceDistinct scope inOrder) c.path.root selected

theorem unchanged {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin)
    (s : Source.Storage E.layout (E.lay a)) (m : SlotView) (view : finiteView r.registrations s m) :
    finiteWriteback r.registrations m s = some s := finiteWriteback_unchanged _ _ _ view

def storeWriteback {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin)
    (m : SlotView) (s : Source.Storage E.layout (E.lay a)) := packedStoreWriteback r.registrations m s

theorem store_reencode {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) : finiteEncode r.registrations out residual = some m :=
  packedStoreWriteback_reencode _ _ _ _ _ r.separated step

theorem store_unchanged {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin)
    (m : SlotView) (s : Source.Storage E.layout (E.lay a)) (view : finiteView r.registrations s m) :
    r.storeWriteback m s = some (s,packedMask r.registrations m) :=
  packedStoreWriteback_unchanged _ _ _ _ view rfl

theorem store_other {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) (p : Source.SPath)
    (unselected : ∀ c ∈ r.registrations, p ≠ c.path) : out.cell p = s.cell p :=
  packedStoreWriteback_other _ _ _ _ _ step p unselected

theorem store_view {E ds d active tr a origin} (r : @CheckedInheritedDeclarations E ds d active tr a origin)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.storeWriteback m s = some (out,residual)) : finiteView r.registrations out m := by
  obtain ⟨written,decoded,same⟩ := Option.map_eq_some_iff.mp step
  cases same
  exact finiteWriteback_result_view _ _ _ _ r.separated decoded

/-- Existing source read effect, with its real view premise; successful concrete
writeback derives that premise via store_view, not a supplied adequacy theorem. -/
theorem readCell_view {E ds d active tr a origin Γ} (r : @CheckedInheritedDeclarations E ds d active tr a origin)
    (F : Source.Fr) (s : Source.EMState E Γ) (m : SlotView)
    (view : finiteView r.registrations
      (if tr then s.2.ex.transient.cells F.this else (s.2.ex.world.accounts F.this).storage) m)
    (c : ScalarPath E.layout (E.lay a)) (member : c ∈ r.registrations) :
    ∃ v, (Source.readCell (E := E) F c.path).run s = (.ok v,s) ∧ c.codec.encode v = c.field.findWord (m c.slot) := by
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp (view c member)
  refine ⟨v,?_,encoded⟩
  have stateRead : (Source.EM.st (E := E) (Γ := Γ)).run s = (.ok s.2,s) := rfl
  unfold Source.readCell
  rw [Source.Hoare.run_bind,stateRead]
  dsimp only
  rw [r.bank_agreement c member]
  cases tr with
  | false =>
    change (s.2.ex.world.accounts F.this).storage.read c.path = some v at read
    simp only [Bool.false_eq_true,if_false,read]
    rfl
  | true =>
    change (s.2.ex.transient.cells F.this).read c.path = some v at read
    simp only [if_true,read]
    rfl

end CheckedInheritedDeclarations
end Solidity.Yul.Views
