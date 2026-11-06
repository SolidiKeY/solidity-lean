import Solidity.Yul.Views.LayoutOrigin

namespace Solidity.Yul.Views

/-- No caller-supplied origin. Both the origin and inherited packing are actual
successful computations over the existing source environment. -/
structure ComputedSourceLayout {E ds} (d : RootDeclarations E ds) (active : String)
    (tr : Bool) (a : Roadmap.Address) where
  origin : ActiveLayoutOrigin E active
  layout : CheckedInheritedDeclarations d active tr a (origin.forBank tr)

def prepareComputedLayout {E ds} (d : RootDeclarations E ds) (active : String)
    (tr : Bool) (a : Roadmap.Address) : Except LayoutOriginError (ComputedSourceLayout d active tr a) := do
  let origin ← prepareActiveOrigin E active
  let layout ← (prepareInheritedDeclarations d active tr a (origin.forBank tr)).mapError LayoutOriginError.declarations
  pure ⟨origin,layout⟩

theorem ComputedSourceLayout.nonwrapping {E ds d active tr a}
    (r : @ComputedSourceLayout E ds d active tr a) :
    (r.origin.forBank tr).val*32 ≤ r.layout.endByte ∧ r.layout.endByte ≤ (2^256)*32 := r.layout.nonwrapping

theorem ComputedSourceLayout.transient_unshifted {E ds d active a}
    (r : @ComputedSourceLayout E ds d active true a) : r.layout.endByte = d.endByte 0 := r.layout.extent

theorem ComputedSourceLayout.raw_reconstruction {E ds d active tr a}
    (r : @ComputedSourceLayout E ds d active tr a)
    (m : SlotView) (s out : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (step : r.layout.storeWriteback m s = some (out,residual)) :
    finiteEncode r.layout.registrations out residual = some m := r.layout.store_reencode _ _ _ _ step

/-- Successful literal layout-at retains an OWNER evaluation and exact range,
not an arbitrary caller word or a modular reduction. -/
theorem active_literal_semantics (name : String) (abstract : Bool) (scope : Option String)
    (e : Source.Syn .expr) (is : Source.Syn (.list .inherit)) (parts : Source.Syn (.list (.part false)))
    (word : Roadmap.Word)
    (success : activeDeclarationOrigin ⟨.contract,name,scope,true,.contract abstract name (.some e) is parts⟩ = .ok word) :
    ∃ q, e.const = some q ∧ q.FitsInt .u256 ∧ Source.isLiteralBase e = true ∧ (word.val : Int) = q.toInt := by
  change (if name = name then (prepareLiteralOrigin e).map ExactLiteralOrigin.value else _) = _ at success
  rw [if_pos rfl] at success
  cases prepared : prepareLiteralOrigin e with
  | error reason => simp only [prepared,Except.map] at success; cases success
  | ok o =>
    simp only [prepared,Except.map,Except.ok.injEq] at success
    cases success
    exact ⟨o.constant,o.evaluated,o.fits,o.profile,o.exactValue⟩

theorem active_default_origin (name : String) (abstract : Bool) (scope : Option String)
    (is : Source.Syn (.list .inherit)) (parts : Source.Syn (.list (.part false))) :
    activeDeclarationOrigin ⟨.contract,name,scope,true,.contract abstract name .none is parts⟩ = .ok 0 := by
  simp only [activeDeclarationOrigin,if_true]

theorem active_origin_profile {d : Source.Decl} {word : Roadmap.Word}
    (success : activeDeclarationOrigin d = .ok word) : d.node.excl = none := by
  rcases d with ⟨kind,name,scope,top,node⟩
  cases kind <;> cases top <;> try cases success
  cases node <;> try cases success
  case contract abstract contractName base is parts =>
    simp only [activeDeclarationOrigin] at success
    split at success
    · cases base with
      | none => rfl
      | some e =>
        cases prepared : prepareLiteralOrigin e with
        | error reason => simp only [prepared,Except.map] at success; cases success
        | ok o => exact literalOrigin_profile o abstract contractName is parts
    · cases success

theorem ActiveLayoutOrigin.profile {E active} (o : ActiveLayoutOrigin E active) : o.declaration.node.excl = none :=
  active_origin_profile o.computed

theorem ActiveLayoutOrigin.identity {E active} (o : ActiveLayoutOrigin E active) :
    o.declaration ∈ E.decls ∧ o.declaration.kind = .contract ∧ o.declaration.scope = none ∧ o.declaration.name = active := by
  have member := List.mem_of_find?_eq_some o.found
  have pred := List.find?_some o.found
  simp only [Bool.and_eq_true,beq_iff_eq] at pred
  exact ⟨member,pred.1.1,pred.1.2,pred.2⟩

end Solidity.Yul.Views
