import Solidity.Lowering.Readonly.PrimitiveValues
import Solidity.Lowering.Readonly.InvocationFrame

/-! Checked primitive field correspondence for the caller-storage projection.
Every target field has a named, existing source state declaration, exact type
and actual storage path. This covers every target primitive field, not every
source declaration or arbitrary aggregate layout; no ABI decoding occurs. -/
namespace Solidity.Lowering.Readonly.PrimitiveFields
open Solidity.Source
open PrimitiveValues InvocationFrame
variable {E : Env}

inductive Fields (E : Env) : List (Name × Ty) → Type where
  | nil : Fields E []
  | field (name : Name) (p : PrimTy) (d : Decl)
      (declared : E.declOf .stateVar ⟨d.scope, d.name⟩ = some d)
      (named : name = d.name) (signature : d.varTy E = some (sourceTy p))
      (typed : E.cellTy d.path = sourceTy p) (persistent : E.transientRoot d.path = false)
      (notConst : d.isConst = false) {rest : List (Name × Ty)} (tail : Fields E rest) :
      Fields E ((name, .prim p) :: rest)

/-- Read actual typed source paths, with exact primitive value equality. -/
def Rel {fs : List (Name × Ty)} (fields : Fields E fs) (caller : Solidity.Roadmap.Address)
    (source : Solidity.Source.Storage E.layout (E.lay caller)) (target : SFields fs) : Prop := by
  induction fields with
  | nil => exact True
  | field name p d declared named signature typed persistent notConst tail ih =>
    cases target with
    | cons value rest =>
      cases value with
      | prim value =>
        exact source.read d.path = some (show Solidity.Source.Val E.layout (E.cellTy d.path) from
          typed.symm ▸ toSource E.layout p value) ∧ ih rest

private theorem cast_injective {D : Layout} {τ σ : STy} (h : τ = σ)
    (left right : Solidity.Source.Val D σ) (same : h.symm ▸ left = h.symm ▸ right) : left = right := by
  cases h
  exact same

private theorem cast_back {D : Solidity.Source.Layout} {τ σ : STy} (h : τ = σ)
    (value : Solidity.Source.Val D τ) : h.symm ▸ (h ▸ value) = value := by
  cases h
  rfl

private theorem default_transport (D : Solidity.Source.Layout) (τ : STy) (p : PrimTy)
    (h : τ = sourceTy p) : Solidity.Source.Val.default D τ =
      some (h.symm ▸ toSource D p (PrimTy.dflt p)) := by
  cases h
  exact default_value D p

/-- Every typed primitive read is represented, including unwritten cells:
the default comes from the ACTUAL source Storage.read/Val.default APIs. -/
theorem read_value (caller : Solidity.Roadmap.Address)
    (source : Solidity.Source.Storage E.layout (E.lay caller)) (path : Solidity.Source.SPath) (p : PrimTy)
    (typed : E.cellTy path = sourceTy p) :
    ∃ value : p.Denote, source.read path = some
      (show Solidity.Source.Val E.layout (E.cellTy path) from typed.symm ▸ toSource E.layout p value) := by
  cases cell : source.cell path with
  | none =>
    refine ⟨PrimTy.dflt p, ?_⟩
    simp only [Solidity.Source.Storage.read, cell]
    exact default_transport E.layout (E.cellTy path) p typed
  | some value =>
    refine ⟨fromSource E.layout p (typed ▸ value), ?_⟩
    simp only [Solidity.Source.Storage.read, cell]
    rw [PrimitiveValues.to_from, cast_back]

/-- A complete target primitive field list has a representation for every
source storage, not just preinitialised source cells. -/
theorem total {fs : List (Name × Ty)} (fields : Fields E fs)
    (caller : Solidity.Roadmap.Address) (source : Solidity.Source.Storage E.layout (E.lay caller)) :
    ∃ target : SFields fs, Rel fields caller source target := by
  induction fields with
  | nil => exact ⟨.nil, True.intro⟩
  | field name p d declared named signature typed persistent notConst tail ih =>
    obtain ⟨value, read⟩ := read_value caller source d.path p typed
    obtain ⟨rest, tailRel⟩ := ih
    exact ⟨.cons (.prim value) rest, read, tailRel⟩

/-- Representation preserves every target field value, rather than merely
choosing an arbitrary functional map from whole source storage. -/
theorem unique {fs : List (Name × Ty)} (fields : Fields E fs)
    (caller : Solidity.Roadmap.Address) (source : Solidity.Source.Storage E.layout (E.lay caller))
    (left right : SFields fs) (hl : Rel fields caller source left) (hr : Rel fields caller source right) :
    left = right := by
  induction fields with
  | nil => cases left; cases right; rfl
  | field name p d declared named signature typed persistent notConst tail ih =>
    cases left with
    | cons lv lt =>
      cases right with
      | cons rv rt =>
        cases lv with
        | prim l =>
          cases rv with
          | prim r =>
            change (_ ∧ Rel tail caller source lt) at hl
            change (_ ∧ Rel tail caller source rt) at hr
            have sourceEqual := Option.some.inj (hl.1.symm.trans hr.1)
            have valueEqual := faithful E.layout p (cast_injective typed _ _ sourceEqual)
            cases valueEqual
            have restEqual := ih lt rt hl.2 hr.2
            cases restEqual
            rfl

/-- One selected actual source declaration, retaining all checked metadata. -/
structure Binding (E : Env) (name : Name) (p : PrimTy) where
  declaration : Decl
  declared : E.declOf .stateVar ⟨declaration.scope, declaration.name⟩ = some declaration
  named : name = declaration.name
  signature : declaration.varTy E = some (sourceTy p)
  typed : E.cellTy declaration.path = sourceTy p
  persistent : E.transientRoot declaration.path = false
  notConst : declaration.isConst = false

/-- Select any actual named target field, not just the first field. The full
relation determines BOTH its source read and its intrinsic root-read value. -/
theorem select {fs : List (Name × Ty)} (fields : Fields E fs)
    (caller : Solidity.Roadmap.Address) (source : Solidity.Source.Storage E.layout (E.lay caller))
    (target : SFields fs) (name : Name) (p : PrimTy)
    (lookup : Solidity.Semantics.lookupBy name fs = some (.prim p)) (related : Rel fields caller source target) :
    ∃ binding : Binding E name p, ∃ value : p.Denote,
      source.read binding.declaration.path = some
        (show Solidity.Source.Val E.layout (E.cellTy binding.declaration.path) from
          binding.typed.symm ▸ toSource E.layout p value) ∧ target.get lookup = .prim value := by
  induction fields with
  | nil => cases lookup
  | field fieldName q d declared named signature typed persistent notConst tail ih =>
    cases target with
    | cons head rest =>
      cases head with
      | prim head =>
        change (_ ∧ Rel tail caller source rest) at related
        by_cases same : name = fieldName
        · subst name
          have types := SFields.lookupBy_cons_pos rfl lookup
          have primitives : q = p := Ty.prim.inj types
          cases primitives
          refine ⟨⟨d, declared, named, signature, typed, persistent, notConst⟩, head, related.1, ?_⟩
          rw [SFields.get_cons]
          simp only []
          rfl
        · have tailLookup := SFields.lookupBy_cons_neg same lookup
          obtain ⟨binding, value, read, targetRead⟩ := ih rest tailLookup related.2
          refine ⟨binding, value, read, ?_⟩
          rw [SFields.get_cons]
          simp only [dif_neg same]
          exact targetRead

structure Layout (E : Env) (C : Contract) where
  fields : Fields E C.vars
  persistent : C.transientRoots = []

/-- The existing source inheritance relation validates each declaration owner
against the actual caller frame's most-derived contract name. -/
def Owned {fs : List (Name × Ty)} (fields : Fields E fs) (owner : String) : Prop := by
  induction fields with
  | nil => exact True
  | field name p d declared named signature typed persistent notConst tail ih =>
    exact (∃ declaredOwner, d.scope = some declaredOwner ∧
      E.isBase ⟨none, owner⟩ ⟨none, declaredOwner⟩ = true) ∧ ih

structure CallLayout {Γ : RCtx} {dn : DeclName} {ps rs : List STy}
    (i : Invocation E Γ dn ps rs) (C : Contract) where
  layout : Layout E C
  owned : Owned layout.fields i.frame.contract

def representation {C : Contract} (layout : Layout E C) (caller : Solidity.Roadmap.Address) :
    StorageRepresentation E C caller where
  relates := Rel layout.fields caller
  unique := fun source left right hl hr => unique layout.fields caller source left right hl hr

/-- The same-invocation P2 transport now uses a fieldwise, typed, named layout
certificate. Actual P1/P3 production and whole-body coverage remain explicit. -/
theorem caller_storage {C : Contract} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}
    (i : Invocation E Γ dn ps rs) (result : Except Halt Solidity.Roadmap.Outcome) (final : St E)
    (raw : i.RawAt result final) (frames : i.RuntimeFrames final) (layout : Layout E C)
    (before after : Solidity.Storage C)
    (entry : Rel layout.fields i.frame.this (i.after.2.ex.world.accounts i.frame.this).storage before)
    (exit : Rel layout.fields i.frame.this (final.ex.world.accounts i.frame.this).storage after) :
    after = before :=
  typed_storage i result final raw frames (representation layout i.frame.this) before after entry exit

/-- Primitive field lowering constructs an exit representation; it need not
assume a favorable exit relation to obtain the same typed caller storage. -/
theorem caller_exit {C : Contract} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}
    (i : Invocation E Γ dn ps rs) (result : Except Halt Solidity.Roadmap.Outcome) (final : St E)
    (raw : i.RawAt result final) (frames : i.RuntimeFrames final) (layout : Layout E C)
    (before : Solidity.Storage C)
    (entry : Rel layout.fields i.frame.this (i.after.2.ex.world.accounts i.frame.this).storage before) :
    ∃ after : Solidity.Storage C,
      Rel layout.fields i.frame.this (final.ex.world.accounts i.frame.this).storage after ∧ after = before := by
  obtain ⟨after, exit⟩ := total layout.fields i.frame.this (final.ex.world.accounts i.frame.this).storage
  exact ⟨after, exit, caller_storage i result final raw frames layout before after entry exit⟩

/-- The caller-frame-bound variant retains explicit source ownership as well
as named typed paths; it does not select an arbitrary contract's fields. -/
theorem lowered_caller_exit {C : Contract} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}
    (i : Invocation E Γ dn ps rs) (result : Except Halt Solidity.Roadmap.Outcome) (final : St E)
    (raw : i.RawAt result final) (frames : i.RuntimeFrames final) (layout : CallLayout i C)
    (before : Solidity.Storage C)
    (entry : Rel layout.layout.fields i.frame.this (i.after.2.ex.world.accounts i.frame.this).storage before) :
    ∃ after : Solidity.Storage C,
      Rel layout.layout.fields i.frame.this (final.ex.world.accounts i.frame.this).storage after ∧ after = before :=
  caller_exit i result final raw frames layout.layout before entry

end Solidity.Lowering.Readonly.PrimitiveFields
