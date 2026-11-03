import Solidity.Source.Resolved

/-! Actual S01 local bindings for Yul adapters. Resolve in the original Ctx
before constructing the intrinsic Idx. No declaration filtering, solc-ID
provenance, value classification, physical view or execution meaning is supplied
by this module. In particular an unsupported local must not expose a declaration
with the same name. -/
namespace Solidity.Yul

structure SourceLocalRef (ctx : Solidity.Source.Ctx) where
  {ty : Solidity.Source.STy}
  index : Solidity.Source.Idx ctx.tys ty

/-- Independent S01 name resolution and exact type-at-position premises. -/
inductive SourceLocalD (ctx : Solidity.Source.Ctx) (name : String) :
    SourceLocalRef ctx → Type where
  | intro (position : Nat) {ty : Solidity.Source.STy}
      (resolution : Solidity.Source.Resolves ctx.env (ctx.locals.map Prod.fst)
        ctx.scope name (.loc position))
      (typed : ctx.tys[position]? = some ty) :
      SourceLocalD ctx name ⟨Solidity.Source.Idx.ofGet? ctx.tys position typed⟩

def checkSourceLocal (ctx : Solidity.Source.Ctx) (name : String) :
    Option ((ref : SourceLocalRef ctx) × SourceLocalD ctx name ref) :=
  match hr : ctx.resolve name with
  | none => none
  | some (.decls _) => none
  | some (.builtin _) => none
  | some (.loc position) =>
    match ht : ctx.tys[position]? with
    | none => none
    | some _ty => some ⟨⟨Solidity.Source.Idx.ofGet? ctx.tys position ht⟩,
        .intro position (Solidity.Source.Env.resolve_sound hr) ht⟩

theorem SourceLocalD.complete {ctx name ref} (d : SourceLocalD ctx name ref) :
    checkSourceLocal ctx name = some ⟨ref, d⟩ := by
  cases d with
  | intro position resolution typed =>
    unfold checkSourceLocal
    have hr : ctx.resolve name = some (.loc position) := resolution.resolve
    split
    · next found => rw [hr] at found; cases found
    · next ds found => rw [hr] at found; cases found
    · next builtin found => rw [hr] at found; cases found
    · next selected found =>
      have same := Option.some.inj (found.symm.trans hr)
      cases same
      split
      · next absent => rw [typed] at absent; cases absent
      · next actual foundType =>
        have same := Option.some.inj (foundType.symm.trans typed)
        cases same
        rfl

theorem checkSourceLocal_iff (ctx : Solidity.Source.Ctx) (name : String) :
    (checkSourceLocal ctx name).isSome = true ↔
      ∃ ref, Nonempty (SourceLocalD ctx name ref) := by
  constructor
  · intro h
    cases found : checkSourceLocal ctx name with
    | none => rw [found] at h; cases h
    | some pair => exact ⟨pair.1, ⟨pair.2⟩⟩
  · rintro ⟨ref, ⟨d⟩⟩
    rw [d.complete]
    rfl

/-- Failed/local-ineligible classification must not retry another declaration.
The original S01 resolution itself is the premise, not a filtered namespace. -/
theorem checkSourceLocal_nonlocal (ctx : Solidity.Source.Ctx) (name : String)
    (notLocal : ∀ position, ctx.resolve name ≠ some (.loc position)) :
    checkSourceLocal ctx name = none := by
  unfold checkSourceLocal
  split
  · rfl
  · rfl
  · rfl
  · next position found => exact False.elim (notLocal position found)


/-- Concrete S01 typing, using the ORIGINAL resolution and type position. -/
def SourceLocalD.typed {ctx name ref} (d : SourceLocalD ctx name ref) :
    Solidity.Source.Typed ctx (.ident name) ref.ty :=
  SourceLocalD.casesOn (motive := fun ref _ =>
    Solidity.Source.Typed ctx (.ident name) ref.ty) d
    (intro := fun _ _ resolution typed => .loc resolution.resolve typed)

def SourceLocalD.lvalue {ctx name ref} (d : SourceLocalD ctx name ref) :
    Solidity.Source.LVal ctx (.ident name) ref.ty :=
  SourceLocalD.casesOn (motive := fun ref _ =>
    Solidity.Source.LVal ctx (.ident name) ref.ty) d
    (intro := fun _ _ resolution typed => .loc resolution.resolve typed)

/-- These adapters reach the EXISTING resolved terms with the exact selected
handle; they do not embed a Yul statement or alter S02's clean value type. -/
theorem SourceLocalD.typed_toR {ctx name ref} (d : SourceLocalD ctx name ref) :
    d.typed.toR = Solidity.Source.RExpr.local ref.index := by
  cases d
  rfl

theorem SourceLocalD.lvalue_toR {ctx name ref} (d : SourceLocalD ctx name ref) :
    d.lvalue.toR = Solidity.Source.RLVal.local ref.index := by
  cases d
  rfl


/-- The existing S01 constructor keeps the exact numeric position. -/
theorem sourceIdx_ofGet_position (types : Solidity.Source.RCtx) (position : Nat)
    {ty : Solidity.Source.STy} (typed : types[position]? = some ty) :
    (Solidity.Source.Idx.ofGet? types position typed).toNat = position := by
  induction types generalizing position with
  | nil => cases typed
  | cons first rest ih =>
    cases position with
    | zero =>
      have same : first = ty := Option.some.inj typed
      cases same
      rfl
    | succ position => exact congrArg Nat.succ (ih position typed)

theorem SourceLocalD.position_resolves {ctx name ref} (d : SourceLocalD ctx name ref) :
    ctx.resolve name = some (.loc ref.index.toNat) := by
  cases d with
  | intro position resolution typed =>
    change ctx.resolve name = some (.loc
      (Solidity.Source.Idx.ofGet? ctx.tys position typed).toNat)
    rw [sourceIdx_ofGet_position]
    exact resolution.resolve

/-- Every actual S01 local resolution has a type at its selected position.
There is no caller-supplied type/range premise in this acceptance theorem. -/
theorem checkSourceLocal_resolves_iff (ctx : Solidity.Source.Ctx) (name : String) :
    (checkSourceLocal ctx name).isSome = true ↔
      ∃ position, ctx.resolve name = some (.loc position) := by
  rw [checkSourceLocal_iff]
  constructor
  · rintro ⟨ref, ⟨d⟩⟩
    exact ⟨ref.index.toNat, d.position_resolves⟩
  · rintro ⟨position, resolved⟩
    have derivation := Solidity.Source.Env.resolve_sound resolved
    cases derivation with
    | inLocals position lookup =>
      rw [List.idxOf?_eq_map_finIdxOf?_val] at lookup
      rcases Option.map_eq_some_iff.mp lookup with ⟨index, found, same⟩
      have bound : position < ctx.tys.length := by
        rw [← same]
        simpa only [Solidity.Source.Ctx.tys, List.length_map] using index.isLt
      have typed : ctx.tys[position]? = some ctx.tys[position] :=
        List.getElem?_eq_getElem bound
      exact ⟨⟨Solidity.Source.Idx.ofGet? ctx.tys position typed⟩,
        ⟨.intro position (Solidity.Source.Env.resolve_sound resolved) typed⟩⟩

end Solidity.Yul
