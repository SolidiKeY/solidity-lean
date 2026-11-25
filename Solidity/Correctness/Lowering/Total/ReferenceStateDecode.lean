import Solidity.Correctness.Lowering.Total.ConstructorDecode
import Solidity.Correctness.Lowering.Total.ReferenceDecode

/-!
# Reference state-root declarations

The declaration component for the roots `TransientDecode` and `ConstructorDecode`
refuse. Reads `Contract.vars` in order with `widths`, `transientRoots`, `structs`
and `inits`, and spells one Source state variable per root: a primitive at the
landed element table's type (`TransientDecode.elemOf`, used as it is); a
reference by `ReferenceDecode.spellRef` in storage at the root's own row keys,
once every row at or below the root is one the spelling reads (`unread`). A
struct is written by the one identifier `Contract.structs` reads as its encoded
table type. Initializers are consumed in their own order (`Constructor.takeInit`)
and spelled by the given expression speller, each on its target root.

A root, row below a reference root, or initializer with no spelling is an `Error`
naming the root: a gap of this component, not an admission condition. Proved:
every root once and in order with its initializers (`partsOf_faithful`); each
declaration's `Source.Decl.varTy` represents its root, under
`ReferenceDecode.Resolved` for the structs mentioned and nothing else
(`partsOf_typed`); `rootDecl_elabInit`; the parts of `Constructor.stateParts`
and `TransientDecode.declsT` wherever those succeed; no contract has a
transient reference root (`ref_not_transient`).

Open, with the composing lane: discharging `Resolved`; struct declarations;
`bytes`/`string`, enum and function-type positions (refused by their rows;
`Contract.enums` is not read); `address payable`, read `address` as `elemB` does;
rows of no root and rows below a primitive root (not inspected); visibility,
constness and override (not retained); identifiers and the `transient` pragma;
the constructor part, placement and elaboration of the unit; that a success on
primitive roots is one of the landed components (the converse of the agreement);
frame correspondence, the meaning of `transient`, and all execution agreement.
No `lowerLoopsCorrect` credit.
-/
namespace Solidity.Correctness.Lowering.Total.ReferenceStateDecode

open Source (Syn STy)
open Decode
open Decode.Constructor (Ordered takeInit)
open ReferenceDecode (spellRef unread Rep Resolved structsTy written? bind_ok)

/-- Why a root list has no declaration list; each names the root concerned. -/
inductive Error where
  | noElem (root : Name) (p : PrimTy) -- the element table reads no elementary type
  | unreadRow (root key : Name) (value : Nat) -- a row below a reference root, not read
  | type (root : Name) (reason : ReferenceDecode.Error) -- no Source spelling of the type
  | transientReference (root : Name) -- Solidity has no transient reference
  | transientInit (root : Name) -- Solidity rejects it
  | unspelledInit (root : Name) (e : RawExpr) -- the expression speller refuses it
  /-- Pending when the roots are exhausted: its target is no root, precedes an
  earlier initializer's root, or already had one. -/
  | strayInit (target : Name)
  deriving Repr

/-- The Source type name of the root `x`: the element table's for a primitive;
for a reference, `spellRef` in storage, once every row at or below `x` is read. -/
def rootType (C : Contract) (el : Name → PrimTy → Option Source.Elem) (x : Name) :
    Ty → Except Error (Syn .typeName)
  | .prim p => match el x p with
    | some e => .ok (.elem e)
    | none => .error (.noElem x p)
  | .ref R => match unread C.widths x (.ref R) with
    | some r => .error (.unreadRow x r.1 r.2)
    | none => match spellRef C C.widths x .storage R with
      | .ok t => .ok t
      | .error e => .error (.type x e)

/-- The spelled initializer of the root `x`, if one is pending for it. -/
def initOf (tr : Name → Bool) (spell : RawExpr → Option (Syn .expr)) (x : Name) :
    Option RawExpr → Except Error (Syn (.opt .expr))
  | none => .ok .none
  | some e => if tr x then .error (.transientInit x) else match spell e with
    | some s => .ok (.some s)
    | none => .error (.unspelledInit x e)

/-- The state variables in root order over a root-type speller, each with its
pending initializer; the result exists only when the initializers' order is the
root order and each names a root. No visibility, constness or override is
written: none is retained. -/
def partsOf (ty : Name → Ty → Except Error (Syn .typeName)) (tr : Name → Bool)
    (spell : RawExpr → Option (Syn .expr)) :
    List (Name × Ty) → List (Name × RawExpr) → Except Error (Syn (.list (.part false)))
  | [], [] => .ok .nil
  | [], i :: _ => .error (.strayInit i.1)
  | (x, T) :: vars, inits => do
    let t ← ty x T
    if tr x && !T.isPrimitive then .error (.transientReference x) else do
      let init ← initOf tr spell x (takeInit x inits).1
      let rest ← partsOf ty tr spell vars (takeInit x inits).2
      .ok (.cons (.stateVar t none none none (tr x) x init) rest)

/-- **The state-variable declarations of a contract**: every root, primitive or
reference, with its initializer. -/
def state (T : Tables) (R : CallSpellExt.Registry) (C : Contract) :
    Except Error (Syn (.list (.part false))) :=
  partsOf (rootType C (TransientDecode.elemOf C)) (fun x => C.transientRoots.contains x)
    (Calls.expr T R) C.vars C.inits

/-- The declaration Source collects for a state variable of `scope` written at
the type name `t`; at `.elem e` it is `Constructor.varDecl`. -/
def rootDecl (scope : String) (t : Syn .typeName) (transient : Bool) (x : Name)
    (init : Syn (.opt .expr)) : Source.Decl :=
  ⟨.stateVar, x, some scope, false, .stateVar t none none none transient x init⟩

variable {C : Contract} {el : Name → PrimTy → Option Source.Elem} {E : Source.Env}
  {ty : Name → Ty → Except Error (Syn .typeName)} {tr : Name → Bool}
  {spell : RawExpr → Option (Syn .expr)}

theorem rootType_prim {x : Name} {p : PrimTy} {t : Syn .typeName}
    (h : rootType C el x (.prim p) = .ok t) : ∃ e, el x p = some e ∧ t = .elem e := by
  simp only [rootType] at h
  split at h <;> cases h
  exact ⟨_, by assumption, rfl⟩

/-- A reference root's type name is `spellRef`'s, with every row below it read. -/
theorem rootType_ref {x : Name} {R : RefTy} {t : Syn .typeName}
    (h : rootType C el x (.ref R) = .ok t) :
    unread C.widths x (.ref R) = none ∧ spellRef C C.widths x .storage R = .ok t := by
  simp only [rootType] at h
  split at h
  · cases h
  · rename_i hu
    split at h <;> cases h
    exact ⟨hu, by assumption⟩

theorem initOf_ok {x : Name} {o : Option RawExpr} {init : Syn (.opt .expr)}
    (h : initOf tr spell x o = .ok init) : (o = none ∧ init = .none) ∨
      ∃ e s, o = some e ∧ tr x = false ∧ spell e = some s ∧ init = .some s := by
  unfold initOf at h
  split at h
  · cases h; exact .inl ⟨rfl, rfl⟩
  · split at h
    · cases h
    · rename_i ht
      split at h <;> cases h
      exact .inr ⟨_, _, rfl, by simpa using ht, by assumption, rfl⟩

/-- A successful assembly, one root at a time. -/
theorem partsOf_cons {x : Name} {T : Ty} {vars : List (Name × Ty)}
    {inits : List (Name × RawExpr)} {parts : Syn (.list (.part false))}
    (h : partsOf ty tr spell ((x, T) :: vars) inits = .ok parts) :
    ∃ t init rest, ty x T = .ok t ∧ (tr x = true → T.isPrimitive = true) ∧
      initOf tr spell x (takeInit x inits).1 = .ok init ∧
      partsOf ty tr spell vars (takeInit x inits).2 = .ok rest ∧
      parts = .cons (.stateVar t none none none (tr x) x init) rest := by
  simp only [partsOf, bind_ok] at h
  obtain ⟨t, ht, h⟩ := h
  split at h
  · cases h
  · rename_i hx
    simp only [bind_ok] at h
    obtain ⟨init, hi, rest, hr, h⟩ := h
    cases h
    exact ⟨t, init, rest, ht, fun htr => by simpa [htr] using hx, hi, hr, rfl⟩

theorem takeInit_none {x : Name} {inits : List (Name × RawExpr)}
    (h : (takeInit x inits).1 = none) : (takeInit x inits).2 = inits := by
  cases inits with
  | nil => rfl
  | cons i inits =>
      simp only [takeInit] at h ⊢
      split <;> rename_i hxy
      · rw [if_pos hxy] at h; cases h
      · rfl

theorem takeInit_some {x : Name} {inits : List (Name × RawExpr)} {e : RawExpr}
    (h : (takeInit x inits).1 = some e) : inits = (x, e) :: (takeInit x inits).2 := by
  cases inits with
  | nil => cases h
  | cons i inits =>
      obtain ⟨y, e'⟩ := i
      simp only [takeInit] at h ⊢
      split at h <;> cases h
      rename_i hxy
      subst hxy
      simp only [if_true]

/-- One root and its Source declaration: a state variable of `scope` under the
root's name, at the type name `ty` spells for it, transient as marked, and a
transient one primitive. -/
def RootSlot (ty : Name → Ty → Except Error (Syn .typeName)) (tr : Name → Bool) (scope : String)
    (v : Name × Ty) (d : Source.Decl) : Prop :=
  ∃ t init, ty v.1 v.2 = .ok t ∧ (tr v.1 = true → v.2.isPrimitive = true) ∧
    d = rootDecl scope t (tr v.1) v.1 init

/-- One model initializer and its Source declaration: the target root, not
transient, with the original expression as spelled (as `Constructor.InitSlot`). -/
def InitSlot (spell : RawExpr → Option (Syn .expr)) (scope : String) (i : Name × RawExpr)
    (d : Source.Decl) : Prop :=
  ∃ t s, spell i.2 = some s ∧ d = rootDecl scope t false i.1 (.some s)

/-- **Roots and initializers are preserved**: the collected declarations are
the roots, one each and in order; those carrying an initializer are the model's
initializers, one each and in order, each on its target root. -/
theorem partsOf_faithful (scope : String) :
    ∀ vars inits parts, partsOf ty tr spell vars inits = .ok parts →
      Ordered (RootSlot ty tr scope) vars (parts.collect (some scope)) ∧
      Ordered (InitSlot spell scope) inits
        ((parts.collect (some scope)).filter fun d => d.init?.isSome)
  | [], [], _, h => by cases h; exact ⟨.nil, .nil⟩
  | [], _ :: _, _, h => by cases h
  | (x, T) :: vars, inits, parts, h => by
      obtain ⟨t, init, rest, ht, htr, hi, hr, rfl⟩ := partsOf_cons h
      obtain ⟨ihv, ihi⟩ := partsOf_faithful scope vars _ rest hr
      rw [Source.Syn.collect]
      refine ⟨.cons ⟨t, init, ht, htr, rfl⟩ ihv, ?_⟩
      rcases initOf_ok hi with ⟨hn, rfl⟩ | ⟨e, s, hn, hx, hs, rfl⟩
      · rw [takeInit_none hn] at ihi
        exact ihi
      · rw [takeInit_some hn, hx]
        exact .cons ⟨t, s, hs, rfl⟩ ihi

/-- What the declared Source type of a root denotes. A primitive: the element
table's type, in storage. A reference: `ReferenceDecode.Rep` at the root's own
rows in storage, with no row at or below the root left unread. -/
inductive RootRep (C : Contract) (el : Name → PrimTy → Option Source.Elem) (E : Source.Env)
    (scope : Option String) (x : Name) : Ty → STy → Prop where
  | prim {p e} : el x p = some e → RootRep C el E scope x (.prim p) (e.ty .storage)
  | ref {R τ} : unread C.widths x (.ref R) = none →
      Rep C C.widths E scope x .storage (.ref R) τ → RootRep C el E scope x (.ref R) τ

/-- **A root's type name elaborates** to a type representing the root, under the
resolution obligations of the structs it mentions and nothing else. -/
theorem rootType_typed {scope : Option String} {x : Name} {T : Ty} {t : Syn .typeName}
    (h : rootType C el x T = .ok t)
    (res : ∀ s ∈ structsTy T, ∀ w, written? C s = some w → ∃ d, Resolved E scope w d) :
    ∃ τ, t.ty E scope .storage = some τ ∧ RootRep C el E scope x T τ := by
  cases T with
  | prim p =>
      obtain ⟨e, he, rfl⟩ := rootType_prim h
      exact ⟨e.ty .storage, rfl, .prim he⟩
  | ref R =>
      obtain ⟨hu, hs⟩ := rootType_ref h
      obtain ⟨τ, typed, rep⟩ := ReferenceDecode.spellRef_typed R x .storage t hs
        (by simpa only [structsTy] using res)
      exact ⟨τ, by simp only [Source.Syn.ty, typed], .ref hu rep⟩

/-- The declared type of a root's declaration is its type name's, in storage. -/
theorem rootDecl_varTy {scope : String} {t : Syn .typeName} {τ : STy}
    (h : t.ty E (some scope) .storage = some τ) (transient : Bool) (x : Name)
    (init : Syn (.opt .expr)) : (rootDecl scope t transient x init).varTy E = some τ := h

/-- One root and its Source declaration, typed: a non-constant state variable of
`scope` under the root's name, transient as marked, whose declared type
elaborates and represents the root. -/
def TypedRoot (C : Contract) (el : Name → PrimTy → Option Source.Elem) (tr : Name → Bool)
    (E : Source.Env) (scope : String) (v : Name × Ty) (d : Source.Decl) : Prop :=
  ∃ τ, d.varTy E = some τ ∧ RootRep C el E (some scope) v.1 v.2 τ ∧ d.kind = .stateVar ∧
    d.name = v.1 ∧ d.scope = some scope ∧ d.isConst = false ∧ d.isTransient = tr v.1

/-- **Source declared types of an assembled root list**: one typed declaration
per root, in order, given resolution of the structs the roots mention. -/
theorem partsOf_typed : ∀ {vars : List (Name × Ty)} {inits : List (Name × RawExpr)}
    {parts : Syn (.list (.part false))} (scope : String),
    partsOf (rootType C el) tr spell vars inits = .ok parts →
    (∀ v ∈ vars, ∀ s ∈ structsTy v.2, ∀ w, written? C s = some w →
      ∃ d, Resolved E (some scope) w d) →
    Ordered (TypedRoot C el tr E scope) vars (parts.collect (some scope))
  | [], [], _, _, h, _ => by cases h; exact .nil
  | [], _ :: _, _, _, h, _ => by cases h
  | (x, T) :: vars, inits, parts, scope, h, res => by
      obtain ⟨t, init, rest, ht, _, _, hr, rfl⟩ := partsOf_cons h
      obtain ⟨τ, typed, rep⟩ := rootType_typed (E := E) ht (res (x, T) List.mem_cons_self)
      rw [Source.Syn.collect]
      exact .cons ⟨τ, rootDecl_varTy typed (tr x) x init, rep, rfl, rfl, rfl, rfl, rfl⟩
        (partsOf_typed scope hr fun v m => res v (List.mem_cons_of_mem _ m))

/-- **A spelled initializer, elaborated**, at any root type: any result of
`Source.elabInit` on the root's declaration has the declared type, and its
expression is a typing derivation of the spelled expression under an implicit
conversion. Whether elaboration succeeds and what it evaluates to are not claimed. -/
theorem rootDecl_elabInit {scope : String} {t : Syn .typeName} {transient : Bool} {x : Name}
    {s : Syn .expr} {τ : STy} (hty : t.ty E (some scope) .storage = some τ)
    (i : {i : Source.RInit E //
      i.var = rootDecl scope t transient x (.some s) ∧ Source.RInit.Derived E i}) :
    i.val.τ = τ ∧
    ∃ (σ : STy) (D : Source.Typed (Source.Ctx.forInit E i.val.var.scope) s σ)
      (c : σ.implicit E.isBase E.mapFree i.val.τ = true), i.val.e = .conv D.toR (.inl c) := by
  obtain ⟨⟨var, τ', hτ, r⟩, hv, e, σ, D, c, he, hr⟩ := i
  cases hv
  cases (hτ.symm.trans (rootDecl_varTy hty transient x (.some s)) : some τ' = some _)
  cases (he : some s = some e)
  exact ⟨rfl, σ, D, c, hr⟩

/-- **Agreement with the constructor component**: where `Constructor.stateParts`
succeeds (its roots are all primitive), the assembly here gives the same parts:
roots, flags, initializers and order, hence the same slots. -/
theorem partsOf_stateParts (C : Contract) :
    ∀ (vars : List (Name × Ty)) (inits : List (Name × RawExpr))
      (parts : Syn (.list (.part false))),
      Constructor.stateParts el tr spell vars inits = some parts →
      partsOf (rootType C el) tr spell vars inits = .ok parts
  | [], [], _, h => by cases h; rfl
  | [], _ :: _, _, h => by cases h
  | (x, .ref _) :: _, _, _, h => by cases h
  | (x, .prim p) :: vars, inits, parts, h => by
      simp only [Constructor.stateParts, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨elem, he, rest, hr, h⟩ := h
      have ih := partsOf_stateParts C vars _ rest hr
      simp only [partsOf, rootType, he, ih, Ty.isPrimitive, Bool.not_true, Bool.and_false,
        Bool.false_eq_true, if_false, bind, Except.bind]
      split at h
      · rename_i hn; cases h; simp only [hn, initOf]
      · rename_i e hn
        split at h
        · cases h
        · rename_i ht
          simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨t, hs, rfl⟩ := h
          have ht : tr x = false := by simpa using ht
          simp only [hn, initOf, ht, Bool.false_eq_true, if_false, hs]

/-- **Agreement with the transient component**: where `TransientDecode.declsT`
succeeds, the assembly here without initializers gives the same declarations,
transient flags included. -/
theorem partsOf_declsT (C : Contract) (roots : List Name) (vars : List (Name × Ty))
    (parts : Syn (.list (.part false))) (h : TransientDecode.declsT el roots vars = .ok parts) :
    partsOf (rootType C el) (fun x => roots.contains x) spell vars [] = .ok parts := by
  induction (TransientDecode.declsT_ok_iff vars parts).mp h with
  | nil => rfl
  | cons he _ ih =>
      rename_i x p e rest ps hf
      have ih := ih ((TransientDecode.declsT_ok_iff rest ps).mpr hf)
      simp only [partsOf, rootType, he, takeInit, initOf, ih, Ty.isPrimitive, Bool.not_true,
        Bool.and_false, Bool.false_eq_true, if_false, bind, Except.bind]
      rfl

/-- **A contract has no transient reference root**: `Contract.transient_ok`
makes every transient root a primitive cell, and `vars_nodup` makes that cell
the root. So `transientReference` is a failure of root lists, never a contract's. -/
theorem ref_not_transient (C : Contract) {x : Name} {R : RefTy} (mem : (x, .ref R) ∈ C.vars) :
    C.transientRoots.contains x = false := by
  cases hc : C.transientRoots.contains x with
  | false => rfl
  | true =>
      have ok := C.transient_ok
      simp only [List.all_eq_true] at ok
      have hr := ok x (by simpa using hc)
      rw [Simulation.lookup_of_mem _ C.vars_nodup x _ mem] at hr
      cases hr

end Solidity.Correctness.Lowering.Total.ReferenceStateDecode
