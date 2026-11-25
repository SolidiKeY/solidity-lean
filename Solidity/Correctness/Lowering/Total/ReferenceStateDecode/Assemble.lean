import Solidity.Correctness.Lowering.Total.ConstructorDecode
import Solidity.Correctness.Lowering.Total.ReferenceDecode

/-!
# Reference state-root declarations: the decoder

Reads `Contract.vars` in order with `Contract.widths`, `transientRoots`,
`structs` and `inits`, and spells one Source state variable per root:

* a primitive root at the element table's type (`TransientDecode.elemOf`, the
  landed primitive decoding, used as it is);
* a reference root by `ReferenceDecode.spellRef` at storage location, at the
  root's own row keys (`xs[]`, `m{}`, `m[]`, …), after checking that every row
  at or below the root is one the spelling reads (`ReferenceDecode.unread`). A
  struct is written by the one identifier `Contract.structs` reads as its
  encoded table type (`written?`), never by the encoded name.

Initializers are consumed in their own order (`Constructor.takeInit`) and spelled
by the given expression speller, each on its target root. Every unsupported
input is an `Error` naming the root and the reason; no root or initializer is
dropped, moved, retyped or guessed. An `Error` is a gap of this component, not an
admission condition.

`partsOf_faithful`: the collected declarations are the roots, one each and in
order, and those with an initializer are the model's initializers, in order.
-/
namespace Solidity.Correctness.Lowering.Total.ReferenceStateDecode

open Source (Syn STy DataLoc)
open Decode
open Decode.Constructor (Ordered takeInit)
open ReferenceDecode (spellRef unread bind_ok)

/-- Why a root list has no declaration list. Each names the root concerned. -/
inductive Error where
  /-- A primitive root the element table gives no elementary type: no reading
  of its rows, or an enum or function-type marker (`TransientDecode.elemOf`). -/
  | noElem (root : Name) (p : PrimTy)
  /-- A width or marker row at or below a reference root that its spelling does
  not read (an enum, function-type or stale row): the type would be guessed. -/
  | unreadRow (root key : Name) (value : Nat)
  /-- The reference type has no Source spelling; the reason is the type decoder's. -/
  | type (root : Name) (reason : ReferenceDecode.Error)
  /-- A reference root marked transient (Solidity has no transient reference). -/
  | transientReference (root : Name)
  /-- An initializer of a transient root (Solidity rejects it). -/
  | transientInit (root : Name)
  /-- An initializer the expression speller does not spell. -/
  | unspelledInit (root : Name) (e : RawExpr)
  /-- A pending initializer when the roots are exhausted: its target is no
  root, precedes an earlier initializer's root, or already had one. -/
  | strayInit (target : Name)
  /-- The constructor component (`Constructor.constructorPart`) refused. -/
  | constructor
  deriving Repr

/-- The Source type name of the root `x`: the element table's for a primitive;
for a reference, `spellRef` in storage at the contract's width rows, once every
row at or below `x` is read. -/
def rootType (C : Contract) (el : Name → PrimTy → Option Source.Elem) (x : Name) :
    Ty → Except Error (Syn .typeName)
  | .prim p =>
    match el x p with
    | some e => .ok (.elem e)
    | none => .error (.noElem x p)
  | .ref R =>
    match unread C.widths x (.ref R) with
    | some r => .error (.unreadRow x r.1 r.2)
    | none =>
      match spellRef C C.widths x .storage R with
      | .ok t => .ok t
      | .error e => .error (.type x e)

/-- The spelled initializer of the root `x`, if one is pending for it. -/
def initOf (tr : Name → Bool) (spell : RawExpr → Option (Syn .expr)) (x : Name) :
    Option RawExpr → Except Error (Syn (.opt .expr))
  | none => .ok .none
  | some e =>
    if tr x then .error (.transientInit x) else
      match spell e with
      | some s => .ok (.some s)
      | none => .error (.unspelledInit x e)

/-- The state variables in root order over a root-type speller `ty`, each with
its pending initializer. Initializers are consumed in their own order, so the
result exists only when that order is the root order and each names a root. No
visibility, constness or override is written: none is retained. -/
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

/-- **The state-variable declarations of a contract**: every root of
`Contract.vars`, primitive or reference, with its initializer. -/
def state (T : Tables) (R : CallSpellExt.Registry) (C : Contract) :
    Except Error (Syn (.list (.part false))) :=
  partsOf (rootType C (TransientDecode.elemOf C)) (fun x => C.transientRoots.contains x)
    (Calls.expr T R) C.vars C.inits

/-- The parts of the declaration assembly, as `Constructor.declarationParts`
orders them: the explicit constructor if there is one, then every root. -/
def declarationParts (T : Tables) (R : CallSpellExt.Registry) (C : Contract) :
    Except Error (Syn (.list (.part false))) := do
  let sv ← state T R C
  match C.ctor with
  | none => .ok sv
  | some d =>
    match Constructor.constructorPart T R d with
    | some node => .ok (.cons node sv)
    | none => .error .constructor

/-- The declaration Source collects for a state variable of `scope` written
with the type name `t`. -/
def rootDecl (scope : String) (t : Syn .typeName) (transient : Bool) (x : Name)
    (init : Syn (.opt .expr)) : Source.Decl :=
  ⟨.stateVar, x, some scope, false, .stateVar t none none none transient x init⟩

/-- At an elementary type it is the primitive component's declaration. -/
theorem varDecl_rootDecl (scope : String) (e : Source.Elem) (transient : Bool) (x : Name)
    (init : Syn (.opt .expr)) :
    Constructor.varDecl scope e transient x init = rootDecl scope (.elem e) transient x init := rfl

variable {C : Contract} {el : Name → PrimTy → Option Source.Elem}
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
    (h : initOf tr spell x o = .ok init) :
    (o = none ∧ init = .none) ∨
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
transient, with the original expression as spelled. -/
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

/-- **Names and order**: the declared names are the roots' names, in order. -/
theorem partsOf_names {vars : List (Name × Ty)} {inits : List (Name × RawExpr)}
    {parts : Syn (.list (.part false))} (h : partsOf ty tr spell vars inits = .ok parts)
    (scope : String) : (parts.collect (some scope)).map (·.name) = vars.map (·.1) := by
  have hv := (partsOf_faithful scope vars inits parts h).1
  generalize parts.collect (some scope) = ds at hv
  generalize vars = vs at hv
  induction hv with
  | nil => rfl
  | cons hd _ ih =>
      obtain ⟨_, _, _, _, rfl⟩ := hd
      simp only [List.map_cons, ih, rootDecl]

/-- **Declaration assembly**: the collected declarations are the constructor
declaration (one for an explicit constructor, none for the implicit one)
followed by the roots' declarations. -/
theorem declarationParts_collect {T : Tables} {R : CallSpellExt.Registry}
    {parts : Syn (.list (.part false))} (h : declarationParts T R C = .ok parts) (scope : String) :
    ∃ sv ctors, state T R C = .ok sv ∧ Constructor.ctorDecls T R scope C.ctor = some ctors ∧
      parts.collect (some scope) = ctors ++ sv.collect (some scope) := by
  simp only [declarationParts, bind_ok] at h
  obtain ⟨sv, hs, h⟩ := h
  cases hc : C.ctor with
  | none =>
      rw [hc] at h; cases h
      exact ⟨_, [], hs, rfl, rfl⟩
  | some d =>
      rw [hc] at h
      simp only at h
      split at h <;> cases h
      rename_i node hn
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ :=
        Constructor.constructorPart_faithful hn scope ⟨[]⟩
      refine ⟨sv, _, hs, by rw [Constructor.ctorDecls, hn]; rfl, ?_⟩
      rw [Source.Syn.collect]
      rfl

end Solidity.Correctness.Lowering.Total.ReferenceStateDecode
