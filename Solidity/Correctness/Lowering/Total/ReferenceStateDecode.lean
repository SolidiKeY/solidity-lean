import Solidity.Correctness.Lowering.Total.ReferenceStateDecode.Assemble

/-!
# Reference state-root declarations: typing, placement, compatibility

The declaration component for the state roots `TransientDecode` and
`ConstructorDecode` refuse: a root of reference type (array, fixed array,
mapping, struct) among `Contract.vars`. `Assemble` holds the decoder (`rootType`,
`partsOf`, `state`, `declarationParts`) and its ordered faithfulness; this module
proves the Source facts and the agreement with the landed components.

* **Types** (`rootType_typed`, `state_typed`): each collected declaration's
  `Source.Decl.varTy` is a type that represents the root (`RootRep`): a
  primitive at its element-table type, a reference by `ReferenceDecode.Rep` at
  storage location with every row at or below the root read. The only premise is
  `ReferenceDecode.Resolved` for the written name of each struct mentioned.
* **Initializers** (`rootDecl_elabInit`): a result of `Source.elabInit` on a
  spelled initializer has the root's declared type and is a derivation of the
  spelled expression; elaboration success is not claimed.
* **Placement** (`placed_state`, `placed_declarations`): in a unit that places
  the parts (`Constructor.Placed`), the contract's state variables are the roots
  in order, the program's initializers the model's in order, and the constructor
  declaration the assembled one.
* **Compatibility** (`partsOf_stateParts`, `stateParts_partsOf`,
  `partsOf_declsT`, `declsT_partsOf`, `declarationParts_compat`): on an
  all-primitive root list the result is `Constructor.stateParts`'s, and without
  initializers `TransientDecode.declsT`'s, in both directions.
* **Transient references** (`ref_not_transient`, `state_ne_transientReference`):
  `Contract.transient_ok` excludes them, so that failure never occurs on a
  contract.

Left open, with the composing lane: discharging `Resolved` (the struct
declaration lane), struct declarations and member widths, `bytes`/`string`,
enum and function-type positions (a named `Error`), stale rows below a primitive
root, visibility/constness/override (not retained, not written), identifier
validity, `Placed` and unit elaboration, the Source frame correspondence of a
root's value, and all execution agreement of initializers. A component: it
defines no admission predicate and gives no `lowerLoopsCorrect` credit.
-/
namespace Solidity.Correctness.Lowering.Total.ReferenceStateDecode

open Source (Syn STy DataLoc)
open Decode
open Decode.Constructor (Ordered takeInit Placed)
open ReferenceDecode (spellRef unread Rep Resolved structsTy written? bind_ok)

variable {C : Contract} {el : Name → PrimTy → Option Source.Elem} {tr : Name → Bool}
  {spell : RawExpr → Option (Syn .expr)} {E : Source.Env}

/-! ## Declared types -/

/-- What the declared Source type of a root denotes. A primitive: the element
table's type for it, in storage. A reference: `ReferenceDecode.Rep` at the root's
own rows in storage, with no row at or below the root left unread. -/
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
  ∃ τ, d.varTy E = some τ ∧ RootRep C el E (some scope) v.1 v.2 τ ∧ d.typesOK E = true ∧
    d.kind = .stateVar ∧ d.name = v.1 ∧ d.scope = some scope ∧ d.isConst = false ∧
    d.isTransient = tr v.1

theorem Ordered.imp {α β : Type} {r r' : α → β → Prop} : ∀ {as : List α} {bs : List β},
    Ordered r as bs → (∀ a ∈ as, ∀ b, r a b → r' a b) → Ordered r' as bs
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, imp =>
      .cons (imp _ List.mem_cons_self _ h) (Ordered.imp t fun a m => imp a (List.mem_cons_of_mem _ m))

/-- **Source declared types of an assembled root list**: one typed declaration
per root, in order, given resolution of the structs the roots mention. -/
theorem partsOf_typed {vars : List (Name × Ty)} {inits : List (Name × RawExpr)}
    {parts : Syn (.list (.part false))}
    (h : partsOf (rootType C el) tr spell vars inits = .ok parts) (scope : String)
    (res : ∀ v ∈ vars, ∀ s ∈ structsTy v.2, ∀ w, written? C s = some w →
      ∃ d, Resolved E (some scope) w d) :
    Ordered (TypedRoot C el tr E scope) vars (parts.collect (some scope)) := by
  refine Ordered.imp (partsOf_faithful scope vars inits parts h).1 fun v mv d slot => ?_
  obtain ⟨t, init, ht, _, rfl⟩ := slot
  obtain ⟨τ, typed, rep⟩ := rootType_typed (E := E) ht (res v mv)
  have vt := rootDecl_varTy typed (tr v.1) v.1 init
  have ok : (Source.Decl.varTy E (rootDecl scope t (tr v.1) v.1 init)).isSome = true := by
    rw [vt]; rfl
  exact ⟨τ, vt, rep, ok, rfl, rfl, rfl, rfl, rfl⟩

/-- **Declared types of a contract's roots.** -/
theorem state_typed {T : Tables} {R : CallSpellExt.Registry} {parts : Syn (.list (.part false))}
    (h : state T R C = .ok parts) (scope : String)
    (res : ∀ v ∈ C.vars, ∀ s ∈ structsTy v.2, ∀ w, written? C s = some w →
      ∃ d, Resolved E (some scope) w d) :
    Ordered (TypedRoot C (TransientDecode.elemOf C) (fun x => C.transientRoots.contains x) E scope)
      C.vars (parts.collect (some scope)) :=
  partsOf_typed h scope res

/-- A primitive root's table type is the marked decoder's reading of its rows
(`TransientDecode.Represents`), with no enum or function-type marker. -/
theorem RootRep.prim_represents {scope : Option String} {x : Name} {p : PrimTy} {τ : STy}
    (h : RootRep C (TransientDecode.elemOf C) E scope x (.prim p) τ) :
    ∃ e, τ = e.ty .storage ∧ TransientDecode.unreadMarker C.widths x = false ∧
      TransientDecode.Represents C.widths x p e ∧ Version.Prim p (e.ty .storage) := by
  cases h with
  | prim he =>
      obtain ⟨hm, he⟩ := TransientDecode.elemOf_some he
      exact ⟨_, rfl, hm, TransientDecode.elemB_represents he, (Version.elemB_prim he).1⟩

/-- **A spelled initializer, elaborated**, at any root type. Any result of
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

/-! ## Placement in a unit -/

private theorem placed_filter {scope : String} {parts : Syn (.list (.part false))}
    (h : Placed E scope parts) (q : Source.Decl → Bool)
    (hq : ∀ d, q d = true → d.scope = some scope ∧ (d.kind = .constructor ∨ d.kind = .stateVar)) :
    E.decls.filter q = (parts.collect (some scope)).filter q := by
  obtain ⟨before, after, hd, out⟩ := h
  have gone : ∀ l : List Source.Decl, (∀ d ∈ l, d ∈ before ++ after) → l.filter q = [] := by
    intro l hl
    rw [List.filter_eq_nil_iff]
    intro d hd hqd
    obtain ⟨h1, h2⟩ := out d (hl d hd) (hq d hqd).1
    exact (hq d hqd).2.elim h1 h2
  rw [hd, List.filter_append, List.filter_append,
    gone before (fun d hd => List.mem_append_left _ hd),
    gone after (fun d hd => List.mem_append_right _ hd), List.nil_append, List.append_nil]

/-- In a unit placing parts that collect to constructor declarations followed by
non-constant state variables of `scope`, Source finds exactly those. -/
theorem placed_split {scope : String} {parts : Syn (.list (.part false))}
    (placed : Placed E scope parts) {ctors ds : List Source.Decl}
    (hcol : parts.collect (some scope) = ctors ++ ds)
    (hc : ∀ d ∈ ctors, d.kind = .constructor ∧ d.scope = some scope)
    (hv : ∀ d ∈ ds, d.kind = .stateVar ∧ d.scope = some scope ∧ d.isConst = false) :
    E.decls.filter (fun d => d.kind == .constructor && d.scope == some scope) = ctors ∧
    E.stateVarsOf scope = ds := by
  constructor
  · rw [placed_filter placed _ (by simp +contextual), hcol, List.filter_append,
      List.filter_eq_self.mpr (fun d hd => by simp [hc d hd]),
      List.filter_eq_nil_iff.mpr (fun d hd => by simp [(hv d hd).1]), List.append_nil]
  · unfold Source.Env.stateVarsOf
    rw [placed_filter placed _ (by simp +contextual), hcol, List.filter_append,
      List.filter_eq_nil_iff.mpr (fun d hd => by simp [(hc d hd).1]),
      List.filter_eq_self.mpr (fun d hd => by simp [hv d hd]), List.nil_append]

theorem Ordered.right {α β : Type} {r : α → β → Prop} {P : β → Prop} : ∀ {as : List α}
    {bs : List β}, Ordered r as bs → (∀ a b, r a b → P b) → ∀ b ∈ bs, P b
  | _, _, .nil, _, _, m => nomatch m
  | _, _, .cons h t, imp, b, m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact imp _ _ h
      · exact Ordered.right t imp b m

/-- The collected declarations of an assembled root list are non-constant state
variables of `scope`. -/
theorem partsOf_kinds {ty : Name → Ty → Except Error (Syn .typeName)} {vars : List (Name × Ty)}
    {inits : List (Name × RawExpr)} {parts : Syn (.list (.part false))}
    (h : partsOf ty tr spell vars inits = .ok parts) (scope : String) :
    ∀ d ∈ parts.collect (some scope),
      d.kind = .stateVar ∧ d.scope = some scope ∧ d.isConst = false :=
  Ordered.right (partsOf_faithful scope vars inits parts h).1 fun _ _ slot => by
    obtain ⟨_, _, _, _, rfl⟩ := slot
    exact ⟨rfl, rfl, rfl⟩

private theorem unmap {scope : String} : ∀ (is : List (Name × RawExpr)) (rs : List (Source.RInit E)),
    Ordered (InitSlot spell scope) is (rs.map fun i => i.var) →
    Ordered (fun i (r : Source.RInit E) => InitSlot spell scope i r.var) is rs
  | _, [], h => by cases h; exact .nil
  | _, _ :: rs, h => by cases h with | cons hd tl => exact .cons hd (unmap _ rs tl)

private theorem placed_ordered {ty : Name → Ty → Except Error (Syn .typeName)}
    {vars : List (Name × Ty)} {inits : List (Name × RawExpr)} {state : Syn (.list (.part false))}
    (h : partsOf ty tr spell vars inits = .ok state) {scope : String}
    (hv : E.stateVarsOf scope = state.collect (some scope)) :
    Ordered (RootSlot ty tr scope) vars (E.stateVarsOf scope) ∧
    (Source.elaborates E = true →
      Ordered (fun i (r : Source.RInit E) => InitSlot spell scope i r.var)
        inits ((Source.progOf E).inits scope)) := by
  obtain ⟨roots, is⟩ := partsOf_faithful scope vars inits state h
  rw [← hv] at roots is
  refine ⟨roots, fun hE => ?_⟩
  rw [← Constructor.progOf_inits E scope hE] at is
  exact unmap _ _ is

/-- **Placed roots and initializers.** In a unit that places an assembled root
list, contract `scope`'s non-constant state variables are the roots'
declarations, one each and in root order; and when the unit elaborates, the
Source program's initializers of `scope` are the model's, one each and in order,
each the spelled original expression on its target root. -/
theorem placed_state {ty : Name → Ty → Except Error (Syn .typeName)} {vars : List (Name × Ty)}
    {inits : List (Name × RawExpr)} {parts : Syn (.list (.part false))}
    (h : partsOf ty tr spell vars inits = .ok parts) {scope : String}
    (placed : Placed E scope parts) :
    Ordered (RootSlot ty tr scope) vars (E.stateVarsOf scope) ∧
    (Source.elaborates E = true →
      Ordered (fun i (r : Source.RInit E) => InitSlot spell scope i r.var)
        inits ((Source.progOf E).inits scope)) :=
  placed_ordered h (placed_split placed (ctors := []) rfl (fun _ m => nomatch m)
    (partsOf_kinds h scope)).2

/-- **The placed declaration assembly**: constructor, roots and initializers as
Source finds them in a unit placing `declarationParts`. The constructor
declaration is the assembled one (none for the implicit constructor), with its
frame; the state variables and initializers are as in `placed_state`. -/
theorem placed_declarations {T : Tables} {R : CallSpellExt.Registry}
    {parts : Syn (.list (.part false))} (h : declarationParts T R C = .ok parts) {scope : String}
    (placed : Placed E scope parts) :
    (∃ ctors, Constructor.ctorDecls T R scope C.ctor = some ctors ∧
      E.ctorDecl scope = ctors.head? ∧ E.ctorFrame scope = ctors.head?.bind (·.frame? E) ∧
      (Source.progOf E).ctor scope =
        ctors.head?.bind fun d => (Source.elabBody E d).map Subtype.val) ∧
    Ordered (RootSlot (rootType C (TransientDecode.elemOf C))
      (fun x => C.transientRoots.contains x) scope) C.vars (E.stateVarsOf scope) ∧
    (Source.elaborates E = true →
      Ordered (fun i (r : Source.RInit E) => InitSlot (Calls.expr T R) scope i r.var)
        C.inits ((Source.progOf E).inits scope)) := by
  obtain ⟨sv, ctors, hs, hc, hcol⟩ := declarationParts_collect h scope
  have ctor : ∀ d ∈ ctors, d.kind = .constructor ∧ d.scope = some scope := by
    cases hctor : C.ctor <;> rw [hctor] at hc <;>
      simp only [Constructor.ctorDecls, Option.map_eq_some_iff, Option.some.injEq] at hc
    · subst hc; simp
    · obtain ⟨node, _, rfl⟩ := hc; simp [Constructor.ctorDecl]
  obtain ⟨hf, hv⟩ := placed_split placed hcol ctor (partsOf_kinds hs scope)
  have found : E.ctorDecl scope = ctors.head? := by
    rw [Source.Env.ctorDecl, ← hf, List.head?_filter]
  exact ⟨⟨ctors, hc, found, by rw [Source.Env.ctorFrame, found],
    by simp only [Source.progOf, found]⟩, placed_ordered hs hv⟩

/-! ## Compatibility with the primitive components -/

/-- Where `Constructor.stateParts` succeeds (its roots are all primitive), the
assembly here succeeds with the same parts: roots, flags, initializers, order. -/
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

/-- Conversely, on an all-primitive root list a success here is a success of
`Constructor.stateParts` with the same parts: the common domain is exactly the
primitive lists, and nothing is accepted there that the landed component refuses. -/
theorem stateParts_partsOf (C : Contract) :
    ∀ (vars : List (Name × Ty)) (inits : List (Name × RawExpr))
      (parts : Syn (.list (.part false))),
      partsOf (rootType C el) tr spell vars inits = .ok parts →
      (∀ v ∈ vars, v.2.isPrimitive = true) →
      Constructor.stateParts el tr spell vars inits = some parts
  | [], [], _, h, _ => by cases h; rfl
  | [], _ :: _, _, h, _ => by cases h
  | (x, .ref R) :: _, _, _, _, prim => by cases prim (x, .ref R) List.mem_cons_self
  | (x, .prim p) :: vars, inits, parts, h, prim => by
      obtain ⟨t, init, rest, ht, _, hi, hr, rfl⟩ := partsOf_cons h
      obtain ⟨e, he, rfl⟩ := rootType_prim ht
      have ih := stateParts_partsOf C vars _ rest hr fun v m => prim v (List.mem_cons_of_mem _ m)
      simp only [Constructor.stateParts, he, ih, Option.bind_eq_bind, Option.bind_some]
      rcases initOf_ok hi with ⟨hn, rfl⟩ | ⟨e', s, hn, ht, hs, rfl⟩
      · simp only [hn]; rfl
      · simp only [hn, ht, Bool.false_eq_true, if_false, hs, Option.bind_some]; rfl

/-- Where `TransientDecode.declsT` succeeds, the assembly here without
initializers gives the same declarations, transient flags included. -/
theorem partsOf_declsT (C : Contract) (roots : List Name) :
    ∀ (vars : List (Name × Ty)) (parts : Syn (.list (.part false))),
      TransientDecode.declsT el roots vars = .ok parts →
      partsOf (rootType C el) (fun x => roots.contains x) spell vars [] = .ok parts := by
  intro vars parts h
  induction (TransientDecode.declsT_ok_iff vars parts).mp h with
  | nil => rfl
  | cons he _ ih =>
      rename_i x p e rest ps hf
      have ih := ih ((TransientDecode.declsT_ok_iff rest ps).mpr hf)
      simp only [partsOf, rootType, he, takeInit, initOf, ih, Ty.isPrimitive, Bool.not_true,
        Bool.and_false, Bool.false_eq_true, if_false, bind, Except.bind]
      rfl

/-- Conversely, without initializers and on an all-primitive root list a
success here is a success of `TransientDecode.declsT` with the same parts. -/
theorem declsT_partsOf (C : Contract) (roots : List Name) :
    ∀ (vars : List (Name × Ty)) (parts : Syn (.list (.part false))),
      partsOf (rootType C el) (fun x => roots.contains x) spell vars [] = .ok parts →
      (∀ v ∈ vars, v.2.isPrimitive = true) →
      TransientDecode.declsT el roots vars = .ok parts
  | [], _, h, _ => by cases h; rfl
  | (x, .ref R) :: _, _, _, prim => by cases prim (x, .ref R) List.mem_cons_self
  | (x, .prim p) :: vars, parts, h, prim => by
      obtain ⟨t, init, rest, ht, _, hi, hr, rfl⟩ := partsOf_cons h
      obtain ⟨e, he, rfl⟩ := rootType_prim ht
      cases hi
      have ih := declsT_partsOf C roots vars rest hr fun v m => prim v (List.mem_cons_of_mem _ m)
      exact (TransientDecode.declsT_ok_iff _ _).mpr
        (.cons he ((TransientDecode.declsT_ok_iff _ _).mp ih))

/-- **Compatibility of the contract assemblies.** Where the landed components
succeed, this component gives their parts: `Constructor.declarationParts` (the
constructor, primitive roots and initializers) and, without initializers,
`TransientDecode.decls`. -/
theorem declarationParts_compat {T : Tables} {R : CallSpellExt.Registry}
    {parts : Syn (.list (.part false))} :
    (Constructor.declarationParts T R C = some parts → declarationParts T R C = .ok parts) ∧
    (TransientDecode.decls C = .ok parts → C.inits = [] → state T R C = .ok parts) := by
  refine ⟨fun h => ?_, fun h hi => ?_⟩
  · simp only [Constructor.declarationParts, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨sv, hs, h⟩ := h
    have hs := partsOf_stateParts C _ _ _ hs
    cases hc : C.ctor with
    | none =>
        rw [hc] at h
        simp only [Option.pure_def, Option.some.injEq] at h; subst h
        simp only [declarationParts, state, hs, hc, bind, Except.bind]
    | some d =>
        rw [hc] at h
        simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨node, hn, rfl⟩ := h
        simp only [declarationParts, state, hs, hc, hn, bind, Except.bind]
  · unfold state; rw [hi]
    exact partsOf_declsT C _ _ _ h

/-! ## Transient references -/

/-- **A contract has no transient reference root**: `Contract.transient_ok`
makes every transient root a primitive cell, and `vars_nodup` makes that cell
the root. -/
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

/-- `transientReference` names a reference root marked transient. -/
theorem partsOf_transientReference {ty : Name → Ty → Except Error (Syn .typeName)} {r : Name} :
    ∀ (vars : List (Name × Ty)) (inits : List (Name × RawExpr)),
      partsOf ty tr spell vars inits = .error (.transientReference r) →
      (∀ x T, ty x T ≠ .error (.transientReference r)) →
      ∃ R, (r, .ref R) ∈ vars ∧ tr r = true
  | [], [], h, _ => by cases h
  | [], _ :: _, h, _ => by cases h
  | (x, T) :: vars, inits, h, hty => by
      simp only [partsOf, bind, Except.bind] at h
      split at h
      · rename_i e he; cases h; exact absurd he (hty x T)
      · split at h
        · rename_i hx
          cases h
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx
          cases T with
          | prim p => cases hx.2
          | ref R => exact ⟨R, List.mem_cons_self, hx.1⟩
        · split at h
          · rename_i e he
            cases h
            unfold initOf at he
            split at he
            · cases he
            · split at he
              · cases he
              · split at he <;> cases he
          · split at h
            · rename_i e he
              cases h
              obtain ⟨R, m, t⟩ := partsOf_transientReference vars _ he hty
              exact ⟨R, List.mem_cons_of_mem _ m, t⟩
            · cases h

/-- **The transient-reference failure never occurs on a contract.** -/
theorem state_ne_transientReference (T : Tables) (R : CallSpellExt.Registry) (C : Contract)
    (r : Name) : state T R C ≠ .error (.transientReference r) := by
  intro h
  obtain ⟨R', m, t⟩ := partsOf_transientReference _ _ h (by
    intro x U hU
    cases U with
    | prim p => simp only [rootType] at hU; split at hU <;> cases hU
    | ref R' =>
        simp only [rootType] at hU
        split at hU
        · cases hU
        · split at hU <;> cases hU)
  rw [ref_not_transient C m] at t
  cases t

end Solidity.Correctness.Lowering.Total.ReferenceStateDecode
