import Solidity.Correctness.Lowering.Total.ConstructorDecode

/-!
# Constructor placement in assembled function units

Discharges `Constructor.Placed` for the units `Callee.withFunctions` builds,
and relates the generated state declarations to `TransientDecode.decls`.

* **Placement.** In a successful `withFunctions` assembly, the collected
  table is the contract declaration (file level), the prefix, then the
  translated functions. Each function entry is an ordinary `function`
  (read off `functionParts`, not assumed), so no other constructor or state
  variable of the contract occurs: `Placed` holds for the unit's own
  environment `u.env`. With the generated constructor/state prefix,
  `placed_inits` and `placed_ctor` then hold for `u.env`; `Source.elaborates`
  appears only where `placed_inits` (through `progOf_inits`) requires it.
* **State agreement.** On the common successful domain, the state parts of
  `declarationParts` with their initializers erased (`stripInits`) are
  exactly `TransientDecode.decls`; the ordered `stateViews` (name, declared
  type, transient flag) agree; the initializers, erased by the projection,
  are retained separately by `initsOf`, one per model initializer, in order.

Not claimed here (decoder and composing lanes): complete model-contract
translation, metadata recovery, inherited state, elaboration success and
semantic binding. Each `none` of a component (a reference root, an
unsupported function entry, …) is an open representation gap, not an
accepted-input restriction.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.Constructor

open Source (Syn)
open Callee (withFunctions functionParts fromMetadata)
open TransientDecode (stateView stateViews declsT stateVarDecl)

/-! ## Placement -/

/-- Every declaration collected from the assembled function entries is an
ordinary `function`: the construction admits no constructor or state
variable among them. -/
theorem functionParts_kind {T : Tables} {R : CallSpellExt.Registry} {scope : String}
    {fs : List (Name × FunDecl)} {functions : Syn (.list (.part false))}
    (h : functionParts T R scope fs = some functions) :
    ∀ d ∈ functions.collect (some scope), d.kind = .function := by
  intro d hd
  have hm : some d ∈ fs.map (fun f => fromMetadata T R scope f.2) := by
    rw [← Callee.functionParts_faithful T R scope fs functions h]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨f, _, hf⟩ := List.mem_map.mp hm
  obtain ⟨source, vis, _, _, hfd, _⟩ := Callee.fromMetadata_header hf
  obtain ⟨_, _, _, _, _, _, _, _, he, _⟩ :=
    Callee.functionDecl_faithful T R scope _ _ _ _ d hfd ⟨[]⟩
  rw [he]

/-- **Placement of any prefix.** A successful `withFunctions` assembly places
its prefix in its own environment: the prefix declarations are contiguous,
preceded only by the file-level contract declaration and followed only by
ordinary functions. -/
theorem withFunctions_placed_prefix {T : Tables} {R : CallSpellExt.Registry} {scope : String}
    {leading : Syn (.list (.part false))} {fs : List (Name × FunDecl)} {u : Syn .unit}
    (hu : withFunctions T R scope leading fs = some u) : Placed u.env scope leading := by
  obtain ⟨functions, hf, _, hd⟩ := Callee.withFunctions_declarations hu
  refine ⟨[_], functions.collect (some scope), by show u.decls = _; rw [hd]; rfl, ?_⟩
  · intro d hd' hs
    rcases List.mem_append.mp hd' with h1 | h2
    · rw [List.mem_singleton] at h1; subst h1; cases hs
    · rw [functionParts_kind hf d h2]; exact ⟨nofun, nofun⟩

/-- **Placement of the generated constructor/state parts.** For every
successful assembly whose prefix is `declarationParts`, `Placed` holds for
the unit's environment. -/
theorem withFunctions_placed {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (_ : declarationParts T R C = some parts)
    {scope : String} {fs : List (Name × FunDecl)} {u : Syn .unit}
    (hu : withFunctions T R scope parts fs = some u) : Placed u.env scope parts :=
  withFunctions_placed_prefix hu

/-- **State variables and initializers of the assembled unit**: `placed_inits`
for `u.env`. -/
theorem withFunctions_inits {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (hp : declarationParts T R C = some parts)
    {scope : String} {fs : List (Name × FunDecl)} {u : Syn .unit}
    (hu : withFunctions T R scope parts fs = some u) :
    Ordered (VarSlot (TransientDecode.elemOf C) (fun x => C.transientRoots.contains x) scope)
      C.vars (u.env.stateVarsOf scope) ∧
    (Source.elaborates u.env = true →
      Ordered (fun i (r : Source.RInit u.env) => InitSlot (Calls.expr T R) scope i r.var)
        C.inits ((Source.progOf u.env).inits scope)) :=
  placed_inits hp (withFunctions_placed hp hu)

/-- **The constructor of the assembled unit**: `placed_ctor` for `u.env`,
explicit or implicit. -/
theorem withFunctions_ctor {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (hp : declarationParts T R C = some parts)
    {scope : String} {fs : List (Name × FunDecl)} {u : Syn .unit}
    (hu : withFunctions T R scope parts fs = some u) :
    ∃ ctors, ctorDecls T R scope C.ctor = some ctors ∧ u.env.ctorDecl scope = ctors.head? ∧
      u.env.ctorFrame scope = ctors.head?.bind (·.frame? u.env) ∧
      (Source.progOf u.env).ctor scope =
        ctors.head?.bind fun d => (Source.elabBody u.env d).map Subtype.val :=
  placed_ctor hp (withFunctions_placed hp hu)

/-! ## Agreement with `TransientDecode.decls` -/

/-- A part with its state-variable initializer erased; other parts unchanged. -/
def stripInit : Syn (.part false) → Syn (.part false)
  | .stateVar T v c o t x _ => .stateVar T v c o t x .none
  | p => p

/-- `stripInit` on every part, in order. -/
def stripInits : Syn (.list (.part false)) → Syn (.list (.part false))
  | .nil => .nil
  | .cons d ds => .cons (stripInit d) (stripInits ds)

/-- A state variable's name and initializer, when it has one. -/
def initOf : Syn (.part false) → Option (Name × Syn .expr)
  | .stateVar _ _ _ _ _ x (.some e) => some (x, e)
  | _ => none

/-- The initializers of a part list, in order. -/
def initsOf : Syn (.list (.part false)) → List (Name × Syn .expr)
  | .nil => []
  | .cons d ds => (initOf d).toList ++ initsOf ds

theorem stateView_stripInit (d : Syn (.part false)) : stateView (stripInit d) = stateView d := by
  unfold stripInit; split <;> rfl

/-- Erasing initializers keeps every view: name, declared type, transient flag. -/
theorem stateViews_stripInits :
    ∀ l : Syn (.list (.part false)), stateViews (stripInits l) = stateViews l
  | .nil => by simp only [stripInits, stateViews]
  | .cons d ds => by
      simp only [stripInits, stateViews, stateView_stripInit, stateViews_stripInits ds]

/-- **Projection equality.** When `stateParts` succeeds, `declsT` succeeds on
the same roots, with exactly its parts minus their initializers. -/
theorem stateParts_declsT (el : Name → PrimTy → Option Source.Elem) (roots : List Name)
    (spell : RawExpr → Option (Syn .expr)) :
    ∀ vars inits state, stateParts el (fun x => roots.contains x) spell vars inits = some state →
      declsT el roots vars = .ok (stripInits state)
  | [], [], _, h => by cases h; simp only [declsT, stripInits]
  | [], _ :: _, _, h => by cases h
  | (_, .ref _) :: _, _, _, h => by cases h
  | (x, .prim p) :: vars, inits, state, h => by
      simp only [stateParts, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨elem, he, rest, hr, h⟩ := h
      have ih := stateParts_declsT el roots spell vars _ rest hr
      have hd : TransientDecode.declT el roots (x, .prim p) = .ok (stateVarDecl elem (roots.contains x) x) := by
        simp only [TransientDecode.declT, he]
      split at h
      · cases h
        simp only [declsT, hd, ih, stripInits, stripInit, stateVarDecl]
      · split at h
        · cases h
        · rename_i ht
          simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨t, _, rfl⟩ := h
          have ht : roots.contains x = false := by simpa using ht
          simp only [declsT, hd, ih, stripInits, stripInit, stateVarDecl, ht]

/-- **Initializers retained.** The spelled initializers of the state parts are
the model's, one each and in order, each on its target root. -/
theorem stateParts_initsOf (el : Name → PrimTy → Option Source.Elem) (tr : Name → Bool)
    (spell : RawExpr → Option (Syn .expr)) :
    ∀ vars inits state, stateParts el tr spell vars inits = some state →
      Ordered (fun (i : Name × RawExpr) (j : Name × Syn .expr) => j.1 = i.1 ∧ spell i.2 = some j.2)
        inits (initsOf state)
  | [], [], _, h => by cases h; simp only [initsOf]; exact .nil
  | [], _ :: _, _, h => by cases h
  | (_, .ref _) :: _, _, _, h => by cases h
  | (x, .prim p) :: vars, inits, state, h => by
      simp only [stateParts, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨elem, _, rest, hr, h⟩ := h
      have ih := stateParts_initsOf el tr spell vars _ rest hr
      split at h
      · rename_i hn
        cases h
        have same : (takeInit x inits).2 = inits := by
          cases inits with
          | nil => rfl
          | cons i inits =>
              simp only [takeInit] at hn ⊢
              split <;> rename_i hxy
              · rw [if_pos hxy] at hn; cases hn
              · rfl
        rw [same] at ih
        simpa [initsOf, initOf] using ih
      · rename_i e hn
        split at h
        · cases h
        · simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨t, hs, rfl⟩ := h
          cases inits with
          | nil => cases hn
          | cons i inits =>
              obtain ⟨y, e'⟩ := i
              simp only [takeInit] at hn ih
              split at hn <;> cases hn
              rename_i hxy
              subst hxy
              simp only [if_true] at ih
              simp only [initsOf, initOf, Option.toList, List.singleton_append]
              exact .cons ⟨rfl, hs⟩ ih

/-- **Agreement on the common successful domain.** When `declarationParts`
succeeds, so does `TransientDecode.decls`, on exactly the state parts with
their initializers erased; the ordered views (names, declared types,
transient flags) agree, behind the explicit constructor's `none` view, if
any; and the erased initializers are the model's, in order. -/
theorem declarationParts_decls {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (hp : declarationParts T R C = some parts) :
    ∃ state tparts,
      stateParts (TransientDecode.elemOf C) (fun x => C.transientRoots.contains x)
        (Calls.expr T R) C.vars C.inits = some state ∧
      TransientDecode.decls C = .ok tparts ∧ tparts = stripInits state ∧
      stateViews state = stateViews tparts ∧
      stateViews parts = (C.ctor.map fun _ => none).toList ++ stateViews tparts ∧
      Ordered (fun (i : Name × RawExpr) (j : Name × Syn .expr) =>
          j.1 = i.1 ∧ Calls.expr T R i.2 = some j.2) C.inits (initsOf state) := by
  simp only [declarationParts, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨state, hs, hp⟩ := hp
  have hd := stateParts_declsT _ _ _ _ _ _ hs
  have hv : stateViews state = stateViews (stripInits state) := (stateViews_stripInits state).symm
  refine ⟨state, _, hs, hd, rfl, hv, ?_, stateParts_initsOf _ _ _ _ _ _ hs⟩
  cases hc : C.ctor with
  | none =>
      rw [hc] at hp
      simp only [Option.pure_def, Option.some.injEq] at hp; subst hp
      simp [hv]
  | some d =>
      rw [hc] at hp
      simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at hp
      obtain ⟨node, hn, rfl⟩ := hp
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ :=
        constructorPart_faithful hn "" ⟨[]⟩
      simp [stateViews, stateView, hv]

/-- The state variables of the assembled unit's contract are the collected
state parts, in order: no constructor, function or other declaration enters. -/
theorem withFunctions_stateVarsOf {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (hp : declarationParts T R C = some parts)
    {scope : String} {fs : List (Name × FunDecl)} {u : Syn .unit}
    (hu : withFunctions T R scope parts fs = some u) :
    ∃ state,
      stateParts (TransientDecode.elemOf C) (fun x => C.transientRoots.contains x)
        (Calls.expr T R) C.vars C.inits = some state ∧
      u.env.stateVarsOf scope = state.collect (some scope) := by
  obtain ⟨functions, hf, _, hd⟩ := Callee.withFunctions_declarations hu
  obtain ⟨state, ctors, hs, hc, hcol⟩ := declarationParts_collect hp scope
  refine ⟨state, hs, ?_⟩
  have vars : ∀ d ∈ state.collect (some scope),
      d.kind = .stateVar ∧ d.scope = some scope ∧ d.isConst = false := by
    have hv := (stateParts_faithful _ _ _ scope _ _ _ hs).1
    generalize state.collect (some scope) = ds at hv
    generalize C.vars = vs at hv
    induction hv with
    | nil => intro d hd; cases hd
    | cons hv _ ih =>
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · obtain ⟨_, _, _, _, _, rfl⟩ := hv
          exact ⟨rfl, rfl, rfl⟩
        · exact ih d hd
  have ctor : ∀ d ∈ ctors, d.kind = .constructor := by
    cases hctor : C.ctor <;> rw [hctor] at hc <;>
      simp only [ctorDecls, Option.map_eq_some_iff, Option.some.injEq] at hc
    · subst hc; simp
    · obtain ⟨node, _, rfl⟩ := hc; simp [ctorDecl]
  have fn := functionParts_kind hf
  show u.decls.filter _ = _
  rw [hd, hcol, List.filter_cons, List.filter_append, List.filter_append,
    List.filter_eq_nil_iff.mpr (fun d hd => by simp [ctor d hd]),
    List.filter_eq_self.mpr (fun d hd => by simp [vars d hd]),
    List.filter_eq_nil_iff.mpr (fun d hd => by simp [fn d hd])]
  simp

/-- **Agreement in the assembled unit.** The unit's state variables of
`scope` are the collected state parts; erasing their initializers gives
`TransientDecode.decls` exactly, with the same ordered views; and the
erased initializers are the model's, in order. -/
theorem withFunctions_decls {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (hp : declarationParts T R C = some parts)
    {scope : String} {fs : List (Name × FunDecl)} {u : Syn .unit}
    (hu : withFunctions T R scope parts fs = some u) :
    ∃ state tparts,
      u.env.stateVarsOf scope = state.collect (some scope) ∧
      TransientDecode.decls C = .ok tparts ∧ tparts = stripInits state ∧
      stateViews state = stateViews tparts ∧
      Ordered (fun (i : Name × RawExpr) (j : Name × Syn .expr) =>
          j.1 = i.1 ∧ Calls.expr T R i.2 = some j.2) C.inits (initsOf state) := by
  obtain ⟨state, tparts, hs, hd, ht, hv, _, hi⟩ := declarationParts_decls hp
  obtain ⟨state', hs', hsv⟩ := withFunctions_stateVarsOf hp hu
  rw [hs] at hs'; cases hs'
  exact ⟨state, tparts, hsv, hd, ht, hv, hi⟩

end Solidity.Correctness.Lowering.Total.Decode.Constructor
