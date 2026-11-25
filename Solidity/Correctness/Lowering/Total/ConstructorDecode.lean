import Solidity.Correctness.Lowering.Total.Decode.Callee.Units
import Solidity.Source.Elaborate

/-!
# Constructor and state-initializer declaration components

Reads `Contract.ctor`, `Contract.inits`, `Contract.vars` and the retained
constructor header (`FunDecl.sourceDecl`), and spells actual Source syntax: one
state variable per storage root, carrying its original initializer, after the
explicit constructor when the contract declares one. Parameters, modifier
invocations and expression/body spelling are the landed callee components.

Proved here are declaration-level facts only: what is spelled, in which order,
which Source frame and declared types result, and what a successful
`Source.elabInit` says about each spelled initializer. Nothing here states
that the Source deployment and the model's `elabCtor` program execute alike.

Unsupported inputs return `none` (a reference root or parameter, a
constructor without a retained constructor header, constructor returns,
initializers out of root order or naming no root). These are implementation
gaps of this component, not admission conditions.

Left for the composing lane (`Obligations`, and the prose at its docstring):
placement in the complete unit, unit elaboration, modifier resolution,
retained-metadata agreement, and all execution correspondence, including that
initializers run before the constructor body.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.Constructor

open Source (Syn STy)
open Callee (parameters Slots modifiers ModifierSpelling)

/-- Two lists related entry by entry, in order: equal lengths, nothing
dropped, added or moved. -/
inductive Ordered {α β : Type} (r : α → β → Prop) : List α → List β → Prop where
  | nil : Ordered r [] []
  | cons {a b as bs} : r a b → Ordered r as bs → Ordered r (a :: as) (b :: bs)

/-! ## The constructor -/

/-- Payable status of a retained constructor header. A header of another
role, and a `pure`/`view` one (which no constructor has), give nothing: the
model's separate `FunDecl.payable` flag is not consulted. -/
def payable? (s : SourceFunction) : Option Bool :=
  match s.callable, s.mutability with
  | .constructor, .nonpayable => some false
  | .constructor, .payable => some true
  | _, _ => none

/-- The constructor's syntax: original parameters at the declaration's own
width table, original modifier applications in order, payable status from the
retained header and the original body spelling. No visibility token is
written: none is retained. -/
def constructorPart (T : Tables) (R : CallSpellExt.Registry) (d : FunDecl) :
    Option (Syn (.part false)) := do
  let source ← d.sourceDecl
  let pay ← payable? source
  match d.rets with
  | [] =>
    let ps ← parameters d.widths d.params
    let ms ← modifiers T R d.mods
    let body ← Tables.WithExpr.items T (Calls.expr T R) .body d.body
    pure (.constructor ps ms pay none (.block body))
  | _ :: _ => none

/-- The declaration Source collects for a constructor written in `scope`. -/
def ctorDecl (scope : String) (node : Syn (.part false)) : Source.Decl :=
  ⟨.constructor, "", some scope, false, node⟩

/-- The constructor declaration of contract `scope`. -/
def constructorDecl (T : Tables) (R : CallSpellExt.Registry) (scope : String) (d : FunDecl) :
    Option Source.Decl :=
  (constructorPart T R d).map (ctorDecl scope)

/-- The written invocations, each an original modifier application: its name
as a one-component path and its arguments as spelled, in order. The list has
no other entry, so nothing written here is a base-constructor argument list
of the model's making. -/
theorem modifiers_invList {T : Tables} {R : CallSpellExt.Registry}
    {mods : List ModApp} {ms : Syn (.list .modInv)} (h : ModifierSpelling T R mods ms) :
      Ordered (fun (m : ModApp) (inv : Source.IdPath × Syn (.opt .callArgs)) =>
        inv.1 = ⟨m.name, []⟩ ∧
        ∃ args, inv.2 = .some (.positional args) ∧ CallSpellExt.ExprsX T R m.args args)
        mods ms.invList := by
  induction h with
  | nil => simp only [Source.Syn.invList]; exact .nil
  | cons ha _ ih => simp only [Source.Syn.invList]; exact .cons ⟨rfl, _, rfl, ha⟩ ih

/-- **Successful constructor assembly.** The declaration is exactly the
constructor of the original parameters, modifier applications and body; its
payable flag is the retained header's; and its actual Source frame has the
original parameter names in order, table-corresponding parameter types, no
return slot, the spelled body and `msg.value` readable exactly when payable.
No execution agreement follows from this. -/
theorem constructorDecl_faithful (T : Tables) (R : CallSpellExt.Registry) (scope : String)
    (d : FunDecl) (out : Source.Decl) (h : constructorDecl T R scope d = some out)
    (E : Source.Env) :
    ∃ source pay ps ms body f,
      d.sourceDecl = some source ∧ source.callable = .constructor ∧
      payable? source = some pay ∧ (pay = true ↔ source.mutability = .payable) ∧
      d.rets = [] ∧
      parameters d.widths d.params = some ps ∧ ModifierSpelling T R d.mods ms ∧
      Tables.WithExpr.items T (Calls.expr T R) .body d.body = some body ∧
      out = ctorDecl scope (.constructor ps ms pay none (.block body)) ∧
      out.modInvs = ms ∧
      out.frame? E = some f ∧
      f.names = d.params.map (fun p => some p.1) ∧ f.rnames = [] ∧
      Slots d.widths d.params f.ps ∧ f.rs = [] ∧
      f.body = body ∧ f.msgValue = pay ∧ f.inModifier = false := by
  simp only [constructorDecl, constructorPart, Option.bind_eq_bind, Option.pure_def,
    Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
  obtain ⟨node, ⟨source, hs, pay, hp, h⟩, rfl⟩ := h
  split at h
  · rename_i hr
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ps, hps, ms, hms, body, hb, rfl⟩ := h
    obtain ⟨names, τs, typed, slots⟩ :=
      Callee.parameters_faithful d.widths E (some scope) _ _ hps
    have role : source.callable = .constructor ∧ (pay = true ↔ source.mutability = .payable) := by
      unfold payable? at hp
      split at hp <;> first
        | (cases hp; rename_i hc hm; exact ⟨hc, by simp [hm]⟩)
        | cases hp
    refine ⟨source, pay, ps, ms, body, ⟨ps.paramNames, τs, [], [], body, pay, false⟩,
      hs, role.1, hp, role.2, hr, hps, Callee.modifiers_spelled T R _ _ hms, hb, rfl, rfl, ?_,
      names, rfl, slots, rfl, rfl, rfl, rfl⟩
    simp [ctorDecl, Source.Decl.frame?, Source.Frame.mk?, typed, Source.Syn.tys,
      Source.Syn.paramNames]
  · cases h

/-! ### Modifier invocations and base-constructor arguments

Source reads a constructor's invocation list twice: a name that resolves to a
modifier is a modifier invocation; one that does not, but names a contract, is
skipped by `Source.elabMods` and read as base-constructor arguments. The model
has modifier applications only, so every spelled invocation must resolve as a
modifier. That resolution depends on the whole unit and is an obligation. -/

/-- Every written invocation names a modifier of the unit. -/
def ModifiersResolve (E : Source.Env) (scope : Option String) (ms : Syn (.list .modInv)) : Prop :=
  ∀ inv ∈ ms.invList, (E.modifierAt scope inv.1).isSome = true

/-- When every invocation resolves as a modifier, successful Source
elaboration keeps each one, in order, as that modifier: none is skipped as a
base-constructor argument list. -/
theorem elabMods_resolved (E : Source.Env) (d : Source.Decl) (f : Source.Frame) :
    ∀ (invs : List (Source.IdPath × Syn (.opt .callArgs))) ms,
      Source.elabMods E d f invs = some ms →
      (∀ inv ∈ invs, (E.modifierAt d.scope inv.1).isSome = true) →
      Ordered (fun (m : Source.RModInv E (Source.tysOf f.locals))
          (inv : Source.IdPath × Syn (.opt .callArgs)) =>
        E.modifierAt d.scope inv.1 = some (m.modifier, m.ps)) ms.val invs
  | [], ms, h, _ => by
      simp only [Source.elabMods, Option.some.injEq] at h
      subst h
      exact .nil
  | (p, args) :: rest, ms, h, hres => by
      simp only [Source.elabMods, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨ms', hms'⟩, hrest, h⟩ := h
      have ih := elabMods_resolved E d f rest _ hrest
        (fun inv hi => hres inv (List.mem_cons_of_mem _ hi))
      have hp := hres (p, args) List.mem_cons_self
      split at h
      · split at h
        · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
          obtain ⟨⟨a, ha⟩, _, rfl⟩ := h
          exact .cons (by assumption) ih
        · cases h
      · rename_i hm
        rw [hm] at hp
        cases hp

/-! ## State variables and their initializers -/

/-- The syntax of one primitive state variable. No visibility, constness or
override is written: none is retained. -/
def varPart (elem : Source.Elem) (transient : Bool) (x : Name) (init : Syn (.opt .expr)) :
    Syn (.part false) :=
  .stateVar (.elem elem) none none none transient x init

/-- The declaration Source collects for that state variable in `scope`. -/
def varDecl (scope : String) (elem : Source.Elem) (transient : Bool) (x : Name)
    (init : Syn (.opt .expr)) : Source.Decl :=
  ⟨.stateVar, x, some scope, false, varPart elem transient x init⟩

/-- The initializer of the root `x`, when it is the next one pending. -/
def takeInit (x : Name) : List (Name × RawExpr) → Option RawExpr × List (Name × RawExpr)
  | (y, e) :: rest => if x = y then (some e, rest) else (none, (y, e) :: rest)
  | [] => (none, [])

/-- An initializer as written, or none. -/
def spellInit (spell : RawExpr → Option (Syn .expr)) : Option RawExpr → Option (Syn (.opt .expr))
  | none => some .none
  | some e => (spell e).map .some

/-- The state variables in root order, each with its pending initializer.
Initializers are consumed in their own order, so the construction succeeds
only when that order is the root order and every initializer names a root:
none is dropped, moved or attached to another variable. -/
def stateParts (el : Name → PrimTy → Option Source.Elem) (tr : Name → Bool)
    (spell : RawExpr → Option (Syn .expr)) :
    List (Name × Ty) → List (Name × RawExpr) → Option (Syn (.list (.part false)))
  | [], [] => some .nil
  | [], _ :: _ => none
  | (x, .prim p) :: vars, inits => do
      let elem ← el x p
      let init ← spellInit spell (takeInit x inits).1
      pure (.cons (varPart elem (tr x) x init) (← stateParts el tr spell vars (takeInit x inits).2))
  | (_, .ref _) :: _, _ => none

/-- One root and its Source declaration: the same name, a mutable state
variable of `scope`, declared at the table's elementary type. -/
def VarSlot (el : Name → PrimTy → Option Source.Elem) (tr : Name → Bool) (scope : String)
    (v : Name × Ty) (d : Source.Decl) : Prop :=
  ∃ p elem init, v.2 = .prim p ∧ el v.1 p = some elem ∧
    d = varDecl scope elem (tr v.1) v.1 init

/-- One model initializer and its Source declaration: the target root and
the original expression as spelled. -/
def InitSlot (spell : RawExpr → Option (Syn .expr)) (i : Name × RawExpr) (d : Source.Decl) : Prop :=
  d.name = i.1 ∧ ∃ t, spell i.2 = some t ∧ d.init? = some t

theorem varDecl_facts (scope : String) (elem : Source.Elem) (transient : Bool) (x : Name)
    (init : Syn (.opt .expr)) (E : Source.Env) :
    let d := varDecl scope elem transient x init
    d.kind = .stateVar ∧ d.name = x ∧ d.scope = some scope ∧ d.isConst = false ∧
      d.varTy E = some (elem.ty .storage) ∧
      (init = .none → d.init? = none) ∧ (∀ t, init = .some t → d.init? = some t) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [varDecl, varPart, Source.Decl.varTy, Source.Syn.ty, Source.Syn.tys]
  · rintro rfl; rfl
  · rintro t rfl; rfl

/-- **Roots are preserved**: the collected declarations are the roots, one
each and in order, at the table's types. -/
theorem stateParts_vars (el : Name → PrimTy → Option Source.Elem) (tr : Name → Bool)
    (spell : RawExpr → Option (Syn .expr)) (scope : String) :
    ∀ vars inits parts, stateParts el tr spell vars inits = some parts →
      Ordered (VarSlot el tr scope) vars (parts.collect (some scope))
  | [], [], _, h => by cases h; exact .nil
  | [], _ :: _, _, h => by cases h
  | (x, .ref _) :: _, _, _, h => by cases h
  | (x, .prim p) :: vars, inits, parts, h => by
      simp only [stateParts, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨elem, he, init, _, rest, hr, rfl⟩ := h
      rw [Source.Syn.collect]
      exact .cons ⟨p, elem, init, rfl, he, rfl⟩ (stateParts_vars el tr spell scope vars _ rest hr)

/-- **Initializers are preserved**: the declarations that carry an
initializer are the model's initializers, one each and in order, each on its
target root with its original expression as spelled. -/
theorem stateParts_inits (el : Name → PrimTy → Option Source.Elem) (tr : Name → Bool)
    (spell : RawExpr → Option (Syn .expr)) (scope : String) :
    ∀ vars inits parts, stateParts el tr spell vars inits = some parts →
      Ordered (InitSlot spell) inits
        ((parts.collect (some scope)).filter fun d => d.init?.isSome)
  | [], [], _, h => by cases h; exact .nil
  | [], _ :: _, _, h => by cases h
  | (x, .ref _) :: _, _, _, h => by cases h
  | (x, .prim p) :: vars, inits, parts, h => by
      simp only [stateParts, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨elem, he, init, hi, rest, hr, rfl⟩ := h
      have ih := stateParts_inits el tr spell scope vars _ rest hr
      rw [Source.Syn.collect]
      cases inits with
      | nil =>
          simp only [takeInit, spellInit, Option.some.injEq] at hi
          subst hi
          simpa [varPart, Source.Syn.collect, Source.Decl.init?] using ih
      | cons i inits =>
          obtain ⟨y, e⟩ := i
          by_cases hxy : x = y
          · subst hxy
            simp only [takeInit, if_true, spellInit, Option.map_eq_some_iff] at hi ih
            obtain ⟨t, ht, rfl⟩ := hi
            have : (varPart elem (tr x) x (.some t)).collect (some scope) =
                [varDecl scope elem (tr x) x (.some t)] := rfl
            rw [this]
            simp only [List.singleton_append, List.filter_cons]
            have keep : (varDecl scope elem (tr x) x (.some t)).init?.isSome = true := rfl
            rw [if_pos keep]
            exact .cons ⟨rfl, t, ht, rfl⟩ ih
          · simp only [takeInit, if_neg hxy, spellInit, Option.some.injEq] at hi ih
            subst hi
            simpa [varPart, Source.Syn.collect, Source.Decl.init?] using ih

/-! ### What `Source.elabInit` says about a spelled initializer -/

/-- A declaration without an initializer has no elaborated initializer. -/
theorem elabInit_none {E : Source.Env} {d : Source.Decl} (h : d.init? = none) :
    Source.elabInit E d = none := by
  unfold Source.elabInit
  split
  · rename_i _ _ he _
    rw [h] at he
    cases he
  · rfl

/-- **A successful `Source.elabInit`**, read off its result: the initializer
belongs to the declaration, its type `τ` is the declaration's declared type,
the written expression `e` has an inferred type `σ` under the initializer
context, `σ` converts implicitly to `τ`, and the resolved expression is that
derivation's under exactly that conversion. -/
theorem elabInit_typed {E : Source.Env} {d : Source.Decl}
    {i : {i : Source.RInit E // i.var = d ∧ Source.RInit.Derived E i}}
    (h : Source.elabInit E d = some i) :
    i.val.var = d ∧ d.varTy E = some i.val.τ ∧
    ∃ (e : Syn .expr) (σ : STy)
      (D : Source.Typed (Source.Ctx.forInit E i.val.var.scope) e σ)
      (c : σ.implicit E.isBase E.mapFree i.val.τ = true),
      d.init? = some e ∧ i.val.e = .conv D.toR (.inl c) := by
  obtain ⟨⟨var, τ, hτ, r⟩, hv, e, σ, D, c, he, hr⟩ := i
  cases hv
  exact ⟨rfl, hτ, e, σ, D, c, he, hr⟩

/-- **A spelled initializer, elaborated.** For the state variable of a root
with initializer `t`, a successful `Source.elabInit` has converted type the
root's table type in storage, and its expression is a typing derivation of
`t` itself, converted from the inferred type. Whether elaboration succeeds,
and what `t` evaluates to, are not claimed. -/
theorem varDecl_elabInit {E : Source.Env} {scope : String} {elem : Source.Elem} {transient : Bool}
    {x : Name} {t : Syn .expr}
    {i : {i : Source.RInit E //
      i.var = varDecl scope elem transient x (.some t) ∧ Source.RInit.Derived E i}}
    (h : Source.elabInit E (varDecl scope elem transient x (.some t)) = some i) :
    i.val.τ = elem.ty .storage ∧
    ∃ (σ : STy) (D : Source.Typed (Source.Ctx.forInit E i.val.var.scope) t σ)
      (c : σ.implicit E.isBase E.mapFree i.val.τ = true),
      i.val.e = .conv D.toR (.inl c) := by
  obtain ⟨_, hτ, e, σ, D, c, he, hr⟩ := elabInit_typed h
  have hty := (varDecl_facts scope elem transient x (.some t) E).2.2.2.2.1
  rw [hty] at hτ
  have het : some t = some e := he
  cases het
  exact ⟨(Option.some.inj hτ).symm, σ, D, c, hr⟩

/-- **The elaborated program keeps declaration order**: when the unit
elaborates, a contract's initializers in the Source program are exactly its
non-constant state variables that carry an initializer, in declaration order. -/
theorem progOf_inits (E : Source.Env) (c : String) (hE : Source.elaborates E = true) :
    ((Source.progOf E).inits c).map (fun i => i.var) =
      (E.stateVarsOf c).filter fun d => d.init?.isSome := by
  have all : ∀ d ∈ E.decls, d.init?.isSome = true → (Source.elabInit E d).isSome = true := by
    intro d hd hi
    simp only [Source.elaborates, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hE
    rcases hE.1.2 d hd with hn | hs
    · rw [Option.isNone_iff_eq_none] at hn
      rw [hn] at hi
      cases hi
    · exact hs
  have sub : ∀ l : List Source.Decl, (∀ d ∈ l, d ∈ E.decls) →
      (l.filterMap fun d => (Source.elabInit E d).map Subtype.val).map (fun i => i.var) =
        l.filter fun d => d.init?.isSome := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons d l ih =>
        intro hl
        have ih := ih fun d hd => hl d (List.mem_cons_of_mem _ hd)
        cases hi : d.init? with
        | none =>
            simp only [List.filterMap_cons, elabInit_none hi, Option.map_none, List.filter_cons,
              hi, Option.isSome_none, Bool.false_eq_true, if_false]
            exact ih
        | some t =>
            have ok := all d (hl d List.mem_cons_self) (by rw [hi]; rfl)
            obtain ⟨i, hi'⟩ := Option.isSome_iff_exists.mp ok
            simp only [List.filterMap_cons, hi', Option.map_some, List.map_cons, List.filter_cons,
              hi, Option.isSome_some, if_true, ih, i.property.1]
  exact sub _ fun d hd => (List.mem_filter.mp hd).1

/-! ## Contract declaration parts -/

/-- The declaration parts this component owns: the explicit constructor if
there is one, then every root as a state variable with its initializer. A
contract without a constructor gets no constructor part: Source's implicit
constructor is the absence of the declaration, not an empty one. The model
does not retain where the constructor stood among the members, and Source
reads neither it nor the state variables by position relative to the other. -/
def declarationParts (T : Tables) (R : CallSpellExt.Registry) (C : Contract) :
    Option (Syn (.list (.part false))) := do
  let state ← stateParts (elemB C.widths) (fun x => C.transientRoots.contains x)
    (Calls.expr T R) C.vars C.inits
  match C.ctor with
  | none => pure state
  | some d => pure (.cons (← constructorPart T R d) state)

/-- The constructor declarations of an optional model constructor. -/
def ctorDecls (T : Tables) (R : CallSpellExt.Registry) (scope : String) :
    Option FunDecl → Option (List Source.Decl)
  | none => some []
  | some d => (constructorDecl T R scope d).map ([·])

/-- **Declaration assembly.** The collected declarations are the constructor
declaration, exactly one for an explicit constructor and none for the
implicit one, followed by the state variables in root order. -/
theorem declarationParts_collect {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (h : declarationParts T R C = some parts) (scope : String) :
    ∃ state ctors,
      stateParts (elemB C.widths) (fun x => C.transientRoots.contains x) (Calls.expr T R)
        C.vars C.inits = some state ∧
      ctorDecls T R scope C.ctor = some ctors ∧
      parts.collect (some scope) = ctors ++ state.collect (some scope) := by
  simp only [declarationParts, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨state, hs, h⟩ := h
  cases hc : C.ctor with
  | none =>
      rw [hc] at h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨state, [], hs, rfl, rfl⟩
  | some d =>
      rw [hc] at h
      simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨node, hn, rfl⟩ := h
      refine ⟨state, [ctorDecl scope node], hs, ?_, ?_⟩
      · simp [ctorDecls, constructorDecl, hn]
      · rw [Source.Syn.collect]
        simp only [constructorPart, Option.bind_eq_bind, Option.bind_eq_some_iff] at hn
        obtain ⟨_, _, _, _, hn⟩ := hn
        split at hn
        · simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at hn
          obtain ⟨_, _, _, _, _, _, rfl⟩ := hn
          rfl
        · cases hn

/-! ## Placement in a unit

The complete unit is composed elsewhere. `Placed` is what these facts need of
it: the parts occur contiguously among the unit's declarations, and nothing
else in the unit is a constructor or state variable of the same contract. -/

/-- The parts' declarations sit in `E`, and are all of contract `scope`'s
constructors and state variables. -/
def Placed (E : Source.Env) (scope : String) (parts : Syn (.list (.part false))) : Prop :=
  ∃ before after, E.decls = before ++ parts.collect (some scope) ++ after ∧
    ∀ d ∈ before ++ after, d.scope = some scope → d.kind ≠ .constructor ∧ d.kind ≠ .stateVar

private theorem filter_outside {scope : String} {q : Source.Decl → Bool} {l : List Source.Decl}
    (out : ∀ d ∈ l, d.scope = some scope → d.kind ≠ .constructor ∧ d.kind ≠ .stateVar)
    (hq : ∀ d, q d = true → d.scope = some scope ∧ (d.kind = .constructor ∨ d.kind = .stateVar)) :
    l.filter q = [] := by
  rw [List.filter_eq_nil_iff]
  intro d hd hqd
  obtain ⟨hs, hk⟩ := hq d hqd
  obtain ⟨h1, h2⟩ := out d hd hs
  rcases hk with hk | hk
  · exact h1 hk
  · exact h2 hk

private theorem placed_filter {E : Source.Env} {scope : String} {parts : Syn (.list (.part false))}
    (h : Placed E scope parts) (q : Source.Decl → Bool)
    (hq : ∀ d, q d = true → d.scope = some scope ∧ (d.kind = .constructor ∨ d.kind = .stateVar)) :
    E.decls.filter q = (parts.collect (some scope)).filter q := by
  obtain ⟨before, after, hd, out⟩ := h
  rw [hd, List.filter_append, List.filter_append,
    filter_outside (fun d hd => out d (List.mem_append_left _ hd)) hq,
    filter_outside (fun d hd => out d (List.mem_append_right _ hd)) hq,
    List.nil_append, List.append_nil]

private theorem state_kinds {el : Name → PrimTy → Option Source.Elem} {tr : Name → Bool}
    {scope : String} {vars : List (Name × Ty)} {ds : List Source.Decl}
    (h : Ordered (VarSlot el tr scope) vars ds) :
    ∀ d ∈ ds, d.kind = .stateVar ∧ d.scope = some scope ∧ d.isConst = false := by
  induction h with
  | nil => intro d hd; cases hd
  | cons hv _ ih =>
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · obtain ⟨_, _, _, _, _, rfl⟩ := hv
        exact ⟨rfl, rfl, rfl⟩
      · exact ih d hd

/-- **Placed state variables.** In a unit that places the parts, contract
`scope`'s non-constant state variables are the roots' declarations in root
order, and those with an initializer are the model's initializers in order. -/
theorem placed_stateVars {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (h : declarationParts T R C = some parts)
    {E : Source.Env} {scope : String} (placed : Placed E scope parts) :
    Ordered (VarSlot (elemB C.widths) (fun x => C.transientRoots.contains x) scope)
      C.vars (E.stateVarsOf scope) ∧
    Ordered (InitSlot (Calls.expr T R)) C.inits
      ((E.stateVarsOf scope).filter fun d => d.init?.isSome) := by
  obtain ⟨state, ctors, hs, hc, hcol⟩ := declarationParts_collect h scope
  have vars := stateParts_vars _ _ _ scope _ _ _ hs
  have inits := stateParts_inits _ _ _ scope _ _ _ hs
  have kinds := state_kinds vars
  have same : E.stateVarsOf scope = state.collect (some scope) := by
    unfold Source.Env.stateVarsOf
    rw [placed_filter placed _ (by
      intro d hd
      simp only [Bool.and_eq_true, beq_iff_eq] at hd
      exact ⟨hd.1.2, .inr hd.1.1⟩), hcol, List.filter_append]
    have keep : (state.collect (some scope)).filter (fun d =>
        d.kind == .stateVar && d.scope == some scope && !d.isConst) = state.collect (some scope) := by
      rw [List.filter_eq_self]
      intro d hd
      obtain ⟨hk, hsc, hcn⟩ := kinds d hd
      simp [hk, hsc, hcn]
    have drop : ctors.filter (fun d =>
        d.kind == .stateVar && d.scope == some scope && !d.isConst) = [] := by
      cases hctor : C.ctor with
      | none => rw [hctor] at hc; cases hc; rfl
      | some d =>
          rw [hctor] at hc
          simp only [ctorDecls, constructorDecl, Option.map_eq_some_iff] at hc
          obtain ⟨_, ⟨node, _, rfl⟩, rfl⟩ := hc
          rfl
    rw [keep, drop, List.nil_append]
  rw [same]
  exact ⟨vars, inits⟩

/-- **Initializers of the elaborated program.** In an elaborating unit that
places the parts, the Source program's initializers of `scope` are the model's
initializers, one each and in order: each belongs to the state variable of
its target root, and is the spelled original expression. -/
theorem placed_inits {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (h : declarationParts T R C = some parts)
    {E : Source.Env} {scope : String} (placed : Placed E scope parts)
    (hE : Source.elaborates E = true) :
    Ordered (fun (i : Name × RawExpr) (r : Source.RInit E) => InitSlot (Calls.expr T R) i r.var)
      C.inits ((Source.progOf E).inits scope) := by
  have order := progOf_inits E scope hE
  have inits := (placed_stateVars h placed).2
  rw [← order] at inits
  generalize (Source.progOf E).inits scope = rs at inits
  generalize C.inits = is at inits
  induction rs generalizing is with
  | nil => cases inits; exact .nil
  | cons r rs ih =>
      cases inits with
      | cons hd tl => exact .cons hd (ih _ tl)

/-- **The implicit constructor.** A contract that declares no constructor
has no constructor declaration in a unit that places its parts: Source's
program has no constructor body for it and its deployment is not payable. -/
theorem placed_implicit {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (h : declarationParts T R C = some parts)
    (hc : C.ctor = none) {E : Source.Env} {scope : String} (placed : Placed E scope parts) :
    E.ctorDecl scope = none ∧ E.ctorFrame scope = none ∧
    (Source.progOf E).ctor scope = none ∧ E.ctorPayable scope = false := by
  obtain ⟨state, ctors, hs, hcs, hcol⟩ := declarationParts_collect h scope
  rw [hc] at hcs
  cases hcs
  have kinds := state_kinds (stateParts_vars _ _ _ scope _ _ _ hs)
  have none : E.ctorDecl scope = none := by
    unfold Source.Env.ctorDecl
    rw [List.find?_eq_none]
    intro d hd hq
    have hf : d ∈ E.decls.filter fun d => d.kind == .constructor && d.scope == some scope :=
      List.mem_filter.mpr ⟨hd, hq⟩
    rw [placed_filter placed _ (by
      intro d hd
      simp only [Bool.and_eq_true, beq_iff_eq] at hd
      exact ⟨hd.2, .inl hd.1⟩), hcol, List.nil_append] at hf
    obtain ⟨hm, hq'⟩ := List.mem_filter.mp hf
    have hk := (kinds d hm).1
    simp [hk] at hq'
  refine ⟨none, ?_, ?_, ?_⟩
  · simp [Source.Env.ctorFrame, none]
  · simp [Source.progOf, none]
  · simp [Source.Env.ctorPayable, none]

/-- **The explicit constructor.** In a unit that places the parts, the
constructor Source finds for `scope` is the assembled declaration, its
constructor frame is that declaration's frame, the program's constructor body
is the elaboration of that declaration alone, and deployment is payable
exactly as the retained header says. Initializers are not part of that body. -/
theorem placed_explicit {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (h : declarationParts T R C = some parts)
    {d : FunDecl} (hc : C.ctor = some d) {E : Source.Env} {scope : String}
    (placed : Placed E scope parts) :
    ∃ out, constructorDecl T R scope d = some out ∧
      E.ctorDecl scope = some out ∧ E.ctorFrame scope = out.frame? E ∧
      (Source.progOf E).ctor scope = (Source.elabBody E out).map Subtype.val ∧
      payable? <$> d.sourceDecl = some (some (E.ctorPayable scope)) := by
  obtain ⟨state, ctors, hs, hcs, hcol⟩ := declarationParts_collect h scope
  rw [hc] at hcs
  simp only [ctorDecls, Option.map_eq_some_iff] at hcs
  obtain ⟨out, ho, rfl⟩ := hcs
  have kinds := state_kinds (stateParts_vars _ _ _ scope _ _ _ hs)
  obtain ⟨source, pay, ps, ms, body, f, hsd, _, hp, _, _, _, _, _, rfl, _⟩ :=
    constructorDecl_faithful T R scope d out ho E
  have found : E.ctorDecl scope =
      some (ctorDecl scope (.constructor ps ms pay none (.block body))) := by
    obtain ⟨before, after, hd, outside⟩ := placed
    unfold Source.Env.ctorDecl
    rw [hd, hcol]
    have skip : ∀ l : List Source.Decl,
        (∀ d ∈ l, d.scope = some scope → d.kind ≠ .constructor) →
        l.find? (fun d => d.kind == .constructor && d.scope == some scope) = none := by
      intro l hl
      rw [List.find?_eq_none]
      intro d hd hq
      simp only [Bool.and_eq_true, beq_iff_eq] at hq
      exact hl d hd hq.2 hq.1
    rw [List.append_assoc, List.find?_append,
      skip before (fun d hd hs => (outside d (List.mem_append_left _ hd) hs).1),
      Option.none_or]
    simp [ctorDecl]
  refine ⟨_, ho, found, ?_, ?_, ?_⟩
  · simp [Source.Env.ctorFrame, found]
  · simp [Source.progOf, found]
  · rw [hsd]
    simp [hp, Source.Env.ctorPayable, found, ctorDecl]

/-- The landed unit builder places these parts when they are its supplied
prefix: the contract declaration precedes them and only ordinary functions
follow. Its other composition facts remain that builder's. -/
theorem withFunctions_placed {T : Tables} {R : CallSpellExt.Registry} {scope : String}
    {parts : Syn (.list (.part false))} {fs : List (Name × FunDecl)} {u : Syn .unit}
    (h : Callee.withFunctions T R scope parts fs = some u) : Placed u.env scope parts := by
  obtain ⟨functions, hf, _, hd⟩ := Callee.withFunctions_declarations h
  refine ⟨[⟨.contract, scope, none, true,
    .contract false scope .none .nil (Callee.appendParts parts functions)⟩],
    functions.collect (some scope), ?_, ?_⟩
  · simp only [Source.Syn.env, hd, List.cons_append, List.nil_append]
  · intro d hd hs
    rcases List.mem_append.mp hd with hd | hd
    · rw [List.mem_singleton.mp hd] at hs
      cases hs
    · have hm : some d ∈ (functions.collect (some scope)).map some := List.mem_map_of_mem hd
      rw [Callee.functionParts_faithful T R scope fs functions hf] at hm
      obtain ⟨f, _, hfd⟩ := List.mem_map.mp hm
      obtain ⟨source, vis, _, _, hfn, _⟩ := Callee.fromMetadata_header hfd
      obtain ⟨_, _, _, _, _, _, _, _, rfl, _⟩ :=
        Callee.functionDecl_faithful T R scope source.name (some vis)
          (Callee.sourceMutability source.mutability) f.2 d hfn { decls := [] }
      exact ⟨(by intro k; cases k), (by intro k; cases k)⟩

/-! ## What remains

`Obligations` collects the hypotheses the theorems above take and the further
agreements they do not give, for the lane that composes the complete unit. -/

/-- The obligations left to the composing lane for a contract whose
declaration parts are `parts`, placed in the Source environment `E`.

Not expressible at declaration level, and so left in prose:

* **Execution.** No statement here relates running the Source constructor to
  running the model's `elabCtor` program. In particular the model prepends the
  initializers to the constructor body, while `Source.construct` runs
  `prog.inits` and then `prog.ctor`; `placed_inits` and `placed_explicit` keep
  the two apart and in order, and agreement of the two executions (initializers
  before the body, on both sides) is still to be proved.
* **Expression and body meaning.** Initializers, modifier arguments and the
  body are spelled, not interpreted: value agreement is the registry's
  faithfulness obligation and the statement simulation.
* **Erased header.** The model does not retain a state variable's visibility,
  `constant`/`immutable` or override, nor a legacy constructor visibility;
  none is written. A source `constant`/`immutable` is spelled as a mutable
  initialized variable, which is a difference to account for.
* **Modifier definitions and bases.** Only invocations are spelled; modifier
  definitions and any inheritance list are other components. -/
structure Obligations (T : Tables) (R : CallSpellExt.Registry) (C : Contract) (E : Source.Env)
    (scope : String) (parts : Syn (.list (.part false))) : Prop where
  /-- Whole-program composition: the parts are placed in the unit. -/
  placed : Placed E scope parts
  /-- Body and initializer typing: the complete unit elaborates. -/
  elaborates : Source.elaborates E = true
  /-- Every constructor invocation resolves as a modifier, so none is read as
  base-constructor arguments. -/
  modifiers : ∀ d out, C.ctor = some d → constructorDecl T R scope d = some out →
    ModifiersResolve E (some scope) out.modInvs
  /-- Retained metadata: the header's payable status is the model's flag. -/
  payable : ∀ d source, C.ctor = some d → d.sourceDecl = some source →
    payable? source = some d.payable

end Solidity.Correctness.Lowering.Total.Decode.Constructor
