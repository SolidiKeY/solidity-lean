import Solidity.Correctness.Lowering.Total.Decode.Callee.Units
import Solidity.Correctness.Lowering.Total.TransientDecode
import Solidity.Source.Elaborate

/-!
# Constructor and state-initializer declaration components

Reads `Contract.ctor`, `Contract.inits`, `Contract.vars` and the retained
constructor header (`FunDecl.sourceDecl`), and spells Source syntax: the
explicit constructor when there is one, then one state variable per root with
its original initializer. Parameters, modifier invocations, expression/body
spelling and the root element table are the landed components.

The theorems are declaration-level: what is spelled, in which order, the
Source frame and declared types, and what a successful `Source.elabInit` gives.
Unsupported inputs return `none` (a reference root or parameter, a root or
parameter with an enum or function-type marker, no retained constructor
header, constructor returns, an initializer of a transient root, initializers
out of root order or naming no root): gaps, not admission conditions.

Left to the composing lane:
* **Composition**: `Placed`, unit elaboration, agreement of these roots with
  `TransientDecode.decls`, inherited state, bases, the pragma, identifier
  validity, stale width rows, and that `T` and `Contract.enums`/`structs`/`errors`
  cover what initializers and bodies mention.
* **Metadata**: `ModifiersResolve`; the header's payable status against
  `FunDecl.payable`; the header's `name`/`signature`/`declaration` and
  `FunDecl.spec`/`paramLocs`/`retMem`/`retStorage`, unread; a state variable's
  visibility, `constant`/`immutable` and override and a legacy constructor
  visibility, not retained and not written (a source constant is spelled as a
  mutable initialized variable); modifier definitions.
* **Semantics**: nothing relates Source deployment to the model's `elabCtor`
  program. The model prepends initializers to the constructor body;
  `Source.construct` runs `prog.inits` and `prog.ctor` separately, along the
  linearization, in a pipeline-dependent order. `placed_inits` and `placed_ctor`
  keep the two apart; that initializers run before the body on both sides, and
  all value agreement of initializers, modifier arguments and bodies, is open.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.Constructor

open Source (Syn STy)
open Callee (parameters Slots modifiers ModifierSpelling)

/-- Two lists related entry by entry, in order: nothing dropped, added or moved. -/
inductive Ordered {α β : Type} (r : α → β → Prop) : List α → List β → Prop where
  | nil : Ordered r [] []
  | cons {a b as bs} : r a b → Ordered r as bs → Ordered r (a :: as) (b :: bs)

/-- Payable status of a retained constructor header. Another role, or a
`pure`/`view` header, gives nothing; `FunDecl.payable` is not consulted. -/
def payable? (s : SourceFunction) : Option Bool :=
  match s.callable, s.mutability with
  | .constructor, .nonpayable => some false
  | .constructor, .payable => some true
  | _, _ => none

/-- The constructor's syntax: original parameters at the declaration's width
table, modifier applications in order, the header's payable status, the
original body. No visibility token is written: none is retained. -/
def constructorPart (T : Tables) (R : CallSpellExt.Registry) (d : FunDecl) :
    Option (Syn (.part false)) := do
  let pay ← payable? (← d.sourceDecl)
  if d.rets.isEmpty && !d.params.any (fun p => TransientDecode.unreadMarker d.widths p.1) then
    let ps ← parameters d.widths d.params
    let ms ← modifiers T R d.mods
    let body ← Tables.WithExpr.items T (Calls.expr T R) .body d.body
    pure (.constructor ps ms pay none (.block body))
  else none

/-- The declaration Source collects for a constructor written in `scope`. -/
def ctorDecl (scope : String) (node : Syn (.part false)) : Source.Decl :=
  ⟨.constructor, "", some scope, false, node⟩

/-- The constructor declarations of an optional model constructor: one, or
none for the implicit constructor. -/
def ctorDecls (T : Tables) (R : CallSpellExt.Registry) (scope : String) :
    Option FunDecl → Option (List Source.Decl)
  | none => some []
  | some d => (constructorPart T R d).map ([ctorDecl scope ·])

/-- **Successful constructor assembly.** The declaration is the constructor
of the original parameters, modifier applications and body, payable as the
retained header says; its Source frame has the original parameter names,
table-corresponding parameter types, no return slot, the spelled body, and
reads `msg.value` exactly when payable. No execution agreement follows. -/
theorem constructorPart_faithful {T : Tables} {R : CallSpellExt.Registry} {d : FunDecl}
    {node : Syn (.part false)} (h : constructorPart T R d = some node) (scope : String)
    (E : Source.Env) :
    ∃ source pay ps ms body f,
      d.sourceDecl = some source ∧ payable? source = some pay ∧ d.rets = [] ∧
      parameters d.widths d.params = some ps ∧ ModifierSpelling T R d.mods ms ∧
      Tables.WithExpr.items T (Calls.expr T R) .body d.body = some body ∧
      node = .constructor ps ms pay none (.block body) ∧
      (ctorDecl scope node).frame? E = some f ∧
      f.names = d.params.map (fun p => some p.1) ∧ f.rnames = [] ∧
      Slots d.widths d.params f.ps ∧ f.rs = [] ∧
      f.body = body ∧ f.msgValue = pay ∧ f.inModifier = false := by
  simp only [constructorPart, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff] at h
  obtain ⟨source, hs, pay, hp, h⟩ := h
  split at h
  · rename_i ok
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ps, hps, ms, hms, body, hb, rfl⟩ := h
    obtain ⟨names, τs, typed, slots⟩ := Callee.parameters_faithful d.widths E (some scope) _ _ hps
    refine ⟨source, pay, ps, ms, body, ⟨ps.paramNames, τs, [], [], body, pay, false⟩, hs, hp,
      by simpa using (Bool.and_eq_true_iff.mp ok).1, hps, Callee.modifiers_spelled T R _ _ hms, hb,
      rfl, ?_, names, rfl, slots, rfl, rfl, rfl, rfl⟩
    simp [ctorDecl, Source.Decl.frame?, Source.Frame.mk?, typed, Source.Syn.tys,
      Source.Syn.paramNames]
  · cases h

/-- Every written invocation names a modifier of the unit. Source reads a
constructor's invocation that resolves to no modifier but names a contract as
base-constructor arguments (`Source.elabMods` skips it); the model has modifier
applications only, so this is required of the whole unit. -/
def ModifiersResolve (E : Source.Env) (scope : Option String) (ms : Syn (.list .modInv)) : Prop :=
  ∀ inv ∈ ms.invList, (E.modifierAt scope inv.1).isSome = true

/-- When every invocation resolves as a modifier, successful Source
elaboration keeps each, in order, as that modifier: none is skipped as a
base-constructor argument list. -/
theorem elabMods_resolved (E : Source.Env) (d : Source.Decl) (f : Source.Frame) :
    ∀ (invs : List (Source.IdPath × Syn (.opt .callArgs))) ms,
      Source.elabMods E d f invs = some ms →
      (∀ inv ∈ invs, (E.modifierAt d.scope inv.1).isSome = true) →
      Ordered (fun (m : Source.RModInv E (Source.tysOf f.locals))
          (inv : Source.IdPath × Syn (.opt .callArgs)) =>
        E.modifierAt d.scope inv.1 = some (m.modifier, m.ps)) ms.val invs
  | [], ms, h, _ => by
      simp only [Source.elabMods, Option.some.injEq] at h; subst h; exact .nil
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
      · rename_i hm; rw [hm] at hp; cases hp

/-- The declaration Source collects for a primitive state variable of
`scope`. No visibility, constness or override is written: none is retained. -/
def varDecl (scope : String) (elem : Source.Elem) (transient : Bool) (x : Name)
    (init : Syn (.opt .expr)) : Source.Decl :=
  ⟨.stateVar, x, some scope, false, .stateVar (.elem elem) none none none transient x init⟩

/-- The initializer of the root `x`, when it is the next one pending. -/
def takeInit (x : Name) : List (Name × RawExpr) → Option RawExpr × List (Name × RawExpr)
  | (y, e) :: rest => if x = y then (some e, rest) else (none, (y, e) :: rest)
  | [] => (none, [])

/-- The state variables in root order, each with its pending initializer.
Initializers are consumed in their own order, so the result exists only when
that order is the root order and each names a root: none is dropped, moved or
attached to another variable. A transient root's initializer is refused. -/
def stateParts (el : Name → PrimTy → Option Source.Elem) (tr : Name → Bool)
    (spell : RawExpr → Option (Syn .expr)) :
    List (Name × Ty) → List (Name × RawExpr) → Option (Syn (.list (.part false)))
  | [], [] => some .nil
  | [], _ :: _ => none
  | (x, .prim p) :: vars, inits => do
      let elem ← el x p
      let rest ← stateParts el tr spell vars (takeInit x inits).2
      match (takeInit x inits).1 with
      | none => pure (.cons (.stateVar (.elem elem) none none none (tr x) x .none) rest)
      | some e => if tr x then none else
          pure (.cons (.stateVar (.elem elem) none none none false x (.some (← spell e))) rest)
  | (_, .ref _) :: _, _ => none

/-- One root and its Source declaration: the same name, a state variable of
`scope` at the table's elementary type, transient as marked. -/
def VarSlot (el : Name → PrimTy → Option Source.Elem) (tr : Name → Bool) (scope : String)
    (v : Name × Ty) (d : Source.Decl) : Prop :=
  ∃ p elem init, v.2 = .prim p ∧ el v.1 p = some elem ∧ d = varDecl scope elem (tr v.1) v.1 init

/-- One model initializer and its Source declaration: the target root, not
transient, with the original expression as spelled. -/
def InitSlot (spell : RawExpr → Option (Syn .expr)) (scope : String) (i : Name × RawExpr)
    (d : Source.Decl) : Prop :=
  ∃ elem t, spell i.2 = some t ∧ d = varDecl scope elem false i.1 (.some t)

/-- **Roots and initializers are preserved**: the collected declarations are
the roots, one each and in order; those carrying an initializer are the
model's initializers, one each and in order, each on its target root. -/
theorem stateParts_faithful (el : Name → PrimTy → Option Source.Elem) (tr : Name → Bool)
    (spell : RawExpr → Option (Syn .expr)) (scope : String) :
    ∀ vars inits parts, stateParts el tr spell vars inits = some parts →
      Ordered (VarSlot el tr scope) vars (parts.collect (some scope)) ∧
      Ordered (InitSlot spell scope) inits
        ((parts.collect (some scope)).filter fun d => d.init?.isSome)
  | [], [], _, h => by cases h; exact ⟨.nil, .nil⟩
  | [], _ :: _, _, h => by cases h
  | (x, .ref _) :: _, _, _, h => by cases h
  | (x, .prim p) :: vars, inits, parts, h => by
      simp only [stateParts, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨elem, he, rest, hr, h⟩ := h
      obtain ⟨ihv, ihi⟩ := stateParts_faithful el tr spell scope vars _ rest hr
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
        rw [same] at ihi
        rw [Source.Syn.collect]
        exact ⟨.cons ⟨p, elem, _, rfl, he, rfl⟩ ihv, ihi⟩
      · rename_i e hn
        split at h
        · cases h
        · rename_i ht
          simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨t, hs, rfl⟩ := h
          have ht : tr x = false := by simpa using ht
          cases inits with
          | nil => cases hn
          | cons i inits =>
              obtain ⟨y, e'⟩ := i
              simp only [takeInit] at hn ihi
              split at hn <;> cases hn
              rename_i hxy
              subst hxy
              simp only [if_true] at ihi
              rw [Source.Syn.collect]
              exact ⟨.cons ⟨p, elem, .some t, rfl, he, by rw [ht]; rfl⟩ ihv,
                .cons ⟨elem, t, hs, rfl⟩ ihi⟩

theorem elabInit_none {E : Source.Env} {d : Source.Decl} (h : d.init? = none) :
    Source.elabInit E d = none := by
  unfold Source.elabInit
  split
  · rename_i _ _ he _; rw [h] at he; cases he
  · rfl

/-- **A spelled initializer, elaborated.** For the state variable of a root
with initializer `t`, any result of `Source.elabInit` has converted type the
root's table type in storage, and its expression is a typing derivation of
`t` itself at some type `σ`, under an implicit conversion from `σ`. This reads
the result's own certificate: that `σ` is the type `Typed.infer` returns,
whether elaboration succeeds and what `t` evaluates to are not claimed. -/
theorem varDecl_elabInit {E : Source.Env} {scope : String} {elem : Source.Elem} {transient : Bool}
    {x : Name} {t : Syn .expr}
    (i : {i : Source.RInit E //
      i.var = varDecl scope elem transient x (.some t) ∧ Source.RInit.Derived E i}) :
    i.val.τ = elem.ty .storage ∧
    ∃ (σ : STy) (D : Source.Typed (Source.Ctx.forInit E i.val.var.scope) t σ)
      (c : σ.implicit E.isBase E.mapFree i.val.τ = true), i.val.e = .conv D.toR (.inl c) := by
  obtain ⟨⟨var, τ, hτ, r⟩, hv, e, σ, D, c, he, hr⟩ := i
  cases hv
  have hty : (varDecl scope elem transient x (.some t)).varTy E = some (elem.ty .storage) := by
    simp [varDecl, Source.Decl.varTy, Source.Syn.ty, Source.Syn.tys]
  cases (hτ.symm.trans hty : some τ = some _)
  cases (he : some t = some e)
  exact ⟨rfl, σ, D, c, hr⟩

/-- **The elaborated program keeps declaration order**: when the unit
elaborates, a contract's initializers in the Source program are exactly its
non-constant state variables that carry an initializer, in declaration order. -/
theorem progOf_inits (E : Source.Env) (c : String) (hE : Source.elaborates E = true) :
    ((Source.progOf E).inits c).map (fun i => i.var) =
      (E.stateVarsOf c).filter fun d => d.init?.isSome := by
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
            simp only [Source.elaborates, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hE
            have ok : (Source.elabInit E d).isSome = true := by
              rcases hE.1.2 d (hl d List.mem_cons_self) with hn | hs
              · rw [hi] at hn; cases hn
              · exact hs
            obtain ⟨i, hi'⟩ := Option.isSome_iff_exists.mp ok
            simp only [List.filterMap_cons, hi', Option.map_some, List.map_cons, List.filter_cons,
              hi, Option.isSome_some, if_true, ih, i.property.1]
  exact sub _ fun d hd => (List.mem_filter.mp hd).1

/-- The parts this component owns: the explicit constructor if there is one,
then every root with its initializer. Without a model constructor there is no
constructor part: Source's implicit constructor is the absence of one. The
model does not retain where the constructor stood, and Source reads neither
it nor the state variables by position relative to the other. -/
def declarationParts (T : Tables) (R : CallSpellExt.Registry) (C : Contract) :
    Option (Syn (.list (.part false))) := do
  let state ← stateParts (TransientDecode.elemOf C) (fun x => C.transientRoots.contains x)
    (Calls.expr T R) C.vars C.inits
  match C.ctor with
  | none => pure state
  | some d => pure (.cons (← constructorPart T R d) state)

/-- **Declaration assembly.** The collected declarations are the constructor
declaration, one for an explicit constructor and none for the implicit one,
followed by the state variables in root order. -/
theorem declarationParts_collect {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (h : declarationParts T R C = some parts) (scope : String) :
    ∃ state ctors,
      stateParts (TransientDecode.elemOf C) (fun x => C.transientRoots.contains x)
        (Calls.expr T R) C.vars C.inits = some state ∧
      ctorDecls T R scope C.ctor = some ctors ∧
      parts.collect (some scope) = ctors ++ state.collect (some scope) := by
  simp only [declarationParts, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨state, hs, h⟩ := h
  cases hc : C.ctor with
  | none =>
      rw [hc] at h
      simp only [Option.pure_def, Option.some.injEq] at h; subst h
      exact ⟨state, [], hs, rfl, rfl⟩
  | some d =>
      rw [hc] at h
      simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨node, hn, rfl⟩ := h
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ :=
        constructorPart_faithful hn scope ⟨[]⟩
      refine ⟨state, _, hs, by rw [ctorDecls, hn]; rfl, ?_⟩
      rw [Source.Syn.collect]
      rfl

/-- What the facts below need of the complete unit: the parts' declarations
occur contiguously in `E`, and nothing else in `E` is a constructor or state
variable of contract `scope`. -/
def Placed (E : Source.Env) (scope : String) (parts : Syn (.list (.part false))) : Prop :=
  ∃ before after, E.decls = before ++ parts.collect (some scope) ++ after ∧
    ∀ d ∈ before ++ after, d.scope = some scope → d.kind ≠ .constructor ∧ d.kind ≠ .stateVar

private theorem placed_filter {E : Source.Env} {scope : String} {parts : Syn (.list (.part false))}
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

private theorem placed_kinds {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (h : declarationParts T R C = some parts)
    {E : Source.Env} {scope : String} (placed : Placed E scope parts) :
    ∃ state ctors,
      stateParts (TransientDecode.elemOf C) (fun x => C.transientRoots.contains x)
        (Calls.expr T R) C.vars C.inits = some state ∧
      ctorDecls T R scope C.ctor = some ctors ∧
      E.decls.filter (fun d => d.kind == .constructor && d.scope == some scope) = ctors ∧
      E.stateVarsOf scope = state.collect (some scope) := by
  obtain ⟨state, ctors, hs, hc, hcol⟩ := declarationParts_collect h scope
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
  have ctor : ∀ d ∈ ctors, d.kind = .constructor ∧ d.scope = some scope := by
    cases hctor : C.ctor <;> rw [hctor] at hc <;>
      simp only [ctorDecls, Option.map_eq_some_iff, Option.some.injEq] at hc
    · subst hc; simp
    · obtain ⟨node, _, rfl⟩ := hc; simp [ctorDecl]
  refine ⟨state, ctors, hs, hc, ?_, ?_⟩
  · rw [placed_filter placed _ (by simp +contextual), hcol, List.filter_append,
      List.filter_eq_self.mpr (fun d hd => by simp [ctor d hd]),
      List.filter_eq_nil_iff.mpr (fun d hd => by simp [(vars d hd).1]), List.append_nil]
  · unfold Source.Env.stateVarsOf
    rw [placed_filter placed _ (by simp +contextual), hcol, List.filter_append,
      List.filter_eq_nil_iff.mpr (fun d hd => by simp [(ctor d hd).1]),
      List.filter_eq_self.mpr (fun d hd => by simp [vars d hd]), List.nil_append]

/-- **Placed state variables and initializers.** In a unit that places the
parts, contract `scope`'s non-constant state variables are the roots'
declarations in root order; and when the unit elaborates, the Source
program's initializers of `scope` are the model's, one each and in order,
each the spelled original expression on its target root. -/
theorem placed_inits {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (h : declarationParts T R C = some parts)
    {E : Source.Env} {scope : String} (placed : Placed E scope parts) :
    Ordered (VarSlot (TransientDecode.elemOf C) (fun x => C.transientRoots.contains x) scope)
      C.vars (E.stateVarsOf scope) ∧
    (Source.elaborates E = true →
      Ordered (fun i (r : Source.RInit E) => InitSlot (Calls.expr T R) scope i r.var)
        C.inits ((Source.progOf E).inits scope)) := by
  obtain ⟨state, _, hs, _, _, hv⟩ := placed_kinds h placed
  obtain ⟨vars, inits⟩ := stateParts_faithful _ _ _ scope _ _ _ hs
  rw [← hv] at vars inits
  refine ⟨vars, fun hE => ?_⟩
  rw [← progOf_inits E scope hE] at inits
  generalize (Source.progOf E).inits scope = rs at inits
  generalize C.inits = is at inits
  induction rs generalizing is with
  | nil => cases inits; exact .nil
  | cons r rs ih => cases inits with | cons hd tl => exact .cons hd (ih _ tl)

/-- **The constructor Source finds.** In a unit that places the parts, the
constructor declaration of `scope` is the assembled one, or none for the
implicit constructor; the constructor frame is that declaration's, and the
program's constructor body is the elaboration of that declaration alone. -/
theorem placed_ctor {T : Tables} {R : CallSpellExt.Registry} {C : Contract}
    {parts : Syn (.list (.part false))} (h : declarationParts T R C = some parts)
    {E : Source.Env} {scope : String} (placed : Placed E scope parts) :
    ∃ ctors, ctorDecls T R scope C.ctor = some ctors ∧ E.ctorDecl scope = ctors.head? ∧
      E.ctorFrame scope = ctors.head?.bind (·.frame? E) ∧
      (Source.progOf E).ctor scope =
        ctors.head?.bind fun d => (Source.elabBody E d).map Subtype.val := by
  obtain ⟨_, ctors, _, hcs, hf, _⟩ := placed_kinds h placed
  have found : E.ctorDecl scope = ctors.head? := by
    rw [Source.Env.ctorDecl, ← hf, List.head?_filter]
  exact ⟨ctors, hcs, found, by rw [Source.Env.ctorFrame, found], by simp only [Source.progOf, found]⟩

end Solidity.Correctness.Lowering.Total.Decode.Constructor
