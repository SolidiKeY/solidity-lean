import Solidity.Source.Infer
import Solidity.Source.Elaborated

/-!
# The elaborator: a resolution to its program (S02 item 1b)

`elaborate r` infers a derivation for every body, initializer, constant,
modifier invocation and base-constructor argument of `r`'s unit
(`Solidity/Source/Infer.lean`) and assembles the `Program` the semantics
runs.  Each piece is built together with the proof that it is the
elaboration of the derivation it came from (`RBody.Derived`,
`RInit.Derived`, `RConvArgs.Derived`), so the `Elaborated` it returns is
coherent by construction.  It returns `none` when a body, an initializer or
a base argument does not elaborate.

Where the syntax goes:

- a function, modifier, `receive` or `fallback` body: `Program.body`, its
  modifier invocations typed in its locals (parameters and named returns);
- a constructor: `Program.body` and `Program.ctor`; its invocations that
  name a contract (`constructor() B(x)`) are base arguments, not modifiers;
- `is B(args)`: base arguments, typed in the contract's scope with the
  constructor's locals present but unnamed, so they occupy the constructor's
  frame without being visible (solc evaluates them outside the constructor);
- a state variable's initializer: `Program.inits` in declaration order; a
  constant's: `Program.consts`.
-/

namespace Solidity.Source

/-- Converted arguments from a derivation, at parameters `ps`, in context
`C`. -/
def elabArgs (C : Ctx) (es : Syn (.list .expr)) (ps : List STy) :
    Option {a : RConvArgs C.env C.tys ps // RConvArgs.DerivedIn C es ps a} :=
  match TypedArgs.infer C es with
  | Option.some ⟨σs, D⟩ =>
    if h : argsFit C.env.isBase σs ps = true then
      Option.some ⟨RArgs.convert ps D.toR h, σs, D, h, HEq.rfl⟩
    else Option.none
  | Option.none => Option.none

/-- Arguments derived in a context, moved to an equal list of local types. -/
def castArgs {C : Ctx} {es : Syn (.list .expr)} {Γ Γ' : RCtx} {ps : List STy} (h : Γ = Γ')
    (a : RConvArgs C.env Γ ps) (ha : RConvArgs.DerivedIn C es ps a) :
    {a' : RConvArgs C.env Γ' ps // RConvArgs.DerivedIn C es ps a'} :=
  ⟨cast (congrArg (RConvArgs C.env · ps) h) a, by
    obtain ⟨σs, D, hf, he⟩ := ha
    exact ⟨σs, D, hf, (cast_heq _ a).trans he⟩⟩

/-- The modifier invocations among `invs`, each typed in `f`'s locals: a
constructor's invocations of a contract are skipped (base arguments). -/
def elabMods (E : Env) (d : Decl) (f : Frame) :
    (invs : List (IdPath × Syn (.opt .callArgs))) → Option {ms : List (RModInv E (tysOf f.locals)) //
      ∀ m ∈ ms, ∃ p a es, (p, a) ∈ invs ∧ E.modifierAt d.scope p = some (m.modifier, m.ps) ∧
        invArgs a = some es ∧ RConvArgs.DerivedIn ((f.ctx E d.scope).at f.locals) es m.ps m.args}
  | [] => Option.some ⟨[], fun _ h => nomatch h⟩
  | (p, args) :: rest => do
    let ⟨ms, hms⟩ ← elabMods E d f rest
    match hm : E.modifierAt d.scope p with
    | Option.some (m, ps) =>
      match hes : invArgs args with
      | Option.some es =>
        let ⟨a, ha⟩ ← elabArgs ((f.ctx E d.scope).at f.locals) es ps
        pure ⟨⟨m, ps, a⟩ :: ms, fun x hx => by
          cases hx with
          | head => exact ⟨p, args, es, List.mem_cons_self, hm, hes, ha⟩
          | tail _ hx =>
            obtain ⟨p', a', es', hmem, h1, h2, h3⟩ := hms x hx
            exact ⟨p', a', es', List.mem_cons_of_mem _ hmem, h1, h2, h3⟩⟩
      | Option.none => Option.none
    | Option.none =>
      if d.kind == .constructor && (E.contractAt d.scope p).isSome then
        pure ⟨ms, fun x hx => by
          obtain ⟨p', a', es', hmem, h1, h2, h3⟩ := hms x hx
          exact ⟨p', a', es', List.mem_cons_of_mem _ hmem, h1, h2, h3⟩⟩
      else Option.none

/-- **A body, elaborated**, with its modifier invocations. -/
def elabBody (E : Env) (d : Decl) : Option {b : RBody E // RBody.Derived E d b} :=
  match hf : d.frame? E with
  | Option.none => Option.none
  | Option.some f =>
    match ItemsD.infer (f.ctx E d.scope) f.locals f.body with
    | Option.none => Option.none
    | Option.some ⟨L', D⟩ =>
      match elabMods E d f d.modInvs.invList with
      | Option.none => Option.none
      | Option.some ⟨ms, hms⟩ =>
        Option.some ⟨RBody.ofDerivation f D ms, f, L', hf, ⟨D, rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩, hms⟩

/-- **An initializer, elaborated** and converted to the variable's type. -/
def elabInit (E : Env) (d : Decl) : Option {i : RInit E // i.var = d ∧ RInit.Derived E i} :=
  match he : d.init?, hτ : d.varTy E with
  | Option.some e, Option.some τ =>
    match Typed.infer (Ctx.forInit E d.scope) e with
    | Option.some ⟨σ, D⟩ =>
      if h : σ.implicit E.isBase τ = true then
        Option.some ⟨⟨d, τ, hτ, .conv D.toR (.inl h)⟩, rfl, e, σ, D, h, he, rfl⟩
      else Option.none
    | Option.none => Option.none
  | _, _ => Option.none

theorem tysOf_anonLocals (L : List (String × STy)) : tysOf (anonLocals L) = tysOf L := by
  simp only [tysOf, anonLocals, List.map_map]
  rfl

/-- The base arguments of inheritance-list entries `xs` of contract `c`. -/
def elabInherit (E : Env) (c : String) :
    (xs : List (IdPath × Syn (.opt .callArgs))) → Option {as : List (RBaseArg E (tysOf (E.ctorFrameLocals c))) //
      ∀ a ∈ as, a.ps = E.ctorParams a.base ∧ ∃ p es, (p, Syn.some (.positional es)) ∈ xs ∧
        E.contractAt Option.none p = some a.base ∧ RConvArgs.DerivedIn (E.inheritCtx c) es a.ps a.args}
  | [] => Option.some ⟨[], fun _ h => nomatch h⟩
  | (p, args) :: rest => do
    let ⟨as, has⟩ ← elabInherit E c rest
    let lift : ∀ (y : IdPath × Syn (.opt .callArgs)), ∀ a ∈ as, a.ps = E.ctorParams a.base ∧
        ∃ p' es, (p', Syn.some (.positional es)) ∈ y :: rest ∧
        E.contractAt Option.none p' = some a.base ∧ RConvArgs.DerivedIn (E.inheritCtx c) es a.ps a.args :=
      fun _ x hx => by
        obtain ⟨h0, p', es, hmem, h1, h2⟩ := has x hx
        exact ⟨h0, p', es, List.mem_cons_of_mem _ hmem, h1, h2⟩
    match args with
    | .none => pure ⟨as, lift _⟩
    | .some (.positional es) =>
      match hb : E.contractAt Option.none p with
      | Option.some b =>
        let ⟨a0, ha0⟩ ← elabArgs (E.inheritCtx c) es (E.ctorParams b)
        let ⟨a, ha⟩ := castArgs (tysOf_anonLocals _) a0 ha0
        pure ⟨⟨b, _, a⟩ :: as, fun x hx => by
          cases hx with
          | head => exact ⟨rfl, p, es, List.mem_cons_self, hb, ha⟩
          | tail _ hx => exact lift _ x hx⟩
      | Option.none => Option.none
    | .some (.named _) => Option.none

/-- A constructor's invocations of base contracts, typed in its parameters. -/
def elabCtorBases (E : Env) (c : String) (d : Decl) (f : Frame) (hL : f.locals = E.ctorFrameLocals c) :
    (xs : List (IdPath × Syn (.opt .callArgs))) → Option {as : List (RBaseArg E (tysOf (E.ctorFrameLocals c))) //
      ∀ a ∈ as, a.ps = E.ctorParams a.base ∧ ∃ p args es, (p, args) ∈ xs ∧
        E.contractAt d.scope p = some a.base ∧ invArgs args = some es ∧
        RConvArgs.DerivedIn ((f.ctx E d.scope).at f.locals) es a.ps a.args}
  | [] => Option.some ⟨[], fun _ h => nomatch h⟩
  | (p, args) :: rest => do
    let ⟨as, has⟩ ← elabCtorBases E c d f hL rest
    let lift : ∀ a ∈ as, a.ps = E.ctorParams a.base ∧ ∃ p' args' es, (p', args') ∈ (p, args) :: rest ∧
        E.contractAt d.scope p' = some a.base ∧ invArgs args' = some es ∧
        RConvArgs.DerivedIn ((f.ctx E d.scope).at f.locals) es a.ps a.args := fun x hx => by
      obtain ⟨h0, p', a', es, hmem, h1, h2, h3⟩ := has x hx
      exact ⟨h0, p', a', es, List.mem_cons_of_mem _ hmem, h1, h2, h3⟩
    match hb : E.contractAt d.scope p with
    | Option.some b =>
      match hes : invArgs args with
      | Option.some es =>
        let ⟨a0, ha0⟩ ← elabArgs ((f.ctx E d.scope).at f.locals) es (E.ctorParams b)
        let ⟨a, ha⟩ := castArgs (congrArg tysOf hL) a0 ha0
        pure ⟨⟨b, _, a⟩ :: as, fun x hx => by
          cases hx with
          | head => exact ⟨rfl, p, args, es, List.mem_cons_self, hb, hes, ha⟩
          | tail _ hx => exact lift x hx⟩
      | Option.none => Option.none
    | Option.none => pure ⟨as, lift⟩

/-- **The base-constructor arguments contract `c` gives**: its
constructor's invocations, then its inheritance list. -/
def elabBaseArgs (E : Env) (c : String) :
    Option {as : List (RBaseArg E (tysOf (E.ctorFrameLocals c))) // ∀ a ∈ as, RBaseArg.Derived E c a} := do
  let ⟨fromInherit, hi⟩ ← elabInherit E c (E.inheritOf c).inheritList
  let hi' : ∀ a ∈ fromInherit, RBaseArg.Derived E c a := fun x hx => by
    obtain ⟨h0, p, es, h1, h2, h3⟩ := hi x hx
    exact ⟨h0, Or.inl ⟨p, es, h1, h2, h3⟩⟩
  match hd : E.ctorDecl c with
  | Option.none => pure ⟨fromInherit, hi'⟩
  | Option.some d =>
    match hf : d.frame? E with
    | Option.none => pure ⟨fromInherit, hi'⟩
    | Option.some f =>
      have hL : f.locals = E.ctorFrameLocals c := by
        simp only [Env.ctorFrameLocals, Env.ctorFrame, hd, Option.bind_some, hf]
      let ⟨fromCtor, hc⟩ ← elabCtorBases E c d f hL d.modInvs.invList
      pure ⟨fromCtor ++ fromInherit, fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨h0, p, args, es, h1, h2, h3, h4⟩ := hc x hx
          exact ⟨h0, Or.inr ⟨d, f, p, args, es, hd, hf, h1, h2, h3, h4⟩⟩
        · exact hi' x hx⟩

/-- The state variables of contract `c` that are not constants, in order. -/
def Env.stateVarsOf (E : Env) (c : String) : List Decl :=
  E.decls.filter fun d => d.kind == .stateVar && d.scope == Option.some c && !d.isConst

/-- **The program** of an environment, every part elaborated on demand. -/
def progOf (E : Env) : Program E where
  body d := (elabBody E d).map Subtype.val
  consts d := if d.isConst then (elabInit E d).map Subtype.val else Option.none
  inits c := (E.stateVarsOf c).filterMap fun d => (elabInit E d).map Subtype.val
  ctor c := (E.ctorDecl c).bind fun d => (elabBody E d).map Subtype.val
  ctorLocals c := tysOf (E.ctorFrameLocals c)
  baseArgs c := ((elabBaseArgs E c).map Subtype.val).getD []
  contracts := E.contracts

/-- Whether every part of a unit elaborates: each body, each initializer,
each contract's base arguments. -/
def elaborates (E : Env) : Bool :=
  E.decls.all (fun d => !d.hasBody || (elabBody E d).isSome) &&
  E.decls.all (fun d => d.init?.isNone || (elabInit E d).isSome) &&
  E.contracts.all fun c => (elabBaseArgs E c).isSome

theorem mem_of_map_val {α : Type} {P : α → Prop} {o : Option (Subtype P)} {a : α}
    (h : o.map Subtype.val = some a) : P a := by
  cases o with
  | none => cases h
  | some x =>
    cases h
    exact x.property

/-- **The elaborator**: a resolution's program, when every part of it
elaborates; coherent by construction. -/
def elaborate (r : Resolution) : Option Elaborated :=
  if elaborates r.env then
    Option.some
      { res := r
        prog := progOf r.env
        bodies_typed := fun _ _ _ hb => by
          obtain ⟨f, L', hf, hD, _⟩ := mem_of_map_val hb
          exact ⟨f, L', hf, hD⟩
        contracts_eq := rfl
        mods_typed := fun _ _ hb => by
          obtain ⟨f, _, hf, _, hm⟩ := mem_of_map_val hb
          exact ⟨f, hf, hm⟩
        ctor_typed := fun c b hb => by
          simp only [progOf, Option.bind_eq_some_iff] at hb
          obtain ⟨d, hd, hb⟩ := hb
          have hm := List.mem_of_find?_eq_some hd
          have hp := List.find?_some hd
          simp only [Bool.and_eq_true, beq_iff_eq] at hp
          exact ⟨d, hm, hp.1, hp.2, hb⟩
        consts_typed := fun d i hi => by
          simp only [progOf] at hi
          split at hi
          · exact mem_of_map_val (P := fun i => i.var = d ∧ RInit.Derived r.env i) hi
          · cases hi
        inits_typed := fun c i hi => by
          simp only [progOf, List.mem_filterMap] at hi
          obtain ⟨d, hd, hi⟩ := hi
          have hp := (List.mem_filter.mp hd).2
          simp only [Bool.and_eq_true, beq_iff_eq] at hp
          obtain ⟨hv, hD⟩ := mem_of_map_val hi
          exact ⟨hv ▸ hp.1.2, hD⟩
        baseArgs_typed := fun c a ha => by
          simp only [progOf] at ha
          cases h : elabBaseArgs r.env c with
          | none => rw [h] at ha; cases ha
          | some x =>
            rw [h] at ha
            exact x.property a ha }
  else Option.none

end Solidity.Source
