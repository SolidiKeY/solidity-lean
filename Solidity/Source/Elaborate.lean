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
  modifier invocations resolved in its parameters;
- a constructor: `Program.body` and `Program.ctor`; its invocations that
  name a contract (`constructor() B(x)`) are base arguments, not modifiers;
- `is B(args)`: base arguments, typed in the contract's scope with the
  constructor's locals present but unnamed, so they occupy the constructor's
  frame without being visible (solc evaluates them outside the constructor);
- a state variable's initializer: `Program.inits` in declaration order; a
  constant's: `Program.consts`.
-/

namespace Solidity.Source

/-- The modifier invocations of a body. -/
def Decl.modInvs (d : Decl) : Syn (.list .modInv) :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ _ ms _ _ _ _ => ms
  | .constructor, _, .constructor _ ms _ _ _ => ms
  | .fallback, _, .fallback _ _ _ ms _ _ _ => ms
  | .receive, _, .receive _ _ ms _ _ _ => ms
  | _, _, _ => .nil

/-- An invocation's positional arguments (none written: none). -/
def invArgs : Syn (.opt .callArgs) → Option (Syn (.list .expr))
  | .none => Option.some .nil
  | .some (.positional es) => Option.some es
  | _ => Option.none

/-- Converted arguments from a derivation, at parameters `ps`, in context
`C`. -/
def elabArgs (C : Ctx) (es : Syn (.list .expr)) (ps : List STy) :
    Option {a : RConvArgs C.env C.tys ps // RConvArgs.Derived C.env C.tys ps a} :=
  match TypedArgs.infer C es with
  | Option.some ⟨σs, D⟩ =>
    if h : argsFit C.env.isBase σs ps = true then
      Option.some ⟨RArgs.convert ps D.toR h, C, es, σs, D, h, rfl, rfl, HEq.rfl⟩
    else Option.none
  | Option.none => Option.none

/-- The declaration of contract `c`'s constructor. -/
def Env.ctorDecl (E : Env) (c : String) : Option Decl :=
  E.decls.find? fun d => d.kind == .constructor && d.scope == Option.some c

/-- The frame of contract `c`'s constructor. -/
def Env.ctorFrame (E : Env) (c : String) : Option Frame :=
  (E.ctorDecl c).bind (·.frame? E)

/-- The locals of contract `c`'s constructor (`[]` without one). -/
def Env.ctorFrameLocals (E : Env) (c : String) : List (String × STy) :=
  match E.ctorFrame c with
  | Option.some f => f.locals
  | Option.none => []

/-- The parameters of contract `c`'s constructor. -/
def Env.ctorParams (E : Env) (c : String) : List STy :=
  match E.ctorFrame c with
  | Option.some f => f.ps
  | Option.none => []

/-- The modifier a path names, with its parameters. -/
def Env.modifierAt (E : Env) (scope : Option String) (p : IdPath) : Option (Decl × List STy) :=
  match E.lookupPath scope p with
  | [m] => if m.kind == .modifier then (m.frame? E).map fun f => (m, f.ps) else Option.none
  | _ => Option.none

/-- The contract a path names. -/
def Env.contractAt (E : Env) (scope : Option String) (p : IdPath) : Option String :=
  match E.lookupPath scope p with
  | [b] => if b.kind == .contract then Option.some b.name else Option.none
  | _ => Option.none

/-- A body's modifier invocations, each typed in its locals: a constructor's
invocations of a contract are skipped (base arguments). -/
def elabMods (E : Env) (d : Decl) (f : Frame) :
    Syn (.list .modInv) → Option {ms : List (RModInv E (tysOf f.locals)) //
      ∀ m ∈ ms, RConvArgs.Derived E (tysOf f.locals) m.ps m.args}
  | .nil => Option.some ⟨[], fun _ h => nomatch h⟩
  | .cons (.modInv p args) rest => do
    let ⟨ms, hms⟩ ← elabMods E d f rest
    match E.modifierAt d.scope p with
    | Option.some (m, ps) =>
      let es ← invArgs args
      let ⟨a, ha⟩ ← elabArgs ((f.ctx E d.scope).at f.locals) es ps
      pure ⟨⟨m, ps, a⟩ :: ms, fun x hx => by
        cases hx with
        | head => exact ha
        | tail _ hx => exact hms x hx⟩
    | Option.none =>
      if d.kind == .constructor && (E.contractAt d.scope p).isSome then pure ⟨ms, hms⟩
      else Option.none

/-- **A body, elaborated**, with its modifier invocations. -/
def elabBody (E : Env) (d : Decl) : Option {b : RBody E // RBody.Derived E d b} :=
  match hf : d.frame? E with
  | Option.none => Option.none
  | Option.some f =>
    match ItemsD.infer (f.ctx E d.scope) f.locals f.body with
    | Option.none => Option.none
    | Option.some ⟨L', D⟩ =>
      match elabMods E d f d.modInvs with
      | Option.none => Option.none
      | Option.some ⟨ms, hms⟩ =>
        Option.some ⟨RBody.ofDerivation f D ms, ⟨f, L', hf, D, rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩, hms⟩

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

/-- The constructor's locals, unnamed: the context of `is B(args)`. -/
def anonLocals (L : List (String × STy)) : List (String × STy) := L.map fun p => ("", p.2)

theorem tysOf_anonLocals (L : List (String × STy)) : tysOf (anonLocals L) = tysOf L := by
  simp only [tysOf, anonLocals, List.map_map]
  rfl

/-- Converted arguments, moved to an equal list of local types. -/
def castDerived {E : Env} {Γ Γ' : RCtx} {ps : List STy} (h : Γ = Γ')
    (a : {a : RConvArgs E Γ ps // RConvArgs.Derived E Γ ps a}) :
    {a : RConvArgs E Γ' ps // RConvArgs.Derived E Γ' ps a} :=
  h ▸ a

/-- The base arguments of an inheritance list, typed with the constructor's
locals unnamed. -/
def elabInherit (E : Env) (c : String) :
    Syn (.list .inherit) → Option {as : List (RBaseArg E (tysOf (E.ctorFrameLocals c))) //
      ∀ a ∈ as, RConvArgs.Derived E (tysOf (E.ctorFrameLocals c)) a.ps a.args}
  | .nil => Option.some ⟨[], fun _ h => nomatch h⟩
  | .cons (.inherit p args) rest => do
    let ⟨as, has⟩ ← elabInherit E c rest
    match args with
    | .none => pure ⟨as, has⟩
    | .some (.positional es) =>
      let b ← E.contractAt Option.none p
      let C : Ctx := { env := E, scope := Option.some c, locals := anonLocals (E.ctorFrameLocals c) }
      let ⟨a, ha⟩ := castDerived (tysOf_anonLocals _) (← elabArgs C es (E.ctorParams b))
      pure ⟨⟨b, _, a⟩ :: as, fun x hx => by
        cases hx with
        | head => exact ha
        | tail _ hx => exact has x hx⟩
    | .some (.named _) => Option.none

/-- A constructor's invocations of base contracts, typed in its locals. -/
def elabCtorBases (E : Env) (c : String) (d : Decl) (f : Frame) (hL : f.locals = E.ctorFrameLocals c) :
    Syn (.list .modInv) → Option {as : List (RBaseArg E (tysOf (E.ctorFrameLocals c))) //
      ∀ a ∈ as, RConvArgs.Derived E (tysOf (E.ctorFrameLocals c)) a.ps a.args}
  | .nil => Option.some ⟨[], fun _ h => nomatch h⟩
  | .cons (.modInv p args) rest => do
    let ⟨as, has⟩ ← elabCtorBases E c d f hL rest
    match E.contractAt d.scope p with
    | Option.some b =>
      let es ← invArgs args
      let ⟨a, ha⟩ := castDerived (congrArg tysOf hL)
        (← elabArgs ((f.ctx E d.scope).at f.locals) es (E.ctorParams b))
      pure ⟨⟨b, _, a⟩ :: as, fun x hx => by
        cases hx with
        | head => exact ha
        | tail _ hx => exact has x hx⟩
    | Option.none => pure ⟨as, has⟩

/-- The inheritance list of contract `c`. -/
def Env.inheritOf (E : Env) (c : String) : Syn (.list .inherit) :=
  match E.decls.find? fun d => d.kind == .contract && d.name == c && d.scope == Option.none with
  | Option.some d =>
    match d.kind, d.top, d.node with
    | .contract, _, .contract _ _ _ is _ => is
    | _, _, _ => .nil
  | Option.none => .nil

/-- **The base-constructor arguments contract `c` gives**: its
constructor's invocations, then its inheritance list. -/
def elabBaseArgs (E : Env) (c : String) :
    Option {as : List (RBaseArg E (tysOf (E.ctorFrameLocals c))) //
      ∀ a ∈ as, RConvArgs.Derived E (tysOf (E.ctorFrameLocals c)) a.ps a.args} := do
  let ⟨fromInherit, hi⟩ ← elabInherit E c (E.inheritOf c)
  match hd : E.ctorDecl c with
  | Option.none => pure ⟨fromInherit, hi⟩
  | Option.some d =>
    match hf : d.frame? E with
    | Option.none => pure ⟨fromInherit, hi⟩
    | Option.some f =>
      have hL : f.locals = E.ctorFrameLocals c := by
        simp only [Env.ctorFrameLocals, Env.ctorFrame, hd, Option.bind_some, hf]
      let ⟨fromCtor, hc⟩ ← elabCtorBases E c d f hL d.modInvs
      pure ⟨fromCtor ++ fromInherit, fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact hc x hx
        · exact hi x hx⟩

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
        bodies_typed := fun _ _ _ hb => (mem_of_map_val hb).1
        contracts_eq := rfl
        mods_typed := fun _ _ hb => (mem_of_map_val hb).2
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
