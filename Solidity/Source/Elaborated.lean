import Solidity.Source.WellFormed
import Solidity.Source.Resolved

/-!
# Elaborated units: resolutions carrying their resolved bodies (S02 prerequisite)

S01's `Resolution` is a unit, its environment and its settings; a typing
derivation of each body exists (`WellFormed.bodies`) but is not part of it.
S02's semantics is given on resolved terms, so it needs the terms
themselves.  `Elaborated` is a resolution together with a `Program`:

- every body (function, modifier, constructor, `receive`, `fallback`) as a
  resolved block `RItems` in its frame (`RBody`), with the function's
  modifier invocations resolved against its parameters (`RModInv`);
- every state variable initializer as a resolved expression at the
  variable's type (`RInit`), per contract in declaration order;
- every constructor's base-constructor arguments, resolved in that
  constructor's parameters (`RBaseArg`).

**Choice and uniqueness.**  Typing derivations are data and are not unique
(`(1)` is `const` or `paren (const …)`), so an `Elaborated` fixes one
derivation per body, and `Elaborated.bodies_typed` records that each
carried body is the elaboration (`ItemsD.toR`) of a derivation of that
body's syntax.  The semantics (`Solidity/Source/Eval.lean`,
`Solidity/Source/Semantics.lean`) reads only the carried program
(`SrcProg`).  The choice does not matter: any two derivations of one body
elaborate to one `RBody` (`RBody.ofDerivation_unique`,
`Solidity/Source/Unique.lean`).  Initializers and constants
(`RInit.Derived`), modifier invocations (`RModInv.Derived`) and base
arguments (`RBaseArg.Derived`) are tied to their syntax and derivations
too (soundness: what is carried was written; not completeness); `elaborate`
(`Solidity/Source/Elaborate.lean`) builds an `Elaborated` from a resolution.
-/

namespace Solidity.Source

/-- A resolved modifier invocation of a body whose locals are `Γ`: the
modifier and its arguments, converted to its parameters. -/
structure RModInv (E : Env) (Γ : RCtx) where
  modifier : Decl
  ps : List STy
  args : RConvArgs E Γ ps

/-- **A resolved body**: its parameter and return types, its initial locals
(parameters then returns, innermost first: `Frame.locals`), its items and
its modifier invocations (outermost first). -/
structure RBody (E : Env) where
  ps : List STy
  rs : List STy
  inModifier : Bool
  locals : RCtx
  out : RCtx
  items : RItems E rs inModifier .body locals out
  mods : List (RModInv E locals) := []

/-- A resolved state variable initializer, at the variable's type. -/
structure RInit (E : Env) where
  var : Decl
  τ : STy
  hτ : var.varTy E = some τ
  e : RExpr E [] τ

/-- The arguments a constructor passes to a base constructor, resolved in
its own parameters `Γ` (`is B(5)` and `constructor(…) B(x)` alike). -/
structure RBaseArg (E : Env) (Γ : RCtx) where
  base : String
  ps : List STy
  args : RConvArgs E Γ ps

/-- **A resolved program** over environment `E`. -/
structure Program (E : Env) where
  /-- The body of each declaration that has one. -/
  body : Decl → Option (RBody E)
  /-- The value of each constant (file-level or `constant` state variable). -/
  consts : Decl → Option (RInit E)
  /-- Each contract's state variable initializers, in declaration order. -/
  inits : String → List (RInit E)
  /-- Each contract's constructor, if it declares one. -/
  ctor : String → Option (RBody E)
  /-- The locals of a contract's constructor (`[]` without one). -/
  ctorLocals : String → RCtx
  /-- The base-constructor arguments each contract gives. -/
  baseArgs : (c : String) → List (RBaseArg E (ctorLocals c))
  /-- The contracts of the compilation input, by position (G01 `Event.create`). -/
  contracts : List String

/-- The contracts of an environment, in declaration order. -/
def Env.contracts (E : Env) : List String :=
  (E.decls.filter fun d => d.kind == .contract && d.scope == none).map (·.name)

/-! ### Where invocations are written -/

/-- The modifier invocations of a body. -/
def Decl.modInvs (d : Decl) : Syn (.list .modInv) :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ _ ms _ _ _ _ => ms
  | .constructor, _, .constructor _ ms _ _ _ => ms
  | .fallback, _, .fallback _ _ _ ms _ _ _ => ms
  | .receive, _, .receive _ _ ms _ _ _ => ms
  | _, _, _ => .nil

/-- The invocations of a list: each name and its arguments. -/
def Syn.invList : Syn (.list .modInv) → List (IdPath × Syn (.opt .callArgs))
  | .nil => []
  | .cons (.modInv p a) rest => (p, a) :: rest.invList

/-- The entries of an inheritance list: each base and its arguments. -/
def Syn.inheritList : Syn (.list .inherit) → List (IdPath × Syn (.opt .callArgs))
  | .nil => []
  | .cons (.inherit p a) rest => (p, a) :: rest.inheritList

/-- An invocation's positional arguments (none written: none). -/
def invArgs : Syn (.opt .callArgs) → Option (Syn (.list .expr))
  | .none => Option.some .nil
  | .some (.positional es) => Option.some es
  | _ => Option.none

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

/-- The modifier a path names, with its parameter types (from its header,
so a `virtual` modifier without a body is named too). -/
def Env.modifierAt (E : Env) (scope : Option String) (p : IdPath) : Option (Decl × List STy) :=
  match E.lookupPath scope p with
  | [m] =>
    match m.kind, m.top, m.node with
    | .modifier, _, .modifier _ (.some ps) _ _ _ => (ps.tys E m.scope .memory).map fun τs => (m, τs)
    | .modifier, _, .modifier _ .none _ _ _ => Option.some (m, [])
    | _, _, _ => Option.none
  | _ => Option.none

/-- The contract a path names. -/
def Env.contractAt (E : Env) (scope : Option String) (p : IdPath) : Option String :=
  match E.lookupPath scope p with
  | [b] => if b.kind == .contract then Option.some b.name else Option.none
  | _ => Option.none

/-- The inheritance list of contract `c`. -/
def Env.inheritOf (E : Env) (c : String) : Syn (.list .inherit) :=
  match E.decls.find? fun d => d.kind == .contract && d.name == c && d.scope == Option.none with
  | Option.some d =>
    match d.kind, d.top, d.node with
    | .contract, _, .contract _ _ _ is _ => is
    | _, _, _ => .nil
  | Option.none => .nil

/-- Locals unnamed: in the context of `is B(args)` the constructor's locals
occupy the frame but no name resolves to them. -/
def anonLocals (L : List (String × STy)) : List (String × STy) := L.map fun p => ("", p.2)

/-- The context of contract `c`'s inheritance-list arguments. -/
def Env.inheritCtx (E : Env) (c : String) : Ctx :=
  { env := E, scope := Option.some c, locals := anonLocals (E.ctorFrameLocals c) }

/-! ### Coherence of the parts -/

/-- Converted arguments that are the elaboration of a derivation of the
argument list `es` in context `C`, converted to the parameters `ps`. -/
def RConvArgs.DerivedIn (C : Ctx) (es : Syn (.list .expr)) {Γ : RCtx} (ps : List STy)
    (args : RConvArgs C.env Γ ps) : Prop :=
  ∃ (σs : List STy) (D : TypedArgs C es σs) (h : argsFit C.env.isBase σs ps = true),
    HEq args (RArgs.convert ps D.toR h)

/-- An initializer elaborated from a derivation of the variable's
initializer, converted implicitly to its type. -/
def RInit.Derived (E : Env) (i : RInit E) : Prop :=
  ∃ (e : Syn .expr) (σ : STy) (D : Typed (Ctx.forInit E i.var.scope) e σ)
    (h : σ.implicit E.isBase i.τ = true), i.var.init? = some e ∧ i.e = .conv D.toR (.inl h)

/-- A modifier invocation of declaration `d` (frame `f`): written in `d`'s
invocations, naming the modifier it carries with that modifier's
parameters, its arguments elaborated from a derivation of the written ones
in `d`'s parameters. -/
def RModInv.Derived (E : Env) (d : Decl) (f : Frame) {Γ : RCtx} (m : RModInv E Γ) : Prop :=
  ∃ p a es, (p, a) ∈ d.modInvs.invList ∧ E.modifierAt d.scope p = some (m.modifier, m.ps) ∧
    invArgs a = some es ∧ RConvArgs.DerivedIn ((f.ctx E d.scope).at f.locals) es m.ps m.args

/-- A body elaborated from a derivation of a declaration's body in its
frame, each modifier invocation from one written in its header. -/
def RBody.Derived (E : Env) (d : Decl) (b : RBody E) : Prop :=
  ∃ f L', d.frame? E = some f ∧ (∃ D : ItemsD (f.ctx E d.scope) f.locals f.body L',
    b.ps = f.ps ∧ b.rs = f.rs ∧ b.inModifier = f.inModifier ∧ b.locals = tysOf f.locals ∧
    b.out = tysOf L' ∧ HEq b.items D.toR) ∧
  ∀ m ∈ b.mods, RModInv.Derived E d f m

/-- A base-constructor argument of contract `c`: written in `c`'s
inheritance list (typed with the constructor's locals unnamed) or among its
constructor's invocations (typed in its parameters), naming a contract, at
that contract's constructor parameters. -/
def RBaseArg.Derived (E : Env) (c : String) {Γ : RCtx} (a : RBaseArg E Γ) : Prop :=
  a.ps = E.ctorParams a.base ∧
  ((∃ p es, (p, Syn.some (.positional es)) ∈ (E.inheritOf c).inheritList ∧
      E.contractAt Option.none p = some a.base ∧ RConvArgs.DerivedIn (E.inheritCtx c) es a.ps a.args) ∨
   (∃ d f p args es, E.ctorDecl c = some d ∧ d.frame? E = some f ∧ (p, args) ∈ d.modInvs.invList ∧
      E.contractAt d.scope p = some a.base ∧ invArgs args = some es ∧
      RConvArgs.DerivedIn ((f.ctx E d.scope).at f.locals) es a.ps a.args))

/-- **An elaborated unit**: a resolution and its resolved program, each
carried body, initializer, constant, modifier invocation and base argument
the elaboration of a typing derivation of its syntax. -/
structure Elaborated where
  res : Resolution
  prog : Program res.env
  bodies_typed : ∀ d ∈ res.unit.decls, ∀ b, prog.body d = some b →
    ∃ f L', d.frame? res.env = some f ∧ ∃ D : ItemsD (f.ctx res.env d.scope) f.locals f.body L',
      b.ps = f.ps ∧ b.rs = f.rs ∧ b.inModifier = f.inModifier ∧ b.locals = tysOf f.locals ∧
      b.out = tysOf L' ∧ HEq b.items D.toR
  contracts_eq : prog.contracts = res.env.contracts
  /-- Each body's modifier invocations are written ones, typed. -/
  mods_typed : ∀ d b, prog.body d = some b → ∃ f, d.frame? res.env = some f ∧
    ∀ m ∈ b.mods, RModInv.Derived res.env d f m
  /-- A contract's constructor is the body of its constructor declaration. -/
  ctor_typed : ∀ c b, prog.ctor c = some b → ∃ d ∈ res.env.decls,
    d.kind = .constructor ∧ d.scope = some c ∧ prog.body d = some b
  /-- A constant's value is its initializer's elaboration. -/
  consts_typed : ∀ d i, prog.consts d = some i → i.var = d ∧ RInit.Derived res.env i
  /-- A contract's initializers are its own variables', elaborated. -/
  inits_typed : ∀ c, ∀ i ∈ prog.inits c, i.var.scope = some c ∧ RInit.Derived res.env i
  /-- Base-constructor arguments are written ones, typed. -/
  baseArgs_typed : ∀ c, ∀ a ∈ prog.baseArgs c, RBaseArg.Derived res.env c a

/-- A body elaborated from a derivation, in its frame. -/
def RBody.ofDerivation {E : Env} {scope : Option String} (f : Frame) {L' : List (String × STy)}
    (D : ItemsD (f.ctx E scope) f.locals f.body L') (mods : List (RModInv E (tysOf f.locals)) := []) :
    RBody E :=
  ⟨f.ps, f.rs, f.inModifier, tysOf f.locals, tysOf L', D.toR, mods⟩

/-- A derivation's body satisfies the coherence `Elaborated` asks. -/
theorem RBody.ofDerivation_typed {E : Env} {scope : Option String} (f : Frame) {L' : List (String × STy)}
    (D : ItemsD (f.ctx E scope) f.locals f.body L') (mods : List (RModInv E (tysOf f.locals))) :
    let b := RBody.ofDerivation f D mods
    b.ps = f.ps ∧ b.rs = f.rs ∧ b.inModifier = f.inModifier ∧ b.locals = tysOf f.locals ∧
      b.out = tysOf L' ∧ HEq b.items D.toR :=
  ⟨rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩

end Solidity.Source
