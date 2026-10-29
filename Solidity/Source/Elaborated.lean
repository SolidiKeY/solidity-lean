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
(`RInit.Derived`), modifier invocations and base arguments
(`RConvArgs.Derived`) are tied to derivations too; `elaborate`
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

/-- Converted arguments elaborated from a derivation of an argument list, in
a context whose environment is `E` and whose locals have types `Γ`. -/
def RConvArgs.Derived (E : Env) (Γ : RCtx) (ps : List STy) (args : RConvArgs E Γ ps) : Prop :=
  ∃ (C : Ctx) (es : Syn (.list .expr)) (σs : List STy) (D : TypedArgs C es σs)
    (h : argsFit C.env.isBase σs ps = true), C.env = E ∧ C.tys = Γ ∧ HEq args (RArgs.convert ps D.toR h)

/-- An initializer elaborated from a derivation of the variable's
initializer, converted implicitly to its type. -/
def RInit.Derived (E : Env) (i : RInit E) : Prop :=
  ∃ (e : Syn .expr) (σ : STy) (D : Typed (Ctx.forInit E i.var.scope) e σ)
    (h : σ.implicit E.isBase i.τ = true), i.var.init? = some e ∧ i.e = .conv D.toR (.inl h)

/-- A body elaborated from a derivation of a declaration's body in its
frame, its modifier invocations from derivations of their arguments. -/
def RBody.Derived (E : Env) (d : Decl) (b : RBody E) : Prop :=
  (∃ f L', d.frame? E = some f ∧ ∃ D : ItemsD (f.ctx E d.scope) f.locals f.body L',
    b.ps = f.ps ∧ b.rs = f.rs ∧ b.inModifier = f.inModifier ∧ b.locals = tysOf f.locals ∧
    b.out = tysOf L' ∧ HEq b.items D.toR) ∧
  ∀ m ∈ b.mods, RConvArgs.Derived E b.locals m.ps m.args

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
  /-- Each body's modifier invocations come from typed arguments. -/
  mods_typed : ∀ d b, prog.body d = some b → ∀ m ∈ b.mods, RConvArgs.Derived res.env b.locals m.ps m.args
  /-- A contract's constructor is the body of its constructor declaration. -/
  ctor_typed : ∀ c b, prog.ctor c = some b → ∃ d ∈ res.env.decls,
    d.kind = .constructor ∧ d.scope = some c ∧ prog.body d = some b
  /-- A constant's value is its initializer's elaboration. -/
  consts_typed : ∀ d i, prog.consts d = some i → i.var = d ∧ RInit.Derived res.env i
  /-- A contract's initializers are its own variables', elaborated. -/
  inits_typed : ∀ c, ∀ i ∈ prog.inits c, i.var.scope = some c ∧ RInit.Derived res.env i
  /-- Base-constructor arguments come from typed arguments in the
  constructor's locals. -/
  baseArgs_typed : ∀ c, ∀ a ∈ prog.baseArgs c, RConvArgs.Derived res.env (prog.ctorLocals c) a.ps a.args

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
