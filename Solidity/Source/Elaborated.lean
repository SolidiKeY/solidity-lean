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

**Canonical choice.**  Typing derivations are data and are not unique (a
hexadecimal literal is a constant or a `bytesN`, S01's `litBytes`), so the
elaborated program *is* the choice: an `Elaborated` fixes one derivation per
body, and `Elaborated.bodies_typed` records that each carried body is the
elaboration (`ItemsD.toR`) of a derivation of that body's syntax.  The
semantics (`Solidity/Source/Eval.lean`, `Solidity/Source/Semantics.lean`)
reads only the carried program (`SrcProg`), so a unit's meaning is a
function of its elaboration: two elaborations with the same program have
the same behaviour by construction.  That every *two* derivations of one body elaborate to terms
with the same behaviour is not proved here (see
`docs/feature-work/source-s02.md`, "Uniqueness").
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

/-- **An elaborated unit**: a resolution and its resolved program, each
carried body the elaboration of a typing derivation of its syntax. -/
structure Elaborated where
  res : Resolution
  prog : Program res.env
  bodies_typed : ∀ d ∈ res.unit.decls, ∀ b, prog.body d = some b →
    ∃ f L', d.frame? res.env = some f ∧ ∃ D : ItemsD (f.ctx res.env d.scope) f.locals f.body L',
      b.ps = f.ps ∧ b.rs = f.rs ∧ b.inModifier = f.inModifier ∧ b.locals = tysOf f.locals ∧
      b.out = tysOf L' ∧ HEq b.items D.toR
  contracts_eq : prog.contracts = res.env.contracts

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
