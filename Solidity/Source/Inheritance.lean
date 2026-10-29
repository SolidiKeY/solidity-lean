import Solidity.Source.WellFormed
import Solidity.Source.Overloads

/-!
# Inheritance checks (G14)

The relations of solc 0.8.38's `ContractLevelChecker`/`OverrideChecker` and
`NameAndTypeResolver` for one source unit, over S01's environment and C3
linearization (`Env.linearize`, `Env.chain`).  S01 checks none of them
("What S01 does not do": override, `virtual`, visibility of overriding
functions, modifier invocations, base-constructor arguments, unimplemented
functions in non-abstract contracts, `using for`).  Each field names the
solc error it is.

- **Base functions** (`Env.baseFns E c d`): for each direct base `B` of the
  contract `c` declaring `d`, the most derived function of `B`'s
  linearization with `d`'s name and parameter types (not `private`), one
  per declaring contract.
- **Overrides** (`FnOverrideOK`): a function with base functions says
  `override` (9456), one without does not (7792); every base function is
  `virtual` (4334; interface functions are implicitly virtual); with two or
  more base contracts the `override(…)` list names exactly them (4327,
  2353); visibility is kept, or `external` becomes `public` (9098);
  mutability only becomes stricter (6959); return types are kept (4822).
- **Required overrides** (`MustOverride`, 6480): two direct bases with
  different most derived functions of one signature force the contract to
  declare it.
- **Abstractness** (`ImplOK`): a function without body is `virtual` (5424),
  and a non-abstract contract implements every function it inherits (3656).
- **Base constructors** (`CtorArgsOK`): for every base in the
  linearization whose constructor has parameters, arguments are given at
  most once along the linearization (3364), exactly once unless the contract
  is abstract (3415), with the right count (7927, 2973).
- **Modifier invocations** (`ModInvOK`, 4659): each invocation of a
  function or constructor names a modifier visible in the contract, or (in a
  constructor) a base contract, with as many arguments as parameters (2973).
- **`using L for T`** (`UsingLibOK`, 4357): `L` is a library.
- **Constructor order** (`Env.ctorOrder`): the linearization reversed, most
  base first.
- **Callable identity** (`CallableId`): a function is identified by its
  contract, name and parameter types; in a `WellFormed` unit the identity
  determines the declaration (`Solidity/Frontend/Static/Inheritance.lean`).
-/

namespace Solidity.Source

/-! ## Function attributes -/

/-- `virtual`, the `override` list and the mutability of a function. -/
def Decl.fnAttrs (d : Decl) : Option (Bool × Option (List IdPath) × Option Mutability) :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ m _ v o _ _ => Option.some (v, o, m)
  | _, _, _ => Option.none

/-- Whether a function is `virtual`, explicitly or as an interface function. -/
def Decl.isVirtual (E : Env) (d : Decl) : Bool :=
  (match d.fnAttrs with
   | Option.some (v, _, _) => v
   | Option.none => false) || E.scopeKind d.scope == Option.some .interface

/-- The `override` list of a function: `none` without `override`. -/
def Decl.overrideList (d : Decl) : Option (List IdPath) :=
  match d.fnAttrs with
  | Option.some (_, o, _) => o
  | Option.none => Option.none

/-- The mutability of a function (`none` is non-payable). -/
def Decl.mutability (d : Decl) : Option Mutability :=
  match d.fnAttrs with
  | Option.some (_, _, m) => m
  | Option.none => Option.none

/-- solc's mutability rule for overriding: equal, or stricter
(non-payable to `view` or `pure`, `view` to `pure`). -/
def mutOK (base derived : Option Mutability) : Bool :=
  base == derived ||
    (base == Option.none && (derived == Option.some .view || derived == Option.some .pure)) ||
    (base == Option.some .view && derived == Option.some .pure)

/-- solc's visibility rule for overriding: equal, or `external` to `public`. -/
def visOK (base derived : Option Visibility) : Bool :=
  base == derived || (base == Option.some .external && derived == Option.some .pub)

/-- Two functions have the same return types. -/
def Decl.sameRets (E : Env) (d d' : Decl) : Bool :=
  match d.fnSig E, d'.fnSig E with
  | Option.some (_, rs), Option.some (_, rs') => STy.sameList rs rs'
  | _, _ => false

/-! ## Base functions -/

/-- The most derived function of `B`'s linearization with `d`'s name and
parameter types, not `private`. -/
def Env.inheritedVersion (E : Env) (B : String) (d : Decl) : Option Decl :=
  (E.chain B).findSome? fun s =>
    (E.declared (Option.some s) d.name).find? fun f =>
      f.kind == .function && !f.isPrivate && f.sameParams E d

/-- Keep the first function of each declaring contract. -/
def dedupScope (l : List Decl) : List Decl :=
  l.foldl (fun acc d => if acc.any (·.scope == d.scope) then acc else acc ++ [d]) []

/-- **The base functions** of `d` in contract `c`: one per declaring
contract, over the direct bases. -/
def Env.baseFns (E : Env) (c : String) (d : Decl) : List Decl :=
  dedupScope ((E.bases c).filterMap fun B => E.inheritedVersion B d)

/-- The contract names an `override(…)` list gives. -/
def overrideNames (ps : List IdPath) : List String := ps.map IdPath.last

/-- **Override rules** for a function `d` declared in contract `c`. -/
structure FnOverrideOK (E : Env) (c : String) (d : Decl) : Prop where
  /-- 9456: "Overriding function is missing 'override' specifier." -/
  missing : E.baseFns c d ≠ [] → d.overrideList.isSome = true
  /-- 7792: "Function has override specified but does not override anything." -/
  nothing : E.baseFns c d = [] → d.overrideList = Option.none
  /-- 4334: "Trying to override non-virtual function." -/
  virtual : ∀ f ∈ E.baseFns c d, f.isVirtual E = true
  /-- 4327: "Function needs to specify overridden contracts". -/
  listed : 2 ≤ (E.baseFns c d).length → ∀ f ∈ E.baseFns c d, ∃ ps, d.overrideList = Option.some ps ∧
    (f.scope.getD "") ∈ overrideNames ps
  /-- 2353: "Invalid contract specified in override list". -/
  valid : ∀ ps, d.overrideList = Option.some ps → ∀ n ∈ overrideNames ps,
    ∃ f ∈ E.baseFns c d, f.scope = Option.some n
  /-- 9098: "Overriding function visibility differs." -/
  vis : ∀ f ∈ E.baseFns c d, visOK f.fnVis d.fnVis = true
  /-- 6959: "Overriding function changes state mutability". -/
  mutab : ∀ f ∈ E.baseFns c d, mutOK f.mutability d.mutability = true
  /-- 4822: "Overriding function return types differ." -/
  rets : ∀ f ∈ E.baseFns c d, f.sameRets E d = true

/-- The contracts and interfaces of a unit, by name. -/
def Env.contractNames (E : Env) : List String :=
  (E.decls.filter fun d => d.kind == .contract || d.kind == .interface).map (·.name)

/-- The functions declared in a contract (not constructors, fallback or
receive). -/
def Env.ownFns (E : Env) (c : String) : List Decl :=
  E.decls.filter fun d => d.kind == .function && d.scope == Option.some c

/-- **Every function overrides correctly.** -/
def OverridesOK (E : Env) : Prop :=
  ∀ c ∈ E.contractNames, ∀ d ∈ E.ownFns c, FnOverrideOK E c d

/-! ## Required overrides -/

/-- The functions a contract inherits, by signature: every visible function
of a strict base (its linearization without itself). -/
def Env.inheritedFnsAll (E : Env) (c : String) : List Decl :=
  ((E.chain c).drop 1).flatMap fun s =>
    E.decls.filter fun f => f.kind == .function && f.scope == Option.some s && !f.isPrivate

/-- Whether contract `c` declares a function with `f`'s name and parameter
types. -/
def Env.declaresSig (E : Env) (c : String) (f : Decl) : Bool :=
  (E.ownFns c).any fun d => d.name == f.name && d.sameParams E f

/-- **Required overrides** (6480): when two direct bases have different
most derived versions (by declaring contract) of a signature, the contract
declares it. -/
def MustOverride (E : Env) : Prop :=
  ∀ c ∈ E.contractNames, ∀ f ∈ E.inheritedFnsAll c,
    2 ≤ (dedupScope ((E.bases c).filterMap fun B => E.inheritedVersion B f)).length →
      E.declaresSig c f = true

/-! ## Abstractness -/

/-- Whether a contract is declared `abstract`. -/
def Env.isAbstract (E : Env) (c : String) : Bool :=
  E.decls.any fun d =>
    d.scope == Option.none && d.name == c &&
      match d.kind, d.top, d.node with
      | .contract, _, .contract abs _ _ _ _ => abs
      | _, _, _ => false

/-- Whether a contract is a `contract` (not an interface or library). -/
def Env.isContract (E : Env) (c : String) : Bool :=
  E.decls.any fun d => d.scope == Option.none && d.name == c && d.kind == .contract

/-- The most derived version of `f` visible in `c`. -/
def Env.finalVersion (E : Env) (c : String) (f : Decl) : Option Decl := E.inheritedVersion c f

/-- **Implementation rules**: a function without body outside interfaces is
`virtual` (5424); a non-abstract contract's most derived version of every
function it has is implemented (3656). -/
structure ImplOK (E : Env) : Prop where
  virtual : ∀ d ∈ E.decls, d.kind = .function → d.top = false → d.hasBody = false →
    E.scopeKind d.scope ≠ Option.some .interface → d.isVirtual E = true
  implemented : ∀ c ∈ E.contractNames, E.isContract c = true → E.isAbstract c = false →
    ∀ f ∈ E.ownFns c ++ E.inheritedFnsAll c, ∀ g, E.finalVersion c f = Option.some g → g.hasBody = true

/-! ## Base constructor arguments -/

/-- The base specifiers of a contract: each base path with its arguments. -/
def Syn.inheritSpecs : {c : Cat} → Syn c → List (IdPath × Option (Syn .callArgs))
  | _, .cons x xs => x.inheritSpecs ++ xs.inheritSpecs
  | _, .inherit p .none => [(p, Option.none)]
  | _, .inherit p (.some a) => [(p, Option.some a)]
  | _, _ => []

/-- The modifier invocations of a list. -/
def Syn.modInvs : {c : Cat} → Syn c → List (IdPath × Option (Syn .callArgs))
  | _, .cons x xs => x.modInvs ++ xs.modInvs
  | _, .modInv p .none => [(p, Option.none)]
  | _, .modInv p (.some a) => [(p, Option.some a)]
  | _, _ => []

/-- The number of positional arguments. -/
def Syn.argCount : Syn .callArgs → Option Nat
  | .positional es => Option.some (count es)
  | .named _ => Option.none
where
  count : {c : Cat} → Syn c → Nat
  | _, .cons _ xs => count xs + 1
  | _, _ => 0

/-- A contract's base specifiers. -/
def Env.baseSpecs (E : Env) (c : String) : List (IdPath × Option (Syn .callArgs)) :=
  match E.decls.find? (fun d => d.scope == Option.none && d.name == c && d.kind == .contract) with
  | Option.some ⟨.contract, _, _, _, .contract _ _ _ is _⟩ => is.inheritSpecs
  | _ => []

/-- A contract's constructor's modifier invocations. -/
def Env.ctorInvs (E : Env) (c : String) : List (IdPath × Option (Syn .callArgs)) :=
  match E.decls.find? (fun d => d.scope == Option.some c && d.kind == .constructor) with
  | Option.some ⟨.constructor, _, _, _, .constructor _ mods _ _ _⟩ => mods.modInvs
  | _ => []

/-- The number of parameters of a contract's constructor (`0` without one). -/
def Env.ctorParams (E : Env) (c : String) : Nat :=
  match E.decls.find? (fun d => d.scope == Option.some c && d.kind == .constructor) with
  | Option.some ⟨.constructor, _, _, _, .constructor ps _ _ _ _⟩ => (ps.paramNames).length
  | _ => 0

/-- The argument lists given for base `B` along a linearization `L`: in
`is` specifiers and constructor modifier invocations. -/
def Env.argsFor (E : Env) (L : List String) (B : String) : List (Syn .callArgs) :=
  L.flatMap fun X =>
    ((E.baseSpecs X ++ E.ctorInvs X).filter fun (p, _) => p.last == B).filterMap (·.2)

/-- **Base constructor arguments** of contract `c`. -/
structure CtorArgsOK (E : Env) (c : String) : Prop where
  /-- 3364: "Base constructor arguments given twice." -/
  once : ∀ B ∈ (E.chain c).drop 1, 0 < E.ctorParams B → (E.argsFor (E.chain c) B).length ≤ 1
  /-- 3415: "No arguments passed to the base constructor." -/
  given : E.isAbstract c = false → ∀ B ∈ (E.chain c).drop 1, 0 < E.ctorParams B →
    (E.argsFor (E.chain c) B).length = 1
  /-- 7927, 2973: wrong argument count. -/
  count : ∀ B ∈ (E.chain c).drop 1, ∀ a ∈ E.argsFor [c] B, a.argCount = Option.some (E.ctorParams B)

/-! ## Modifier invocations -/

/-- The modifier invocations of a function's or constructor's declaration. -/
def Decl.modInvs (d : Decl) : List (IdPath × Option (Syn .callArgs)) :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ _ mods _ _ _ _ => mods.modInvs
  | .constructor, _, .constructor _ mods _ _ _ => mods.modInvs
  | _, _, _ => []

/-- The number of parameters of a modifier. -/
def Decl.modParams (d : Decl) : Nat :=
  match d.kind, d.top, d.node with
  | .modifier, _, .modifier _ (.some ps) _ _ _ => ps.paramNames.length
  | _, _, _ => 0

/-- **Modifier invocations** (4659, 2973): every invocation names a
modifier visible in the contract with as many arguments as parameters, or,
in a constructor, a base contract (whose arguments `CtorArgsOK` checks). -/
def ModInvOK (E : Env) : Prop :=
  ∀ d ∈ E.decls, ∀ inv ∈ d.modInvs, (∃ m, (E.lookupPath d.scope inv.1).filter (·.kind == .modifier) = [m] ∧
      ∀ a, inv.2 = Option.some a → a.argCount = Option.some m.modParams) ∨
    (d.kind = .constructor ∧ ∃ c, d.scope = Option.some c ∧ inv.1.last ∈ (E.chain c).drop 1)

/-! ## `using for` -/

/-- The library paths of `using L for …` directives in a tree. -/
def Syn.usingLibs : {c : Cat} → Syn c → List IdPath
  | _, .unit xs => xs.usingLibs
  | _, .cons x xs => x.usingLibs ++ xs.usingLibs
  | _, .topPart p => p.usingLibs
  | _, .contract _ _ _ _ body => body.usingLibs
  | _, .library _ body => body.usingLibs
  | _, .usingPart u => u.usingLibs
  | _, .usingPath l _ _ => [l]
  | _, _ => []

/-- **`using L for T`** (4357): `L` names a library. -/
def UsingLibOK (E : Env) (u : Syn .unit) : Prop :=
  ∀ l ∈ u.usingLibs, ∃ d, E.lookupPath Option.none l = [d] ∧ d.kind = .library

/-! ## Constructor order and callable identity -/

/-- **Constructor order**: the linearization reversed, most base first. -/
def Env.ctorOrder (E : Env) (c : String) : List String := (E.chain c).reverse

/-- A callable's identity: its contract, name and parameter types. -/
def CallableId (E : Env) (d d' : Decl) : Prop :=
  d.kind = .function ∧ d'.kind = .function ∧ d.scope = d'.scope ∧ d.name = d'.name ∧
    d.sameParams E d' = true ∧ d'.sameParams E d = true

/-- **G14's inheritance judgment** of a unit. -/
structure InheritanceOK (r : Resolution) : Prop where
  overrides : OverridesOK r.env
  mustOverride : MustOverride r.env
  impl : ImplOK r.env
  ctorArgs : ∀ c ∈ r.env.contractNames, r.env.isContract c = true → CtorArgsOK r.env c
  modInvs : ModInvOK r.env
  usingLibs : UsingLibOK r.env r.unit

end Solidity.Source
