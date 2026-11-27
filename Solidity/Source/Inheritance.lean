import Solidity.Source.WellFormed
import Solidity.Source.Overloads


namespace Solidity.Source


def Decl.fnAttrs (d : Decl) : Option (Bool × Option (List IdPath) × Option Mutability) :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ m _ v o _ _ => Option.some (v, o, m)
  | _, _, _ => Option.none

def Decl.isVirtual (E : Env) (d : Decl) : Bool :=
  (match d.fnAttrs with
   | Option.some (v, _, _) => v
   | Option.none => false) || E.scopeKind d.scope == Option.some .interface

def Decl.overrideList (d : Decl) : Option (List IdPath) :=
  match d.fnAttrs with
  | Option.some (_, o, _) => o
  | Option.none => Option.none

def Decl.mutability (d : Decl) : Option Mutability :=
  match d.fnAttrs with
  | Option.some (_, _, m) => m
  | Option.none => Option.none

def mutOK (base derived : Option Mutability) : Bool :=
  base == derived ||
    (base == Option.none && (derived == Option.some .view || derived == Option.some .pure)) ||
    (base == Option.some .view && derived == Option.some .pure)

def visOK (base derived : Option Visibility) : Bool :=
  base == derived || (base == Option.some .external && derived == Option.some .pub)

mutual

def STy.sameUpToLoc : STy → STy → Bool
  | .bytes _, .bytes _ | .string _, .string _ => true
  | .array _ τ n, .array _ τ' n' => STy.sameUpToLoc τ τ' && n == n'
  | .struct _ d, .struct _ d' => d == d'
  | .mapping k v, .mapping k' v' => STy.sameUpToLoc k k' && STy.sameUpToLoc v v'
  | .tuple ts, .tuple ts' => STy.sameListUpToLoc ts ts'
  | τ, τ' => STy.same τ τ'

def STy.sameListUpToLoc : List STy → List STy → Bool
  | [], [] => true
  | τ :: τs, τ' :: τs' => STy.sameUpToLoc τ τ' && STy.sameListUpToLoc τs τs'
  | _, _ => false

end

def Decl.sameSig (E : Env) (d d' : Decl) : Bool :=
  match d.fnSig E, d'.fnSig E with
  | Option.some (ps, _), Option.some (ps', _) => STy.sameListUpToLoc ps ps'
  | _, _ => false

def Decl.sameRets (E : Env) (d d' : Decl) : Bool :=
  match d.fnSig E, d'.fnSig E with
  | Option.some (_, rs), Option.some (_, rs') => STy.sameListUpToLoc rs rs'
  | _, _ => false

def Decl.saysVirtual (d : Decl) : Bool :=
  match d.fnAttrs with
  | Option.some (v, _, _) => v
  | Option.none => false


def Env.inheritedVersion (E : Env) (B : String) (d : Decl) : Option Decl :=
  (E.chain B).findSome? fun s =>
    (E.declared (Option.some s) d.name).find? fun f =>
      f.kind == .function && !f.isPrivate && f.sameSig E d

def dedupScope (l : List Decl) : List Decl :=
  l.foldl (fun acc d => if acc.any (·.scope == d.scope) then acc else acc ++ [d]) []

def Env.baseFns (E : Env) (c : String) (d : Decl) : List Decl :=
  dedupScope ((E.bases c).filterMap fun B => E.inheritedVersion B d)

def Env.singleIface (E : Env) : List Decl → Bool
  | [f] => E.scopeKind f.scope == Option.some .interface
  | _ => false

def overrideNames (ps : List IdPath) : List String := ps.map IdPath.last

structure FnOverrideOK (E : Env) (c : String) (d : Decl) : Prop where
  missing : E.baseFns c d ≠ [] → E.singleIface (E.baseFns c d) = false → d.overrideList.isSome = true
  nothing : E.baseFns c d = [] → d.overrideList = Option.none
  virtual : ∀ f ∈ E.baseFns c d, f.isVirtual E = true
  listed : 2 ≤ (E.baseFns c d).length → ∀ f ∈ E.baseFns c d, ∃ ps, d.overrideList = Option.some ps ∧
    (f.scope.getD "") ∈ overrideNames ps
  valid : ∀ ps, d.overrideList = Option.some ps → ∀ n ∈ overrideNames ps,
    ∃ f ∈ E.baseFns c d, f.scope = Option.some n
  vis : ∀ f ∈ E.baseFns c d, visOK f.fnVis d.fnVis = true
  mutab : ∀ f ∈ E.baseFns c d, mutOK f.mutability d.mutability = true
  rets : ∀ f ∈ E.baseFns c d, f.sameRets E d = true
  distinct : ∀ ps, d.overrideList = Option.some ps → (overrideNames ps).Nodup
  keepsBody : ∀ f ∈ E.baseFns c d, f.hasBody = true → d.hasBody = true

def Env.contractNames (E : Env) : List String :=
  (E.decls.filter fun d => d.kind == .contract || d.kind == .interface).map (·.name)

def Env.ownFns (E : Env) (c : String) : List Decl :=
  E.decls.filter fun d => d.kind == .function && d.scope == Option.some c

def OverridesOK (E : Env) : Prop :=
  ∀ c ∈ E.contractNames, ∀ d ∈ E.ownFns c, FnOverrideOK E c d


def Env.inheritedFnsAll (E : Env) (c : String) : List Decl :=
  ((E.chain c).drop 1).flatMap fun s =>
    E.decls.filter fun f => f.kind == .function && f.scope == Option.some s && !f.isPrivate

def Env.declaresSig (E : Env) (c : String) (f : Decl) : Bool :=
  (E.ownFns c).any fun d => d.name == f.name && d.sameSig E f

def MustOverride (E : Env) : Prop :=
  ∀ c ∈ E.contractNames, ∀ f ∈ E.inheritedFnsAll c,
    2 ≤ (dedupScope ((E.bases c).filterMap fun B => E.inheritedVersion B f)).length →
      E.declaresSig c f = true


def Env.isAbstract (E : Env) (c : String) : Bool :=
  E.decls.any fun d =>
    d.scope == Option.none && d.name == c &&
      match d.kind, d.top, d.node with
      | .contract, _, .contract abs _ _ _ _ => abs
      | _, _, _ => false

def Env.isContract (E : Env) (c : String) : Bool :=
  E.decls.any fun d => d.scope == Option.none && d.name == c && d.kind == .contract

def Env.finalVersion (E : Env) (c : String) (f : Decl) : Option Decl := E.inheritedVersion c f

structure ImplOK (E : Env) : Prop where
  virtual : ∀ d ∈ E.decls, d.kind = .function → d.top = false → d.hasBody = false →
    E.scopeKind d.scope ≠ Option.some .interface → d.isVirtual E = true
  implemented : ∀ c ∈ E.contractNames, E.isContract c = true → E.isAbstract c = false →
    ∀ f ∈ E.ownFns c ++ E.inheritedFnsAll c, ∀ g, E.finalVersion c f = Option.some g → g.hasBody = true

def VirtualDeclOK (E : Env) : Prop :=
  ∀ d ∈ E.decls, d.kind = .function → d.saysVirtual = true →
    d.isPrivate = false ∧ E.scopeKind d.scope ≠ Option.some .library


def Syn.inheritSpecs : {c : Cat} → Syn c → List (IdPath × Option (Syn .callArgs))
  | _, .cons x xs => x.inheritSpecs ++ xs.inheritSpecs
  | _, .inherit p .none => [(p, Option.none)]
  | _, .inherit p (.some a) => [(p, Option.some a)]
  | _, _ => []

def Syn.modInvs : {c : Cat} → Syn c → List (IdPath × Option (Syn .callArgs))
  | _, .cons x xs => x.modInvs ++ xs.modInvs
  | _, .modInv p .none => [(p, Option.none)]
  | _, .modInv p (.some a) => [(p, Option.some a)]
  | _, _ => []

def Syn.argCount : Syn .callArgs → Option Nat
  | .positional es => Option.some (count es)
  | .named _ => Option.none
where
  count : {c : Cat} → Syn c → Nat
  | _, .cons _ xs => count xs + 1
  | _, _ => 0

def Env.baseSpecs (E : Env) (c : String) : List (IdPath × Option (Syn .callArgs)) :=
  match E.decls.find? (fun d => d.scope == Option.none && d.name == c && d.kind == .contract) with
  | Option.some ⟨.contract, _, _, _, .contract _ _ _ is _⟩ => is.inheritSpecs
  | _ => []

def Env.ctorInvs (E : Env) (c : String) : List (IdPath × Option (Syn .callArgs)) :=
  match E.decls.find? (fun d => d.scope == Option.some c && d.kind == .constructor) with
  | Option.some ⟨.constructor, _, _, _, .constructor _ mods _ _ _⟩ => mods.modInvs
  | _ => []

def Env.ctorArity (E : Env) (c : String) : Nat :=
  match E.decls.find? (fun d => d.scope == Option.some c && d.kind == .constructor) with
  | Option.some ⟨.constructor, _, _, _, .constructor ps _ _ _ _⟩ => (ps.paramNames).length
  | _ => 0

def Env.argsFor (E : Env) (L : List String) (B : String) : List (Syn .callArgs) :=
  L.flatMap fun X =>
    ((E.baseSpecs X ++ E.ctorInvs X).filter fun (p, _) => p.last == B).filterMap (·.2)

structure CtorArgsOK (E : Env) (c : String) : Prop where
  once : ∀ B ∈ (E.chain c).drop 1, 0 < E.ctorArity B → (E.argsFor (E.chain c) B).length ≤ 1
  given : E.isAbstract c = false → ∀ B ∈ (E.chain c).drop 1, 0 < E.ctorArity B →
    (E.argsFor (E.chain c) B).length = 1
  count : ∀ B ∈ (E.chain c).drop 1, ∀ a ∈ E.argsFor [c] B, a.argCount = Option.some (E.ctorArity B)


def Decl.modInvList (d : Decl) : List (IdPath × Option (Syn .callArgs)) :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ _ mods _ _ _ _ => mods.modInvs
  | .constructor, _, .constructor _ mods _ _ _ => mods.modInvs
  | _, _, _ => []

def Decl.modParams (d : Decl) : Nat :=
  match d.kind, d.top, d.node with
  | .modifier, _, .modifier _ (.some ps) _ _ _ => ps.paramNames.length
  | _, _, _ => 0

def invCount : Option (Syn .callArgs) → Option Nat
  | Option.some a => a.argCount
  | Option.none => Option.some 0

def ModInvOK (E : Env) : Prop :=
  ∀ d ∈ E.decls, ∀ inv ∈ d.modInvList, (∃ m, (E.lookupPath d.scope inv.1).filter (·.kind == .modifier) = [m] ∧
      invCount inv.2 = Option.some m.modParams) ∨
    (d.kind = .constructor ∧ inv.2.isSome = true ∧ ∃ c, d.scope = Option.some c ∧ inv.1.last ∈ (E.chain c).drop 1)


def Syn.usingLibs : {c : Cat} → Syn c → List IdPath
  | _, .unit xs => xs.usingLibs
  | _, .cons x xs => x.usingLibs ++ xs.usingLibs
  | _, .topPart p => p.usingLibs
  | _, .contract _ _ _ _ body => body.usingLibs
  | _, .library _ body => body.usingLibs
  | _, .usingPart u => u.usingLibs
  | _, .usingPath l _ _ => [l]
  | _, _ => []

def UsingLibOK (E : Env) (u : Syn .unit) : Prop :=
  ∀ l ∈ u.usingLibs, ∃ d, E.lookupPath Option.none l = [d] ∧ d.kind = .library


def Env.ctorOrder (E : Env) (c : String) : List String := (E.chain c).reverse

def CallableId (E : Env) (d d' : Decl) : Prop :=
  d.kind = .function ∧ d'.kind = .function ∧ d.scope = d'.scope ∧ d.name = d'.name ∧
    d.sameParams E d' = true ∧ d'.sameParams E d = true


inductive C3Lin (E : Env) : String → List String → Prop where
  | mk {c : String} {Ls : List (List String)} {M : List String} :
      Ls.length = (E.bases c).reverse.length →
      (∀ (i : Nat) (b : String) (Lb : List String), (E.bases c).reverse[i]? = Option.some b →
        Ls[i]? = Option.some Lb → C3Lin E b Lb) →
      M.Nodup →
      (∀ l, l ∈ Ls ++ [(E.bases c).reverse] → l.Sublist M) →
      (∀ x, x ∈ M → ∃ l, l ∈ Ls ++ [(E.bases c).reverse] ∧ x ∈ l) →
      C3Lin E c (c :: M)

structure InheritanceOK (r : Resolution) : Prop where
  linearizes : ∀ c ∈ r.env.contractNames, (r.env.linearize c).isSome = true
  overrides : OverridesOK r.env
  mustOverride : MustOverride r.env
  impl : ImplOK r.env
  virtualDecls : VirtualDeclOK r.env
  ctorArgs : ∀ c ∈ r.env.contractNames, r.env.isContract c = true → CtorArgsOK r.env c
  modInvs : ModInvOK r.env
  usingLibs : UsingLibOK r.env r.unit

end Solidity.Source
