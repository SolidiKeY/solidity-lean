import Solidity.Source.Typing
import Solidity.Roadmap.Contracts

/-!
# Settings, resolutions and well-formedness (S01)

The resolved form of a source unit and when it is well formed, the S01
part of G01's `SourceSpec` (`Resolves`, `WellFormed`, the settings fields):

- `Settings`: solc's two pipelines (decision G00 Q4, second round): legacy
  with the pragma's ABI coder, via-IR with coder v2 (`Settings.coder`), and
  the library link map, which must be empty (G05 Q1);
- `Syn.pragmaCoder`: the coder a unit's pragmas select (`pragma abicoder
  v1/v2`, `pragma experimental ABIEncoderV2`; v2 by default);
- `Resolution`: a unit with its environment and the settings it was
  resolved under (`resolve`);
- `WellFormed`: every contract linearizes, no name is declared twice in a
  scope (functions and events may overload), at most one `abicoder`
  pragma, every state variable initializer converts to its type, every
  function body is well typed (`StmtOK`), and no syntax-level exclusion
  (`Syn.rejections`) — the last is the syntax part of the profile, kept as a
  separate conjunct (`InProfileSyntax`).
-/

namespace Solidity.Source

open Solidity.Roadmap (Pipeline AbiCoder Address)

/-! ## Settings -/

/-- Compilation settings: the pipeline, and the library link map. -/
structure Settings where
  pipeline : Pipeline
  links : List (String × Address) := []

/-- The ABI coder a unit's pragmas select (v2 when none does). -/
def Syn.pragmaCoder : Syn .unit → AbiCoder
  | .unit xs => go xs
where
  go : Syn (.list .top) → AbiCoder := fun xs => (coders xs).headD .v2
  /-- The coders the pragmas name, in order. -/
  coders : {c : Cat} → Syn c → List AbiCoder
    | _, .cons x xs => coders x ++ coders xs
    | _, .pragma ["abicoder", "v1"] => [.v1]
    | _, .pragma ["abicoder", "v2"] => [.v2]
    | _, .pragma ["experimental", "ABIEncoderV2"] => [.v2]
    | _, _ => []

/-- The number of `abicoder` pragmas. -/
def Syn.abicoderPragmas : Syn .unit → Nat
  | .unit xs => (Syn.pragmaCoder.coders xs).length

/-- **The coder a unit compiles with**: the pragma's under the legacy
pipeline, v2 under via-IR. -/
def Settings.coder (s : Settings) (u : Syn .unit) : AbiCoder :=
  match s.pipeline with
  | .legacy => u.pragmaCoder
  | .viaIR => .v2

theorem Settings.coder_legacy {s : Settings} (u : Syn .unit) (h : s.pipeline = .legacy) :
    s.coder u = u.pragmaCoder := by
  simp only [Settings.coder, h]

theorem Settings.coder_viaIR {s : Settings} (u : Syn .unit) (h : s.pipeline = .viaIR) :
    s.coder u = .v2 := by
  simp only [Settings.coder, h]

/-! ## Resolutions -/

/-- A resolved source unit: the syntax, its environment and the settings
it was resolved under. -/
structure Resolution where
  unit : Syn .unit
  env : Env
  pipeline : Pipeline
  coder : AbiCoder

/-- The resolution of a unit under settings. -/
def resolveUnit (s : Settings) (u : Syn .unit) : Resolution := ⟨u, u.env, s.pipeline, s.coder u⟩

/-- The relation `SourceSpec.Resolves` reads: the resolution of the unit
under the settings, with an empty link map. -/
def Resolves' (s : Settings) (u : Syn .unit) (r : Resolution) : Prop :=
  s.links = [] ∧ r = resolveUnit s u

theorem Resolves'.unique {s : Settings} {u : Syn .unit} {r r' : Resolution} (h : Resolves' s u r)
    (h' : Resolves' s u r') : r = r' := by
  rw [h.2, h'.2]

/-- A resolution records its settings. -/
theorem resolveUnit_settings (s : Settings) (u : Syn .unit) :
    (resolveUnit s u).pipeline = s.pipeline ∧ (resolveUnit s u).coder = s.coder u := ⟨rfl, rfl⟩

/-! ## Bodies -/

/-- What a body is typed against: the named parameters and returns, their
types, the statements, and the body's `msg.value` and placeholder flags. -/
structure Frame where
  names : List (Option String)
  ps : List STy
  rnames : List (Option String)
  rs : List STy
  body : Syn (.list (.item .body))
  msgValue : Bool
  inModifier : Bool

/-- A frame from parameter and return lists. -/
def Frame.mk? (E : Env) (scope : Option String) (ps rs : Syn (.list .param))
    (body : Syn (.list (.item .body))) (msgValue inModifier : Bool) : Option Frame :=
  match ps.tys E scope .memory, rs.tys E scope .memory with
  | Option.some a, Option.some r =>
    Option.some ⟨ps.paramNames, a, rs.paramNames, r, body, msgValue, inModifier⟩
  | _, _ => Option.none

/-- Whether a function may read `msg.value`: `payable`, `internal` or
`private` (solc refuses it in a non-payable public or external one). -/
def readsValue (vis : Option Visibility) (m : Option Mutability) : Bool :=
  m == Option.some .payable || vis == Option.some .internal || vis == Option.some .priv

/-- Whether a declaration has a body: a function, modifier, constructor,
fallback or receive function with a block. -/
def Decl.hasBody (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ _ _ _ _ _ (.some _) => true
  | .modifier, _, .modifier _ _ _ _ (.some _) => true
  | .constructor, _, .constructor _ _ _ _ _ => true
  | .fallback, _, .fallback _ _ _ _ _ _ (.some _) => true
  | .receive, _, .receive _ _ _ _ _ (.some _) => true
  | _, _, _ => false

/-- **The frame of a body**, when its parameter and return types elaborate. -/
def Decl.frame? (E : Env) (d : Decl) : Option Frame :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ ps vis m _ _ _ rs (.some (.block b)) =>
    Frame.mk? E d.scope ps rs b (readsValue vis m) false
  | .modifier, _, .modifier _ (.some ps) _ _ (.some (.block b)) =>
    Frame.mk? E d.scope ps .nil b true true
  | .modifier, _, .modifier _ .none _ _ (.some (.block b)) =>
    Frame.mk? E d.scope .nil .nil b true true
  | .constructor, _, .constructor ps _ pay _ (.block b) =>
    Frame.mk? E d.scope ps .nil b pay false
  | .fallback, _, .fallback .fbNoParams _ m _ _ _ (.some (.block b)) =>
    Frame.mk? E d.scope .nil .nil b (m == Option.some .payable) false
  | .fallback, _, .fallback (.fbParams p ps rs) _ m _ _ _ (.some (.block b)) =>
    Frame.mk? E d.scope (.cons p ps) rs b (m == Option.some .payable) false
  | .receive, _, .receive _ _ _ _ _ (.some (.block b)) =>
    Frame.mk? E d.scope .nil .nil b true false
  | _, _, _ => Option.none

/-- The locals a body starts with: parameters, then returns (named ones in
scope, which solc does), the last innermost.  An unnamed one keeps its
position under the name `""`, which no identifier resolves to, so a
body's local positions are its arguments' positions. -/
def Frame.locals (f : Frame) : List (String × STy) :=
  ((f.names ++ f.rnames).zip (f.ps ++ f.rs)).map (fun (n, τ) => (n.getD "", τ)) |>.reverse

/-- The context of a body. -/
def Frame.ctx (E : Env) (scope : Option String) (f : Frame) : Ctx :=
  { env := E, scope := scope, locals := [], rets := f.rs, msgValue := f.msgValue,
    inModifier := f.inModifier }

/-- The parameter and return names are distinct. -/
def Frame.distinct (f : Frame) : Prop := ((f.names ++ f.rnames).filterMap id).Nodup

/-! ## Declarations -/

/-- Whether a declaration is a constructor, fallback or receive function:
one of each per contract. -/
def Decl.isSpecial (d : Decl) : Bool :=
  d.kind == .constructor || d.kind == .fallback || d.kind == .receive

/-- Whether two declarations clash: two constructors, fallback or receive
functions of one contract; or the same name in the same scope, unless both
are functions, or both events, with different parameter types. -/
def Decl.clash (E : Env) (d d' : Decl) : Bool :=
  (d.isSpecial && d.kind == d'.kind && d.scope == d'.scope) ||
  d.name != "" && d.name == d'.name && d.scope == d'.scope &&
    (if d.kind == .function && d'.kind == .function then
      match d.fnSig E, d'.fnSig E with
      | Option.some (a, _), Option.some (a', _) => STy.sameList a a'
      | _, _ => true
    else if d.kind == .event && d'.kind == .event then
      match d.paramTys E, d'.paramTys E with
      | Option.some a, Option.some a' => STy.sameList a a'
      | _, _ => true
    else true)

/-- The initializer of a state variable or constant, if any. -/
def Decl.init? (d : Decl) : Option (Syn .expr) :=
  match d.kind, d.top, d.node with
  | .stateVar, _, .stateVar _ _ _ _ _ _ (.some e) => Option.some e
  | .constant, _, .constant _ _ e => Option.some e
  | _, _, _ => Option.none

/-- Whether a declaration is a constant (file-level, or a `constant` state
variable). -/
def Decl.isConst (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .stateVar, _, .stateVar _ _ (Option.some .constant) _ _ _ _ => true
  | .constant, _, _ => true
  | _, _, _ => false

/-- Whether the declared types of a declaration elaborate: a variable's
type, a function's signature, an event's or error's parameters, a struct's
members (in storage, where mappings may occur). -/
def Decl.typesOK (E : Env) (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .stateVar, _, _ | .constant, _, _ => (d.varTy E).isSome
  | .function, _, _ => (d.fnSig E).isSome
  | .event, _, _ | .error, _, _ => (d.paramTys E).isSome
  | .struct, _, .struct _ m ms => (m.tys E d.scope .storage).isSome && (ms.tys E d.scope .storage).isSome
  | _, _, _ => true

/-- The kind of the contract, interface or library a scope names. -/
def Env.scopeKind (E : Env) : Option String → Option DeclKind
  | Option.none => Option.none
  | Option.some c => (E.decls.find? fun d => d.scope == Option.none && d.name == c &&
      (d.kind == .contract || d.kind == .interface || d.kind == .library)).map (·.kind)

/-- Whether a `receive` function is `external payable`. -/
def Decl.receiveOK (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .receive, _, .receive ext pay _ _ _ _ => ext && pay
  | _, _, _ => true

/-- solc's placement rules: a free function has no visibility and a body; a
contract function has a visibility; an interface function is `external`
and has no body; an interface has no modifiers, constructors or state
variables; a library no constructor, `receive`, `fallback` or non-constant
state variable; `receive` is `external payable`. -/
def Decl.placementOK (E : Env) (d : Decl) : Bool :=
  let k := E.scopeKind d.scope
  match d.kind with
  | .function =>
    if d.top then d.fnVis.isNone && d.hasBody
    else if k == Option.some .interface then
      d.fnVis == Option.some .external && !d.hasBody
    else d.fnVis.isSome
  | .modifier => k != Option.some .interface
  | .constructor => k != Option.some .interface && k != Option.some .library
  | .stateVar => k != Option.some .interface && (k != Option.some .library || d.isConst)
  | .receive => k != Option.some .library && d.receiveOK
  | .fallback => k != Option.some .library
  | _ => true

/-! ## Pragmas -/

/-- The pragmas of a unit, their words in order. -/
def Syn.pragmas : {c : Cat} → Syn c → List (List String)
  | _, .unit xs => Syn.pragmas xs
  | _, .cons x xs => Syn.pragmas x ++ Syn.pragmas xs
  | _, .pragma ws => [ws]
  | _, _ => []

/-- The admitted pragmas: a version, an ABI coder, `experimental
ABIEncoderV2`. -/
def knownPragma : List String → Bool
  | "solidity" :: _ => true
  | ["abicoder", "v1"] | ["abicoder", "v2"] | ["experimental", "ABIEncoderV2"] => true
  | _ => false

/-! ## Well-formedness -/

/-- The context of a state variable's or constant's initializer. -/
def Ctx.forInit (E : Env) (scope : Option String) : Ctx := { env := E, scope := scope, locals := [] }

/-- **Well-formedness** of a resolved unit. -/
structure WellFormed (r : Resolution) : Prop where
  /-- Every base is an earlier contract or interface. -/
  bases : r.env.basesOK = true
  linearizes : ∀ d ∈ r.unit.decls, d.kind = .contract ∨ d.kind = .interface →
    (r.env.linearize d.name).isSome
  /-- No two declarations clash (pairwise over the list, so a duplicate
  clashes too). -/
  noClash : r.unit.decls.Pairwise fun d d' => d.clash r.env d' = false
  pragmas : ∀ ws ∈ r.unit.pragmas, knownPragma ws = true
  oneCoder : r.unit.abicoderPragmas ≤ 1
  types : ∀ d ∈ r.unit.decls, d.typesOK r.env = true
  placement : ∀ d ∈ r.unit.decls, d.placementOK r.env = true
  /-- A constant has an initializer. -/
  constInit : ∀ d ∈ r.unit.decls, d.isConst = true → d.init?.isSome
  inits : ∀ d ∈ r.unit.decls, ∀ e, d.init? = Option.some e → ∃ τ σ, d.varTy r.env = Option.some τ ∧
    HasType (Ctx.forInit r.env d.scope) e σ ∧ σ.implicit (Ctx.forInit r.env d.scope).isBase τ = true
  /-- Every body's frame elaborates, its names are distinct, and its
  statements are well typed. -/
  bodies : ∀ d ∈ r.unit.decls, d.hasBody = true → ∃ f L', d.frame? r.env = Option.some f ∧
    f.distinct ∧ ItemsOK (f.ctx r.env d.scope) f.locals f.body L'

/-- The syntax part of the profile: no syntax-level exclusion. -/
def InProfileSyntax (r : Resolution) : Prop := r.unit.rejections = []

end Solidity.Source
