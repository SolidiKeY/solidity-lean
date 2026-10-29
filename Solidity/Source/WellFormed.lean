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

/-! ## Well-formedness -/

/-- The parameter names of a parameter list, in order. -/
def Syn.paramNames : {c : Cat} → Syn c → List (Option String)
  | _, .cons x xs => x.paramNames ++ xs.paramNames
  | _, .param _ _ n => [n]
  | _, _ => []

/-- The context of a function body: its named parameters as locals (the
last innermost) and its return types. -/
def Ctx.forFn (E : Env) (scope : Option String) (names : List (Option String)) (ps rs : List STy) : Ctx :=
  { env := E, scope := scope, rets := rs,
    locals := ((names.zip ps).filterMap fun (n, τ) => n.map (·, τ)).reverse }

/-- Whether two declarations clash: the same name in the same scope, one of
them neither a function nor an event. -/
def Decl.clash (d d' : Decl) : Bool :=
  d.name != "" && d.name == d'.name && d.scope == d'.scope &&
    !((d.kind == .function && d'.kind == .function) || (d.kind == .event && d'.kind == .event))

/-- The body of a function declaration, if it has one. -/
def Decl.body? (d : Decl) : Option (Syn (.list (.item .body))) :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ _ _ _ _ _ (.some (.block b)) => Option.some b
  | _, _, _ => Option.none

/-- The parameter names of a function declaration. -/
def Decl.paramNames (d : Decl) : List (Option String) :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ ps _ _ _ _ _ _ _ => ps.paramNames
  | _, _, _ => []

/-- The initializer of a state variable, if any. -/
def Decl.init? (d : Decl) : Option (Syn .expr) :=
  match d.kind, d.top, d.node with
  | .stateVar, _, .stateVar _ _ _ _ _ _ (.some e) => Option.some e
  | .constant, _, .constant _ _ e => Option.some e
  | _, _, _ => Option.none

/-- **Well-formedness** of a resolved unit. -/
structure WellFormed (r : Resolution) : Prop where
  linearizes : ∀ d ∈ r.unit.decls, d.kind = .contract ∨ d.kind = .interface →
    (r.env.linearize d.name).isSome
  noClash : ∀ d ∈ r.unit.decls, ∀ d' ∈ r.unit.decls, d.clash d' = true → d = d'
  oneCoder : r.unit.abicoderPragmas ≤ 1
  inits : ∀ d ∈ r.unit.decls, ∀ e, d.init? = Option.some e → ∃ τ σ, d.varTy r.env = Option.some τ ∧
    HasType ⟨r.env, d.scope, [], []⟩ e σ ∧ σ.implicit (Ctx.isBase ⟨r.env, d.scope, [], []⟩) τ = true
  bodies : ∀ d ∈ r.unit.decls, ∀ b, d.body? = Option.some b → ∃ ps rs Γ',
    d.fnSig r.env = Option.some (ps, rs) ∧ ItemsOK (Ctx.forFn r.env d.scope d.paramNames ps rs) b Γ'

/-- The syntax part of the profile: no syntax-level exclusion. -/
def InProfileSyntax (r : Resolution) : Prop := r.unit.rejections = []

end Solidity.Source
