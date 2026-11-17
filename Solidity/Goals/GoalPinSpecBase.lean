import Solidity.Tools.Goal

/-! The goal-pin vocabulary `GoalPinSpec`, moved out of `Goals/Plan.lean` (H666). -/

namespace Solidity.Goals

namespace GoalPinSpec

/-- One committed statement digest and its decision identifier. -/
structure Pin where
  goal : Lean.Name
  digest : List Nat
  decision : Nat
  deriving DecidableEq

/-- A SHA-256 digest is exactly 32 bytes; decision records are checked separately. -/
def Pin.WellFormed (p : Pin) : Prop :=
  p.digest.length = 32 ∧ p.digest.all (fun b => decide (b < 256)) = true

open Lean

inductive CoverageError where
  | duplicateRegistry | finishMissing | finishMalformed | finishMismatch | statusFailed
  deriving DecidableEq

/-- The finish statement must name registered components in a conjunction. -/
def finishLeaves : Expr → Option (List Lean.Name)
  | .app (.app (.const ``And []) a) b => do
      pure ((← finishLeaves a) ++ (← finishLeaves b))
  | .const n _ => some [n]
  | .mdata _ e => finishLeaves e
  | _ => none

/-- Coverage from the current environment, using the roadmap classifier itself.
The aggregate itself is included so its component occurrences are pinned. The
integration command must load the complete goal registry after the proof is
available; this operation does not establish import completeness. -/
def required : MetaM (Except CoverageError (List Lean.Name)) :=
  tryCatchRuntimeEx (do
    let env ← getEnv
    let entries := (goalExt.getState env).toList
    let names := entries.map (·.decl)
    if names.eraseDups.length != names.length then return .error .duplicateRegistry
    let finish := entries.filter (fun e => e.decl == `Solidity.Goals.projectFinished)
    let [entry] := finish | return .error .finishMissing
    let some (.defnInfo d) := env.toKernelEnv.find? entry.decl | return .error .finishMalformed
    let some components := finishLeaves d.value | return .error .finishMalformed
    let deps := entry.deps.toList
    if components.eraseDups.length != components.length || deps.eraseDups.length != deps.length ||
        !(components.all deps.contains) || !(deps.all components.contains) ||
        !(components.all names.contains) then
      return .error .finishMismatch
    let rs ← statuses
    let proved := rs.toList.filterMap fun (e, s) => if s == .proved then some e.decl else none
    return .ok (entry.decl :: components ++ proved).eraseDups) fun _ => pure (.error .statusFailed)

/-! Canonical unfolding nodes retain the source application, including the fully
qualified declaration identity, universe arguments and term arguments. The
unfolding spine retains the literal constant head and independently normalized
arguments, without unfolding that head again. Data bodies remain folded.
Encoding removes metadata and binder names, and retains binder annotations and
universe syntax. Encoding alone does not validate
source declarations, typing or the unfolding relation. -/
inductive Canonical where
  | bvar (index : Nat)
  | sort (level : Lean.Level)
  | const (name : Lean.Name) (levels : List Lean.Level)
  | app (fn arg : Canonical)
  | lam (type body : Canonical) (info : Lean.BinderInfo)
  | forallE (type body : Canonical) (info : Lean.BinderInfo)
  | letE (type value body : Canonical) (nondep : Bool)
  | natLit (value : Nat)
  | strLit (value : String)
  | proj (typeName : Lean.Name) (index : Nat) (target : Canonical)
  | unfolded (source spine body : Canonical)

/-- Reify syntax without metadata or binder names; this requires separate typing validation. -/
def reify : Lean.Expr → Option Canonical
  | .bvar i => some (.bvar i)
  | .fvar _ | .mvar _ => none
  | .sort u => some (.sort u)
  | .const n us => some (.const n us)
  | .app f a => do pure (.app (← reify f) (← reify a))
  | .lam _ t b bi => do pure (.lam (← reify t) (← reify b) bi)
  | .forallE _ t b bi => do pure (.forallE (← reify t) (← reify b) bi)
  | .letE _ t v b nondep => do pure (.letE (← reify t) (← reify v) (← reify b) nondep)
  | .lit (.natVal n) => some (.natLit n)
  | .lit (.strVal s) => some (.strLit s)
  | .mdata _ e => reify e
  | .proj n i e => do pure (.proj n i (← reify e))

/-- Source expressions contain no unfolding markers. -/
def Canonical.raw : Canonical → Bool
  | .app f a => f.raw && a.raw
  | .lam t b _ | .forallE t b _ => t.raw && b.raw
  | .letE t v b _ => t.raw && v.raw && b.raw
  | .proj _ _ e => e.raw
  | .unfolded .. => false
  | _ => true


/-- Check source universe parameters without assigning metavariables. -/
def validLevel (params : List Lean.Name) : Lean.Level → Bool
  | .zero => true
  | .succ a => validLevel params a
  | .max a b | .imax a b => validLevel params a && validLevel params b
  | .param n => params.contains n
  | .mvar _ => false

/-- A reified declaration is closed under its binders and declared universes. -/
def Canonical.sourceScoped (params : List Lean.Name) (depth : Nat) : Canonical → Bool
  | .bvar i => decide (i < depth)
  | .sort u => validLevel params u
  | .const _ us => us.all (validLevel params)
  | .app f a => f.sourceScoped params depth && a.sourceScoped params depth
  | .lam t b _ | .forallE t b _ =>
      t.sourceScoped params depth && b.sourceScoped params (depth+1)
  | .letE t v b _ => t.sourceScoped params depth && v.sourceScoped params depth &&
      b.sourceScoped params (depth+1)
  | .natLit _ | .strLit _ => true
  | .proj _ _ e => e.sourceScoped params depth
  | .unfolded .. => false

structure Definition where
  name : Lean.Name
  levelParams : List Lean.Name
  type : Canonical
  value : Canonical

inductive DefinitionError where
  | missing | notDefinition | unsafeDefinition | malformed | lookupFailed
  deriving DecidableEq

/-- Inspect the checked kernel environment and reify its source syntax. -/
def inspectIn (env : Lean.Environment) (n : Lean.Name) : Except DefinitionError Definition := do
  let some info := env.toKernelEnv.find? n | throw .missing
  let .defnInfo d := info | throw .notDefinition
  if d.safety != .safe then throw .unsafeDefinition
  if d.levelParams.eraseDups.length != d.levelParams.length then throw .malformed
  let some ty := reify d.type | throw .malformed
  let some val := reify d.value | throw .malformed
  if !(ty.sourceScoped d.levelParams 0) || !(val.sourceScoped d.levelParams 0) then
    throw .malformed
  pure ⟨n, d.levelParams, ty, val⟩

/-- Read a definition from the current environment; no caller supplies its body. -/
def inspectDefinition (n : Lean.Name) : MetaM (Except DefinitionError Definition) :=
  tryCatchRuntimeEx (do return inspectIn (← getEnv) n) fun _ => pure (.error .lookupFailed)

namespace Canonical

/-! Capture-avoiding substitution is applied to raw syntax before unfolding
markers are introduced. Universe parameters are instantiated simultaneously. -/

def raiseVars (cutoff amount : Nat) : Canonical → Canonical
  | .bvar i => if i < cutoff then .bvar i else .bvar (i + amount)
  | .app f a => .app (raiseVars cutoff amount f) (raiseVars cutoff amount a)
  | .lam t b bi => .lam (raiseVars cutoff amount t) (raiseVars (cutoff+1) amount b) bi
  | .forallE t b bi => .forallE (raiseVars cutoff amount t) (raiseVars (cutoff+1) amount b) bi
  | .letE t v b nondep => .letE (raiseVars cutoff amount t) (raiseVars cutoff amount v)
      (raiseVars (cutoff+1) amount b) nondep
  | .proj n i e => .proj n i (raiseVars cutoff amount e)
  | .unfolded src spine body => .unfolded (raiseVars cutoff amount src)
      (raiseVars cutoff amount spine) (raiseVars cutoff amount body)
  | e => e

def instantiateAt (depth : Nat) (arg : Canonical) : Canonical → Canonical
  | .bvar i =>
    if i == depth then raiseVars 0 depth arg else if i > depth then .bvar (i-1) else .bvar i
  | .app f a => .app (instantiateAt depth arg f) (instantiateAt depth arg a)
  | .lam t b bi => .lam (instantiateAt depth arg t) (instantiateAt (depth+1) arg b) bi
  | .forallE t b bi => .forallE (instantiateAt depth arg t) (instantiateAt (depth+1) arg b) bi
  | .letE t v b nondep => .letE (instantiateAt depth arg t) (instantiateAt depth arg v)
      (instantiateAt (depth+1) arg b) nondep
  | .proj n i e => .proj n i (instantiateAt depth arg e)
  | .unfolded src spine body => .unfolded (instantiateAt depth arg src)
      (instantiateAt depth arg spine) (instantiateAt depth arg body)
  | e => e

def beta (f : Canonical) : List Canonical → Canonical
  | [] => f
  | a :: args =>
    match f with
    | .lam _ body _ => beta (instantiateAt 0 a body) args
    | _ => beta (.app f a) args

def findLevel (n : Lean.Name) : List (Lean.Name × Lean.Level) → Option Lean.Level
  | [] => none
  | (p, u) :: rest => if p == n then some u else findLevel n rest

def substLevel (mapping : List (Lean.Name × Lean.Level)) : Lean.Level → Lean.Level
  | .zero => .zero
  | .succ a => .succ (substLevel mapping a)
  | .max a b => .max (substLevel mapping a) (substLevel mapping b)
  | .imax a b => .imax (substLevel mapping a) (substLevel mapping b)
  | .param n => (findLevel n mapping).getD (.param n)
  | .mvar n => .mvar n

def instantiateLevels (mapping : List (Lean.Name × Lean.Level)) : Canonical → Canonical
  | .sort u => .sort (substLevel mapping u)
  | .const n us => .const n (us.map (substLevel mapping))
  | .app f a => .app (instantiateLevels mapping f) (instantiateLevels mapping a)
  | .lam t b bi => .lam (instantiateLevels mapping t) (instantiateLevels mapping b) bi
  | .forallE t b bi => .forallE (instantiateLevels mapping t) (instantiateLevels mapping b) bi
  | .letE t v b nondep => .letE (instantiateLevels mapping t) (instantiateLevels mapping v)
      (instantiateLevels mapping b) nondep
  | .proj n i e => .proj n i (instantiateLevels mapping e)
  | .unfolded src spine body => .unfolded (instantiateLevels mapping src)
      (instantiateLevels mapping spine) (instantiateLevels mapping body)
  | e => e

end Canonical

namespace Encoding
def number (n : Nat) : List Nat := (toString n).toUTF8.data.toList.map UInt8.toNat ++ [0]
def bytes (s : String) : List Nat :=
  let bs := s.toUTF8.data.toList.map UInt8.toNat
  number bs.length ++ bs
def name : Lean.Name → List Nat
  | .anonymous => [1]
  | .str p s => [2] ++ name p ++ bytes s
  | .num p n => [3] ++ name p ++ number n
def level : Lean.Level → Option (List Nat)
  | .zero => some [1]
  | .succ a => do pure ([2] ++ (← level a))
  | .max a b => do pure ([3] ++ (← level a) ++ (← level b))
  | .imax a b => do pure ([4] ++ (← level a) ++ (← level b))
  | .param n => some ([5] ++ name n)
  | .mvar _ => none
def levels : List Lean.Level → Option (List Nat)
  | [] => some [0]
  | l :: ls => do pure ([1] ++ (← level l) ++ (← levels ls))
def binder : Lean.BinderInfo → Nat
  | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
def term (depth : Nat) : Canonical → Option (List Nat)
  | .bvar i => if i < depth then some ([1] ++ number i) else none
  | .sort u => do pure ([2] ++ (← level u))
  | .const n us => do pure ([3] ++ name n ++ (← levels us))
  | .app f a => do pure ([4] ++ (← term depth f) ++ (← term depth a))
  | .lam t b bi => do pure ([5, binder bi] ++ (← term depth t) ++ (← term (depth+1) b))
  | .forallE t b bi => do pure ([6, binder bi] ++ (← term depth t) ++ (← term (depth+1) b))
  | .letE t v b nondep => do
      pure ([7, if nondep then 1 else 0] ++ (← term depth t) ++ (← term depth v) ++
        (← term (depth+1) b))
  | .natLit n => some ([8] ++ number n)
  | .strLit s => some ([9] ++ bytes s)
  | .proj n i e => do pure ([10] ++ name n ++ number i ++ (← term depth e))
  | .unfolded e spine b => do
      pure ([11] ++ (← term depth e) ++ (← term depth spine) ++ (← term depth b))
def encode (e : Canonical) : Option (List Nat) :=
  (term 0 e).map fun bs => [71, 80, 1, 0] ++ bs
end Encoding

/-- A digest of this representation; recomputation must still bind it to `goal`. -/
def Pin.DigestOf (p : Pin) (normal : Canonical) : Prop :=
  ∃ bs, Encoding.encode normal = some bs ∧ p.digest = Solidity.Hashes.sha256 bs

/-- Canonical trailer spelling; existence of the decision is an integration check. -/
def Pin.decisionId (p : Pin) : String := "H" ++ toString p.decision

/-- Collision freedom only for these two byte strings, not for the finite digest. -/
def CollisionFreeOn (a b : List Nat) : Prop :=
  Solidity.Hashes.sha256 a = Solidity.Hashes.sha256 b → a = b

/-- Duplicate identities, even identical entries, are rejected. -/
def Unique (pins : List Pin) : Prop := (pins.map Pin.goal).Nodup

/-- Every required identity has a committed entry. -/
def Covers (requiredNames : List Lean.Name) (pins : List Pin) : Prop :=
  ∀ n ∈ requiredNames, ∃ p ∈ pins, p.goal = n

/-! Operational acceptance remains an integration obligation: stale or mismatched
pins must fail elaboration; an isolated weakening of `CompilerEndpointWith` must
be rejected without editing production endpoint files; and a compiling added
`Compilation` branch passes only when canonical `Input` is unchanged, otherwise
requiring a recorded decision and pin update. CI must reject pin-file edits without
a `Goal-Change: H<n>` trailer bound to a recorded decision. These checks are not
established by the Lean specification alone. -/

end GoalPinSpec

end Solidity.Goals
