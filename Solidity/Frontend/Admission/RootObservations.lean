import Solidity.Source.Resolved
import Solidity.Language.Features

/-!
# Observation sites of resolved expression roots (G15 checkpoint 1)

Walk the actual intrinsic resolved syntax, including expressions inside lvalues
and both converted/unconverted argument lists. Declaration identities are
retained at call sites; this module does not follow function bodies yet. This
is a structural extraction interface, not an operational adequacy theorem or
complete feature extraction for types, specification terms or the
solc-JSON importer. No syntax representation is replaced.
-/
namespace Solidity.Frontend.Admission
open Solidity.Source
open Solidity.Language

/-- Admission metadata, never an intermediate executable expression. -/
inductive ObservationSite where
  | builtin (name : Builtin)
  | magic (name : Builtin) (member : String)
  | internalCall (declaration : Decl)
  | externalCall (declaration : Decl)
  | balance
  | payment
  | abiEncode (kind : AbiKind)
  | abiDecode
  | emitEvent (declaration : Decl)
  | customError (declaration : Decl)
  | rethrow

/-- Missing namespace members fail closed. Calls carry their declarations for
subsequent closure extraction; their local status does not certify callees. -/
def ObservationSite.status : ObservationSite → Option Status
  | .builtin b => some b.status
  | .magic b m => b.memberStatus m
  | .internalCall _ => some (.admitted "internalCalls")
  | .externalCall _ => some (.admitted Feature.externalTypedCalls.id)
  | .balance => some (.admitted "addressBalance")
  | .payment => some (.admitted "sendTransfer")
  | .abiEncode .encode => some (.admitted "abiEncode")
  | .abiEncode .encodePacked => some (.admitted "abiEncodePacked")
  | .abiEncode .encodeWithSelector => some (.admitted "abiEncodeWithSelector")
  | .abiEncode .encodeWithSignature => some (.admitted "abiEncodeWithSignature")
  | .abiDecode => some (.admitted "abiDecode")
  | .emitEvent _ => some (.admitted "emitStatement")
  | .customError _ => some (.admitted Feature.revertStatement.id)
  | .rethrow => some (.admitted "canonicalRethrow")

/-- This is the existing S01 status decision, not an implementation inventory. -/
def ObservationSite.allowed (site : ObservationSite) : Bool :=
  match site.status with
  | some (.admitted name) =>
    (Feature.all.find? (fun f => f.id == name)).any fun f =>
      decide (f.info.scope = .model ∨ f.info.scope = .abstract)
  | _ => false

/-- A local acceptance must name a real feature in the frozen profile, with
exactly the S01 status identifier and an allowed scope. Unknown IDs fail closed. -/
theorem ObservationSite.allowed_iff (site : ObservationSite) :
    site.allowed = true ↔ ∃ name f, site.status = some (.admitted name) ∧
      Feature.all.find? (fun f => f.id == name) = some f ∧ f.inProfile := by
  cases hs : site.status with
  | none => simp only [allowed, hs, Bool.false_eq_true, false_iff]; rintro ⟨_, _, h, _⟩; cases h
  | some st =>
    cases st with
    | excluded name =>
      simp only [allowed, hs, Bool.false_eq_true, false_iff]
      rintro ⟨_, _, h, _⟩; cases h
    | removed name =>
      simp only [allowed, hs, Bool.false_eq_true, false_iff]
      rintro ⟨_, _, h, _⟩; cases h
    | admitted name =>
      simp only [allowed, hs, Option.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨f, hf, hp⟩
        exact ⟨name, f, rfl, hf, hp⟩
      · rintro ⟨n, f, hn, hf, hp⟩
        cases hn
        exact ⟨f, hf, hp⟩

mutual
/-- All local observation sites, in structural order; no fuel or truncation.
The cases motives generalize every result index (intrinsic Gate G0). -/
def observations {E : Env} {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) : List ObservationSite :=
  RExpr.casesOn (motive_1 := fun _ _ => List ObservationSite) e
    (fun _ => []) -- const
    (fun _ _ => []) -- bytesLit
    (fun _ => []) -- addressLit
    (fun _ => []) -- bool
    (fun _ => []) -- str
    (fun _ => []) -- local
    (fun _ _ => []) -- state
    (fun _ => [.builtin .this])
    (fun es => argsObservations es)
    (fun e _ => observations e) -- conv
    (fun e _ => observations e) -- explicit conversion
    (fun _ e => observations e) -- unary
    (fun _ _ l => lvalObservations l) -- inc/dec
    (fun l => lvalObservations l) -- delete
    (fun _ a b => observations a ++ observations b) -- binary
    (fun _ a b => observations a ++ observations b) -- compare
    (fun _ _ _ => []) -- constant comparison
    (fun _ a b _ => observations a ++ observations b) -- shift
    (fun c a b => observations c ++ observations a ++ observations b)
    (fun l e => lvalObservations l ++ observations e)
    (fun _ l e _ => lvalObservations l ++ observations e) -- compound
    (fun a i _ => observations a ++ observations i) -- array index
    (fun a i => observations a ++ observations i) -- mapping index
    (fun a i _ => observations a ++ observations i) -- byte index
    (fun a _ => observations a) -- length
    (fun a => observations a) -- payable
    (fun d _ args => .internalCall d :: convObservations args)
    (fun b m _ => [.magic b m])
    (fun a => .balance :: observations a)
    (fun b args _ => .builtin b :: argsObservations args)
    (fun a _ _ => observations a) -- member
    (fun _ args => convObservations args) -- struct construction
    (fun target d _ value args => .externalCall d ::
      (observations target ++ observations value ++ convObservations args))
    (fun a v => .payment :: (observations a ++ observations v)) -- transfer
    (fun a v => .payment :: (observations a ++ observations v)) -- send
    (fun k args => .abiEncode k :: argsObservations args)
    (fun l e _ => lvalObservations l ++ observations e) -- copy assignment
    (fun data _ _ => .abiDecode :: observations data)
    (fun a _ lo _ hi _ _ => observations a ++ observations lo ++ observations hi)
    (fun args _ => convObservations args) -- inline array
    (fun _ len _ => observations len) -- new array
termination_by structural e

def argsObservations {E : Env} {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) : List ObservationSite :=
  RArgs.casesOn (motive_2 := fun _ _ => List ObservationSite) es
    [] (fun e es => observations e ++ argsObservations es)
termination_by structural es

def convObservations {E : Env} {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) : List ObservationSite :=
  RConvArgs.casesOn (motive_3 := fun _ _ => List ObservationSite) es
    [] (fun e _ es => observations e ++ convObservations es)
termination_by structural es

def lvalObservations {E : Env} {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) : List ObservationSite :=
  RLVal.casesOn (motive_4 := fun _ _ => List ObservationSite) l
    (fun _ => []) (fun _ _ _ => [])
    (fun a _ i _ => observations a ++ observations i)
    (fun a i => observations a ++ observations i)
    (fun a _ i _ => observations a ++ observations i)
    (fun a _ _ _ => observations a)
termination_by structural l
end

/-- Optional loop conditions are still expression roots. -/
def optBoolObservations {E : Env} {Γ : RCtx} : ROptBool E Γ → List ObservationSite
  | .none => []
  | .some e => observations e

def optExprObservations {E : Env} {Γ : RCtx} : ROptExpr E Γ → List ObservationSite
  | .none => []
  | .some e => observations e

mutual
/-- Every expression-bearing statement position, including loop postconditions,
all branches and try success/catch bodies. No execution-fuel bound is used. -/
def stmtObservations {E : Env} {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') : List ObservationSite :=
  RStmt.casesOn (motive_1 := fun _ _ _ _ => List ObservationSite) s
    (fun e => observations e) -- expression
    (fun _ => []) -- placeholder
    (fun _ => []) -- declaration
    (fun e _ => observations e)
    (fun b => itemsObservations b)
    (fun c s => observations c ++ stmtObservations s)
    (fun c s t => observations c ++ stmtObservations s ++ stmtObservations t)
    (fun c s => observations c ++ stmtObservations s) -- while
    (fun s c => stmtObservations s ++ observations c) -- do/while
    (fun init c post body => stmtObservations init ++ optBoolObservations c ++
      stmtObservations body ++ optExprObservations post)
    [] [] [] -- skip, break, continue
    (fun _ => []) -- return
    (fun _ e _ => observations e)
    (fun es => convObservations es)
    (fun d _ args => .emitEvent d :: convObservations args)
    (fun d _ args => .customError d :: convObservations args)
    (fun _ => [.rethrow])
    (fun _ e _ => observations e) -- tuple declaration
    (fun target d _ args ok _ cat => .externalCall d ::
      (observations target ++ convObservations args ++ itemsObservations ok ++ itemsObservations cat))
termination_by structural s

def itemsObservations {E : Env} {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (b : RItems E R M k Γ Γ') : List ObservationSite :=
  RItems.casesOn (motive_2 := fun _ _ _ _ => List ObservationSite) b
    [] (fun s rest => stmtObservations s ++ itemsObservations rest)
    (fun b rest => itemsObservations b ++ itemsObservations rest)
termination_by structural b
end

/-- A root retains its environment and local/result type indices. -/
abbrev ExprRoot (E : Env) := (Γ : RCtx) × (τ : STy) × RExpr E Γ τ

def rootObservations {E : Env} (roots : List (ExprRoot E)) : List ObservationSite :=
  roots.flatMap fun root => observations root.2.2

/-- No root's observations disappear in aggregation. -/
theorem root_observation_iff {E : Env} (roots : List (ExprRoot E)) (site : ObservationSite) :
    site ∈ rootObservations roots ↔ ∃ root ∈ roots, site ∈ observations root.2.2 := by
  exact List.mem_flatMap

/-- Admission of the collected local observations covers every supplied root,
not just the first root. Callee bodies and statement roots remain a next step. -/
theorem accepted_roots {E : Env} (roots : List (ExprRoot E))
    (h : (rootObservations roots).all ObservationSite.allowed = true)
    {root : ExprRoot E} (hr : root ∈ roots) {site : ObservationSite}
    (hs : site ∈ observations root.2.2) : site.allowed = true :=
  List.all_eq_true.mp h site ((root_observation_iff roots site).mpr ⟨root, hr, hs⟩)

/-- The exact magic member, including excluded ones, is reported. -/
theorem magic_reported {E : Env} {Γ : RCtx} {τ : STy} (b : Builtin) (m : String)
    (h : b.memberTy m = some τ) :
    ObservationSite.magic b m ∈ observations (RExpr.magic (E := E) (Γ := Γ) b m h) :=
  List.mem_cons_self

/-- Local shadowing is already resolved: a local is not classified as a builtin. -/
theorem local_no_observations {E : Env} {Γ : RCtx} {τ : STy} (i : Idx Γ τ) :
    observations (RExpr.local (E := E) i) = [] := rfl

end Solidity.Frontend.Admission
