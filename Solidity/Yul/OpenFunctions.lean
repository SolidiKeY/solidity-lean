import Solidity.Yul.CoordinateUpdates

/-! Intrinsic lexical environments retaining actual open-context Yul bodies.
Only globals are visible in a function body. No caller local/cell state is
stored. Tier-specific body admission evidence is real and required by constructors.
Execution/lowering remain explicitly tier A; generic environment data does not implement B/C effects. Lowering targets the existing word interpreter, not compiler bytecode. -/
namespace Solidity.Yul.OpenFunctions
open Closed

theorem body_policy {tier F G signatures sig} (index : Member signatures sig)
    (bodies : Bodies F G signatures) (policy : Policy.BodiesP tier bodies) :
    Policy.StmtP tier (Closed.bodyAt index bodies) := by
  induction index with
  | here => cases bodies with | cons body rest => exact policy.1
  | @there sig head signatures index ih =>
    cases bodies with
    | cons body rest => exact ih rest policy.2

inductive Environment (tier : Tier) : List Sig → Type where
  | nil : Environment tier []
  | group {F X} (signatures : List Sig) (outer : Environment tier F)
      (bodies : Bodies (signatures ++ F) (globals X) signatures)
      (policy : Policy.BodiesP tier bodies) : Environment tier (signatures ++ F)

structure Closure (tier : Tier) (sig : Sig) where
  functions : List Sig
  externals : List ExternalType
  environment : Environment tier functions
  body : Stmt functions (globals externals) ⟨true,false⟩ (sig.args+sig.rets)
  policy : Policy.StmtP tier body

def lookup {tier F} (environment : Environment tier F) {sig} (index : Member F sig) : Closure tier sig :=
  Environment.casesOn (motive := fun F _ => {sig : Sig} → Member F sig → Closure tier sig) environment
    (nil := fun {_} index => PEmpty.elim (Closed.peelMember index))
    (group := fun {F X} signatures outer bodies policy {_} index =>
      match Closed.splitMember signatures F index with
      | .inl selected =>
          ⟨_,X,.group signatures outer bodies policy,Closed.bodyAt selected bodies,
            body_policy selected bodies policy⟩
      | .inr selected => lookup outer selected)
    index
termination_by structural environment

theorem lookup_group {tier F X signatures sig} (outer : Environment tier F)
    (bodies : Bodies (signatures++F) (globals X) signatures) (policy : Policy.BodiesP tier bodies)
    (index : Member (signatures++F) sig) :
    lookup (.group signatures outer bodies policy) index =
      (match Closed.splitMember signatures F index with
       | .inl selected =>
           ⟨_,X,.group signatures outer bodies policy,Closed.bodyAt selected bodies,
             body_policy selected bodies policy⟩
       | .inr selected => lookup outer selected) := rfl

theorem lookup_new {tier F X signatures sig} (outer : Environment tier F)
    (bodies : Bodies (signatures++F) (globals X) signatures) (policy : Policy.BodiesP tier bodies)
    (index : Member signatures sig) :
    lookup (.group signatures outer bodies policy) (index.append F) =
      ⟨_,X,.group signatures outer bodies policy,Closed.bodyAt index bodies,
        body_policy index bodies policy⟩ := by
  rw [lookup_group,Closed.splitMember_append]

theorem lookup_old {tier F X signatures sig} (outer : Environment tier F)
    (bodies : Bodies (signatures++F) (globals X) signatures) (policy : Policy.BodiesP tier bodies)
    (index : Member F sig) :
    lookup (.group signatures outer bodies policy) (index.prefix signatures) = lookup outer index := by
  rw [lookup_group,Closed.splitMember_prefix]

abbrev PureEnvironment := Environment .A

def globalCells (X : List ExternalType) : WordCells (globals X) :=
  fun cell => False.elim cell.not_globals

def globalCoordinates (X : List ExternalType) (n : Nat) : Coordinates (globals X) n n where
  locals := fun i => i
  cells := fun cell => False.elim cell.not_globals
  origin := Sum.inl
  origin_local := fun _ => rfl
  origin_cell := fun cell => False.elim cell.not_globals
  location_origin := fun _ => rfl

theorem global_pack {X n} (state : WordState (globals X) n) :
    (globalCoordinates X n).pack state = state.locals := rfl

def lower {F} (environment : Environment .A F) : Closed.FunctionEnv F :=
  Environment.casesOn (motive := fun F _ => Closed.FunctionEnv F) environment
    (nil := .nil)
    (group := fun {_ _} signatures outer bodies policy =>
      .group signatures (lower outer) (WordAdapter.functions bodies policy (fun cell => cell.not_globals)).code)
termination_by structural environment

theorem lower_words {F} (environment : Environment .A F) : Closed.EnvWordP (lower environment) := by
  cases environment with
  | nil => exact True.intro
  | @group F X signatures outer bodies policy =>
    exact ⟨lower_words outer,(WordAdapter.functions bodies policy (fun cell => cell.not_globals)).words⟩
termination_by structural environment

def lowerClosure {sig} (closure : Closure .A sig) : Closed.Closure sig :=
  ⟨closure.functions,lower closure.environment,
    (WordAdapter.statement closure.body closure.policy (fun index => index)
      (fun cell => False.elim cell.not_globals)).code⟩

theorem lowerClosure_words {sig} (closure : Closure .A sig) : Closed.ClosureWordP (lowerClosure closure) :=
  ⟨lower_words closure.environment,
    (WordAdapter.statement closure.body closure.policy (fun index => index)
      (fun cell => False.elim cell.not_globals)).words⟩

theorem body_lower {F G signatures sig} (index : Member signatures sig) (bodies : Bodies F G signatures)
    (policy : Policy.BodiesP .A bodies) (empty : WordCell G → False) :
    Closed.bodyAt index (WordAdapter.functions bodies policy empty).code =
      (WordAdapter.statement (Closed.bodyAt index bodies) (body_policy index bodies policy)
        (fun i => i) (fun cell => False.elim (empty cell))).code := by
  induction index with
  | here => cases bodies with | cons body rest => rfl
  | @there sig head signatures index ih =>
    cases bodies with
    | cons body rest => exact ih rest policy.2

theorem lookup_lower {F} (environment : Environment .A F) {sig} (index : Member F sig) :
    Closed.lookup (lower environment) index = lowerClosure (lookup environment index) := by
  cases environment with
  | nil => exact PEmpty.elim (Closed.peelMember index)
  | @group F X signatures outer bodies policy =>
    rw [lower,Closed.lookup_group,lookup_group]
    cases selection : Closed.splitMember signatures F index with
    | inl selected =>
      change Closed.Closure.mk _ (lower (.group signatures outer bodies policy))
        (Closed.bodyAt selected (WordAdapter.functions bodies policy (fun cell => cell.not_globals)).code) =
          Closed.Closure.mk _ (lower (.group signatures outer bodies policy))
            (WordAdapter.statement (Closed.bodyAt selected bodies) (body_policy selected bodies policy)
              (fun i => i) (fun cell => False.elim cell.not_globals)).code
      rw [body_lower]
    | inr selected => exact lookup_lower outer selected
termination_by structural environment

end Solidity.Yul.OpenFunctions
