import Solidity.Yul.RawBoundary
import Solidity.Yul.LocalExprStatement

/-! Additive H11 raw-frame consumer for certified ACTUAL Source expression
statements. Existing typed layers are untouched. This is a concrete bool-control
slice, not a new global admission predicate or general P16/session theorem.
All halts retain the actual partial raw word state and whole world. -/
namespace Solidity.Yul.RawSource

def rawEmpty {ctx} (state : RawFrame.State ctx) : Bool :=
  (allWordCells (localExternalTypes ctx)).all (fun cell => (state.raw cell).isNone)

theorem rawEmpty_iff {ctx} (state : RawFrame.State ctx) :
    rawEmpty state = true ↔ ∀ cell, state.raw cell = none := by
  rw [rawEmpty, List.all_eq_true]
  constructor
  · intro empty cell
    exact Option.isNone_iff_eq_none.mp (empty cell (allWordCells_complete cell))
  · intro empty cell _
    exact Option.isNone_iff_eq_none.mpr (empty cell)

theorem rawEmpty_ofClean {ctx : Solidity.Source.Ctx} (locals : Solidity.Source.Locals ctx.env.layout ctx.tys)
    (world : Solidity.Source.St ctx.env) :
    rawEmpty (RawFrame.ofClean locals world) = true := by
  exact (rawEmpty_iff _).mpr (fun _ => rfl)

/-- Preserve genuine clean constructors when NO raw overlay exists. In the
other case use the already proved exact word materialization, never cleaning
dirty words. This is representation preparation, not an ordinary read policy. -/
def localState {ctx} (state : RawFrame.State ctx) : LocalState ctx.env ctx.tys :=
  if rawEmpty state = true then (LocalValues.ofClean state.clean, state.world)
  else RawFrame.materialize state

theorem localState_view {ctx} (state : RawFrame.State ctx) :
    localWordCells ctx (localState state).1 = RawFrame.view state := by
  unfold localState
  split
  · next empty =>
    funext cell
    change localWordCells ctx (LocalValues.ofClean state.clean) cell =
      (state.raw cell).getD (localWordCells ctx (LocalValues.ofClean state.clean) cell)
    rw [(rawEmpty_iff state).mp empty cell]
    rfl
  · exact RawFrame.materialize_view state

theorem localState_ofClean {ctx : Solidity.Source.Ctx} (locals : Solidity.Source.Locals ctx.env.layout ctx.tys)
    (world : Solidity.Source.St ctx.env) :
    localState (RawFrame.ofClean locals world) = LocalState.ofClean (locals, world) := by
  unfold localState
  rw [if_pos (rawEmpty_ofClean locals world)]
  rfl

def capture {ctx} (initial : RawFrame.State ctx) (next : LocalState ctx.env ctx.tys) :
    RawFrame.State ctx :=
  ⟨initial.clean, fun cell => some (localWordCells ctx next.1 cell), next.2⟩

theorem capture_view {ctx} (initial : RawFrame.State ctx) (next : LocalState ctx.env ctx.tys) :
    RawFrame.view (capture initial next) = localWordCells ctx next.1 := rfl

/-- Certificate over an existing intrinsic RStmt; no replacement statement AST.
The supported Source bool-control expression syntax is explicit. -/
inductive Supported (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
    (modifier : Bool) (control : Solidity.Source.SCtx) :
    Solidity.Source.RStmt ctx.env returns modifier control ctx.tys ctx.tys → Type where
  | expression {expr} : LocalBoolControl.Supported ctx.env ctx.tys expr →
      Supported ctx returns modifier control (.expr expr)

def localRun {ctx returns modifier control stmt}
    (proof : Supported ctx returns modifier control stmt) :
    Nat → RawFrame.State ctx → Solidity.Source.R Unit × LocalState ctx.env ctx.tys :=
  Supported.casesOn
    (motive := fun _ _ =>
      Nat → RawFrame.State ctx → Solidity.Source.R Unit × LocalState ctx.env ctx.tys)
    proof (fun {_expr} body fuel state =>
      LocalExprStatement.discard (LocalBoolControl.eval body) fuel (localState state))

/-- Raw-frame statement execution preserves the full local result on timeout
and other halts; it does not erase dirty locals through Source.EM.sub. -/
def execS {ctx returns modifier control stmt}
    (proof : Supported ctx returns modifier control stmt) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  let result := localRun proof fuel state
  (result.1, capture state result.2)

theorem exact_result {ctx returns modifier control stmt}
    (proof : Supported ctx returns modifier control stmt) (fuel : Nat) (state : RawFrame.State ctx) :
    (execS proof fuel state).1 = (localRun proof fuel state).1 ∧
      RawFrame.view (execS proof fuel state).2 = localWordCells ctx (localRun proof fuel state).2.1 ∧
      (execS proof fuel state).2.world = (localRun proof fuel state).2.2 :=
  ⟨rfl, rfl, rfl⟩

/-- Existing Source statement observation, separate from retained raw state.
On a dirty normal result it may refuse; no implicit whole-frame cleanup. -/
def observation {ctx returns modifier control stmt}
    (proof : Supported ctx returns modifier control stmt) (fuel : Nat) (state : RawFrame.State ctx) :=
  LocalExprStatement.project (localRun proof fuel state)

theorem clean_source_agrees {ctx returns modifier control stmt}
    (proof : Supported ctx returns modifier control stmt)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) (world : Solidity.Source.St ctx.env) :
    observation proof fuel (RawFrame.ofClean locals world) =
      some ((Solidity.Source.execS glob frame fuel nps ph stmt locals).run
        (Solidity.Source.L0 ctx.env, world)) := by
  cases proof with
  | expression body =>
    change LocalExprStatement.project
      (LocalExprStatement.discard (LocalBoolControl.eval body) fuel
        (localState (RawFrame.ofClean locals world))) = _
    rw [localState_ofClean]
    exact LocalExprStatement.bool_source_agrees body glob frame fuel nps ph
      returns modifier control locals world

end Solidity.Yul.RawSource
