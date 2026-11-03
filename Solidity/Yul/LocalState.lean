import Solidity.Yul.LocalValues

/-! LOCAL extension of the actual Source machine state. The existing St is
retained verbatim. This is not physical-view/world semantics. The clean bridge
below refuses raw constructors; it is NOT the general assembly statement hook
or a pipeline cleanup policy. -/
namespace Solidity.Yul

abbrev LocalState (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx) :=
  LocalValues env ctx × Solidity.Source.St env

theorem LocalValues.clean_writeScalar {env ctx ty encoding}
    (locals : LocalValues env ctx) (index : Solidity.Source.Idx ctx ty)
    (shape : DeclaredSourceTypeD env ty (.value encoding)) (raw : Word) :
    LocalValues.clean? ctx (locals.writeScalar index shape raw) = none := by
  induction index with
  | here => rfl
  | there index ih =>
      change (do
        let first ← locals.1.clean?
        let rest ← LocalValues.clean? _ (locals.2.writeScalar index shape raw)
        pure (Solidity.Source.Locals.cons first rest)) = none
      rw [ih locals.2]
      cases locals.1.clean? <;> rfl

namespace LocalState

def ofClean {env ctx} (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    LocalState env ctx := (LocalValues.ofClean state.1, state.2)

def clean? {env ctx} (state : LocalState env ctx) :
    Option (Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :=
  (LocalValues.clean? ctx state.1).map (fun locals => (locals,state.2))

theorem clean_ofClean {env ctx}
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    clean? (ofClean state) = some state := by
  simp only [clean?,ofClean,LocalValues.clean_ofClean,Option.map_some]

/-- Exactly the existing Source evaluator on states recognized as clean.
A raw state returns none; no cleaning operation or inferred invariant is used. -/
def runClean {env ctx α} (action : Solidity.Source.EM env ctx α)
    (state : LocalState env ctx) :
    Option (Except Solidity.Source.Halt α × LocalState env ctx) :=
  (clean? state).map (fun clean =>
    let result := action.run clean
    (result.1,ofClean result.2))

theorem runClean_ofClean {env ctx α} (action : Solidity.Source.EM env ctx α)
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    runClean action (ofClean state) =
      some ((action.run state).1,ofClean (action.run state).2) := by
  simp only [runClean,clean_ofClean,Option.map_some]

theorem runClean_refuses {env ctx α} (action : Solidity.Source.EM env ctx α)
    (state : LocalState env ctx) (raw : clean? state = none) :
    runClean action state = none := by
  simp only [runClean,raw,Option.map_none]

def writeScalar {ctx : Solidity.Source.Ctx} (state : LocalState ctx.env ctx.tys)
    (cell : SourceScalarCell ctx) (raw : Word) : LocalState ctx.env ctx.tys :=
  (cell.localWrite state.1 raw,state.2)

theorem writeScalar_world {ctx : Solidity.Source.Ctx} (state : LocalState ctx.env ctx.tys)
    (cell : SourceScalarCell ctx) (raw : Word) :
    (writeScalar state cell raw).2 = state.2 := rfl

theorem writeScalar_read {ctx : Solidity.Source.Ctx} (state : LocalState ctx.env ctx.tys)
    (cell : SourceScalarCell ctx) (raw : Word) :
    cell.localRead? (writeScalar state cell raw).1 = some raw :=
  cell.localRead_write state.1 raw

theorem writeScalar_not_clean {ctx : Solidity.Source.Ctx}
    (state : LocalState ctx.env ctx.tys) (cell : SourceScalarCell ctx) (raw : Word) :
    clean? (writeScalar state cell raw) = none := by
  unfold clean? writeScalar SourceScalarCell.localWrite
  rw [LocalValues.clean_writeScalar]
  rfl

end LocalState
end Solidity.Yul
