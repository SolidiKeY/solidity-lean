import Solidity.Yul.RawFrame
import Solidity.Yul.LocalOperations

/-! Explicit H11 LOCAL boundaries. These APIs model canonical bool/uint8
return-value reads, not all ordinary Solidity operations. Both pinned pipelines
use the same canonical return projection; unchecked uint8 addition separately
retains the existing H3 pipeline difference. No assembly write invokes them.
Compiler agreement is finite evidence, not asserted as a universal theorem. -/
namespace Solidity.Yul.RawFrame
abbrev Pipeline := LocalOperations.Pipeline

def boolWord {ctx} (state : State ctx) (index : Solidity.Source.Idx ctx.tys .bool) : Word :=
  LocalOperations.scalarWord ((materialize state).1.get index) (LocalOperations.boolShape ctx.env)

def u8Word {ctx} (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)) : Word :=
  LocalOperations.scalarWord ((materialize state).1.get index) (LocalOperations.u8Shape ctx.env)

def returnBool {ctx} (pipeline : Pipeline) (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys .bool) : Solidity.Source.Val ctx.env.layout .bool :=
  match pipeline with
  | .legacy => LocalOperations.boolInput ((materialize state).1.get index)
  | .viaIR => LocalOperations.boolInput ((materialize state).1.get index)

def returnU8 {ctx} (pipeline : Pipeline) (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)) :
    Solidity.Source.Val ctx.env.layout (.int Solidity.Source.IntTy.u8) :=
  match pipeline with
  | .legacy => LocalOperations.u8Input ((materialize state).1.get index)
  | .viaIR => LocalOperations.u8Input ((materialize state).1.get index)

/-- Independent numeric relation on the intrinsically typed return value.
The raw frame itself retains the original word. -/
def BoolReturnD {ctx} (_pipeline : Pipeline) (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys .bool) (value : Solidity.Source.Val ctx.env.layout .bool) : Prop :=
  value.key = some (if (boolWord state index).val != 0 then 1 else 0)

def U8ReturnD {ctx} (_pipeline : Pipeline) (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8))
    (value : Solidity.Source.Val ctx.env.layout (.int Solidity.Source.IntTy.u8)) : Prop :=
  value.key = some (((u8Word state index).val % 256 : Nat) : Int)

theorem returnBool_sound {ctx} (pipeline : Pipeline) (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys .bool) :
    BoolReturnD pipeline state index (returnBool pipeline state index) := by
  cases pipeline <;> rfl

theorem returnU8_sound {ctx} (pipeline : Pipeline) (state : State ctx)
    (index : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)) :
    U8ReturnD pipeline state index (returnU8 pipeline state index) := by
  cases pipeline <;> rfl

def uncheckedU8Add {ctx} (pipeline : Pipeline) (state : State ctx)
    (left right : Solidity.Source.Idx ctx.tys (.int Solidity.Source.IntTy.u8)) :
    Solidity.Source.R (LocalValue ctx.env (.int Solidity.Source.IntTy.u8)) :=
  LocalOperations.uncheckedU8Add pipeline
    ((materialize state).1.get left) ((materialize state).1.get right)

end Solidity.Yul.RawFrame
