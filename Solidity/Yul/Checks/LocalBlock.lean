import Solidity.Yul.LocalBlock
import Solidity.Yul.Checks.LocalWordView
import Solidity.Source.Semantics
namespace Solidity.Yul.Checks.LocalBlock
open Solidity.Source
def env : Solidity.Source.Env := ⟨[]⟩
def functionTy := LocalWordView.functionTy
def ctx : Solidity.Source.Ctx :=
  {env:=env,scope:=none,locals:=[("flag",.bool),("ptr1",functionTy),
    ("small",.int IntTy.u8),("ptr2",functionTy),("byte",.fixedBytes 1 (by decide))]}
abbrev X := localExternalTypes ctx
def locals : Solidity.Source.Locals env.layout ctx.tys :=
  .cons (.bool true) (.cons LocalWordView.functionValue
    (.cons CleanLocals.small (.cons (.externalFn ⟨22136,by decide⟩ [1,2,3,4] rfl)
      (.cons CleanLocals.byteValue .nil))))
def initial : LocalState env ctx.tys :=
  (LocalValues.ofClean locals,Solidity.Source.St.init env)
def flag : WordCell X := .scalar ⟨.boolean,.here⟩
def first : Member X .externalFunction := .there .here
def second : Member X .externalFunction := .there (.there (.there .here))
def small : WordCell X := .scalar ⟨.unsigned 0,.there (.there .here)⟩
def byte : WordCell X := .scalar ⟨.fixedBytes 0,.there (.there (.there (.there .here)))⟩
def addr1 : WordCell X := .address first
def sel2 : WordCell X := .selector second

def assign (cell : WordCell X) (value : Expr [] X 0 1) :
    Stmt [] X ⟨false,false⟩ 0 :=
  .assign (Fin.cases (.external cell.writeRef) Fin.elim0) value
def maxExpr : Expr [] X 0 1 := .builtin (.pure .not) (Fin.cases (.literal (word 0)) Fin.elim0)
def addExpr : Expr [] X 0 1 := .builtin (.pure .add)
  (Fin.cases (.external small.readRef) (Fin.cases (.literal (word 256)) Fin.elim0))
def code : Stmt [] X ⟨false,false⟩ 0 :=
  .seq (assign flag (.literal (word 2)))
    (.seq (assign addr1 maxExpr) (.seq (assign sel2 maxExpr) (assign small addExpr)))
def policy : Policy.StmtP .A code := (Policy.stmt_iff .A code).mp rfl

example : wordCellCount X = 7 := rfl
example : (sourceFunctionAt ctx first).position ≠ (sourceFunctionAt ctx second).position :=
  sourceFunctionAt_different ctx first second (by intro same; cases same)
example (raw : Word) :
    localWordCells ctx (writeLocalWord ctx initial.1 raw addr1) (.address second) =
      localWordCells ctx initial.1 (.address second) :=
  localWordCells_write_other ctx initial.1 addr1 (.address second) raw (by intro same; cases same)
example (raw : Word) :
    localWordCells ctx (writeLocalWord ctx initial.1 raw flag) (.selector first) =
      localWordCells ctx initial.1 (.selector first) :=
  localWordCells_write_other ctx initial.1 flag (.selector first) raw (by intro same; cases same)
example (values : WordCells X) :
    localWordCells ctx (writebackLocalWords ctx initial.1 values) = values :=
  writebackLocalWords_view ctx initial.1 values
example (fuel : Nat) :
    (runLocalBlock ctx code policy fuel initial).map LocalBlockOutcome.project =
      WordAdapter.run code policy fuel ⟨Fin.elim0,localWordCells ctx initial.1⟩ :=
  runLocalBlock_projection ctx code policy fuel initial

def snapshot (state : LocalState env ctx.tys) : List Nat :=
  (List.finRange (wordCellCount X)).map (fun i => (localWordCells ctx state.1 (wordCellAt X i)).val)

#eval do
  let expected := [2,2^256-1,2309737967,257,22136,2^256-1,171*2^248]
  let some result := runLocalBlock ctx code policy 32 initial |
    throw (IO.userError "actual Source local block exhausted horizon32")
  unless snapshot result.state == expected && result.flow.isNormal do
    throw (IO.userError "actual Source local block dirty-word result mismatch")
  for fuel in [0,1,2,4,8,16,32] do
    match runLocalBlock ctx code policy fuel initial with
    | none => pure ()
    | some earlier =>
        unless snapshot earlier.state == expected && earlier.flow.isNormal do
          throw (IO.userError "actual Source completed horizon changed")
  let restored := writebackLocalWords ctx initial.1
    (fun cell => word (cell.slot.val+100))
  unless (List.finRange (wordCellCount X)).map
      (fun i => (localWordCells ctx restored (wordCellAt X i)).val) ==
        [100,101,102,103,104,105,106] do
    throw (IO.userError "actual full Source local writeback mismatch")
  IO.println "LOCAL_BLOCK_COMPILED_PASS: dirty bool/u8/two Fn fields; seven-cell writeback and completed horizons"

theorem code_completes : (runLocalBlock ctx code policy 32 initial).isSome = true := by decide
def completedWitness : Nonempty (LocalBlockOutcome ctx ⟨false,false⟩) :=
  ⟨(runLocalBlock ctx code policy 32 initial).get code_completes⟩

def memoryRef : SourceLocalRef LocalWordView.ctx := ⟨.there .here⟩
def memoryShape : DeclaredSourceTypeD LocalWordView.ctx.env memoryRef.ty .memory :=
  .basic (.reference .bytesMemory)
example (values : WordCells (localExternalTypes LocalWordView.ctx)) :
    (writebackLocalWords LocalWordView.ctx LocalWordView.extended values).get memoryRef.index =
      LocalWordView.extended.get memoryRef.index :=
  writebackLocalWords_zero LocalWordView.ctx LocalWordView.extended values memoryRef memoryShape rfl

def retagged := writebackLocalWords ctx initial.1 (localWordCells ctx initial.1)
example : localWordCells ctx retagged = localWordCells ctx initial.1 :=
  writebackLocalWords_view ctx initial.1 (localWordCells ctx initial.1)
example : ((initial.1.get .here).clean?).isSome = true := rfl
example : ((retagged.get .here).clean?).isNone = true := by decide

def completed := (runLocalBlock ctx code policy 32 initial).get code_completes
example : snapshot completed.state =
    [2,2^256-1,2309737967,257,22136,2^256-1,171*2^248] := by decide

def cellWitness : Nonempty (SourceFunctionCell ctx) := ⟨sourceFunctionAt ctx second⟩
def stateWitness : Nonempty (LocalState env ctx.tys) := ⟨initial⟩
#check @localWordCells_write
#check @writebackLocalWords_view
#check @writebackLocalWords_zero
#check @runLocalBlock_projection
#check @runLocalBlock_world
#check @runLocalBlock_stable
#print axioms localWordCells_write
#print axioms writebackLocalWords_view
#print axioms runLocalBlock_projection
end Solidity.Yul.Checks.LocalBlock
