import Solidity.Yul.LocalWordView
import Solidity.Yul.Checks.CleanLocals
namespace Solidity.Yul.Checks.LocalWordView
open Solidity.Source
def env : Solidity.Source.Env := ⟨[]⟩
def functionTy : STy := .fn true [.bool] [.int IntTy.u8] (some .view)
def functionShape : DeclaredSourceTypeD env functionTy .externalFunction :=
  .basic (.reference (.externalFunction _ _ _))
def functionValue : Solidity.Source.Val env.layout functionTy :=
  .externalFn ⟨4660,by decide⟩ [137,171,205,239] rfl
def maxWord := word (2^256-1)
def topWord := word (2^255+85)

example : cleanFunctionFields functionValue = some (word 4660,word 2309737967) := by decide
example : functionValue.word = none := rfl
example : (Solidity.Source.Val.fixedBytes (D := env.layout) (n := 4) (h := by decide) [137,171,205,239] rfl).word =
    some (word (2309737967*2^224)) := by decide
example : LocalValue.readFunctionFields (LocalValue.initializeFunction functionShape functionValue)
    functionShape = some (word 4660,word 2309737967) := by decide
example : LocalValue.readFunctionFields
    (.externalFunction [.bool] [.int IntTy.u8] (some .view) maxWord topWord) functionShape =
      some (maxWord,topWord) := rfl
example : LocalValue.rawFunction (env := env) (.fn false [] [] none) (word 1) (word 2) =
    none := rfl
example : LocalValue.rawFunction (env := env) (.bytes .memory) (word 1) (word 2) = none := rfl
example : cleanFunctionFields (Solidity.Source.Val.internalFn (D := env.layout)
    (ps := []) (rs := []) (m := none) ⟨none,"f"⟩) = none := rfl

def ctx : Solidity.Source.Ctx :=
  {env:=env,scope:=none,locals:=[("flag",.bool),("memory",.bytes .memory),
    ("ptr",functionTy),("small",.int IntTy.u8),("byte",.fixedBytes 1 (by decide))]}
def locals : Solidity.Source.Locals env.layout ctx.tys :=
  .cons (.bool true) (.cons (.memRef rfl 64) (.cons functionValue
    (.cons CleanLocals.small (.cons CleanLocals.byteValue .nil))))
def extended := LocalValues.ofClean locals
def index : Member (localExternalTypes ctx) .externalFunction := .there (.there .here)
def functionCell := sourceFunctionAt ctx index
def scalar : ScalarRef (localExternalTypes ctx) := ⟨.unsigned 0,.there (.there (.there .here))⟩
def initialized := initialLocalWordState ctx locals
def addressed := functionCell.writeAddress extended maxWord
def selected := functionCell.writeSelector addressed topWord

example : wordCellCount (localExternalTypes ctx) = 5 := rfl
example : initialized.cells (.address index) = word 4660 := by decide
example : initialized.cells (.selector index) = word 2309737967 := by decide
example : initialized.cells (.scalar scalar) = word 1 := rfl
example : functionCell.fields addressed = (maxWord,word 2309737967) := by decide
example : functionCell.fields selected = (maxWord,topWord) := by decide
example : localWordCells ctx selected (.address index) = maxWord := by decide
example : localWordCells ctx selected (.selector index) = topWord := by decide
example : localWordCells ctx selected (.scalar scalar) = word 1 := rfl
example (address selector : Word) :
    functionCell.fields (functionCell.writeFields extended address selector) = (address,selector) :=
  functionCell.fields_writeFields extended address selector

def fieldWitness : Nonempty (SourceFunctionCell ctx) := ⟨functionCell⟩
def stateWitness : Nonempty (WordState (localExternalTypes ctx) 0) := ⟨initialized⟩
#check @cleanFunctionFields_total
#check @LocalValue.initializeFunction_read
#check @SourceFunctionCell.fields_writeAddress
#check @SourceFunctionCell.fields_writeSelector
#check @initialLocalWordState
#print axioms LocalValue.initializeFunction_read
#print axioms SourceFunctionCell.fields_writeFields
/-- info: LOCAL_WORD_VIEW_COMPILED_PASS: actual Source function fields, raw updates, mixed 5-word state -/
#guard_msgs in
#eval do
  unless functionCell.fields selected == (maxWord,topWord) &&
      initialized.cells (.selector index) == word 2309737967 &&
      localWordCells ctx selected (.scalar scalar) == word 1 do
    throw (IO.userError "actual Source function-field/word-state mismatch")
  let packed := initialized.pack
  unless packed ⟨0,by decide⟩ == word 1 && packed ⟨1,by decide⟩ == word 4660 &&
      packed ⟨2,by decide⟩ == word 2309737967 && packed ⟨3,by decide⟩ == word 1 &&
      packed ⟨4,by decide⟩ == word (171*2^248) do
    throw (IO.userError "actual initialized packed word-state mismatch")
  IO.println "LOCAL_WORD_VIEW_COMPILED_PASS: actual Source function fields, raw updates, mixed 5-word state"
end Solidity.Yul.Checks.LocalWordView
