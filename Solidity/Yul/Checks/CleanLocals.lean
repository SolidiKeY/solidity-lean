import Solidity.Yul.CleanLocals
import Solidity.Yul.Checks.SourceTypes
namespace Solidity.Yul.Checks.CleanLocals
def env : Solidity.Source.Env := ⟨[]⟩
def boolShape : DeclaredSourceTypeD env .bool (.value .boolean) := .basic (.scalar .bool)
def u8Shape : DeclaredSourceTypeD env (.int Solidity.Source.IntTy.u8)
    (.value (.unsigned 0)) := .basic (.scalar (.int _ 0 rfl))
def i8 : Solidity.Source.IntTy := ⟨true,8,by decide⟩
def i8Shape : DeclaredSourceTypeD env (.int i8) (.value (.signed 0)) :=
  .basic (.scalar (.int _ 0 rfl))
def bytesShape : DeclaredSourceTypeD env (.fixedBytes 1 (by decide))
    (.value (.fixedBytes 0)) := .basic (.scalar (.bytes 1 (by decide) 0 rfl))
def small : Solidity.Source.Val env.layout (.int Solidity.Source.IntTy.u8) := .int 1 (by decide)
def negative : Solidity.Source.Val env.layout (.int i8) := .int (-128) (by decide)
def byteValue : Solidity.Source.Val env.layout (.fixedBytes 1 (by decide)) :=
  .fixedBytes [171] rfl

example : LocalValue.readScalar (.clean (.bool true)) boolShape = some (word 1) := rfl
example : LocalValue.readScalar (.clean (.bool false)) boolShape = some (word 0) := rfl
example : LocalValue.readScalar (.scalar boolShape (word 2)) boolShape = some (word 2) := rfl
example : LocalValue.readScalar (.clean small) u8Shape = some (word 1) := rfl
example : LocalValue.readScalar (.scalar u8Shape (word 257)) u8Shape = some (word 257) := rfl
example : LocalValue.readScalar (.clean negative) i8Shape = some (iword (-128)) := by
  change some (Solidity.Source.intWord (-128)) = _
  rw [source_intWord]
example : LocalValue.readScalar (.scalar i8Shape (word 384)) i8Shape = some (word 384) := rfl
example : LocalValue.readScalar (.clean byteValue) bytesShape =
    some (word (171 * 2^248)) := by decide
example : LocalValue.readScalar (.scalar bytesShape (word (171*2^248+17))) bytesShape =
    some (word (171*2^248+17)) := rfl
example : LocalValue.readScalar (LocalValue.initializeScalar u8Shape small) u8Shape =
    small.word := LocalValue.initialize_read u8Shape small
example : (LocalValue.initializeScalar boolShape (.bool true)).clean? = none := rfl
example : (LocalValue.readScalar (.clean negative) i8Shape).bind
    (Solidity.Source.readInt i8) = some (-128) :=
  Solidity.Source.Val.word_int (-128) (by decide)

def named := Checks.SourceTypes.name
def udvtEnv : Solidity.Source.Env := ⟨[Checks.SourceTypes.udvtDecl .bool]⟩
def udvtShape : DeclaredSourceTypeD udvtEnv (.udvt named) (.value .boolean) :=
  .udvt rfl .intro .bool
def udvtValue : Solidity.Source.Val udvtEnv.layout (.udvt named) := .udvt (.bool true)
example : udvtValue.word = some (word 1) := rfl
example : LocalValue.readScalar (LocalValue.initializeScalar udvtShape udvtValue) udvtShape =
    some (word 1) := rfl
example : udvtEnv.layout.underlying named = .bool :=
  declared_underlying (show udvtEnv.declOf .udvt named = some (Checks.SourceTypes.udvtDecl .bool) from rfl)
    UdvtNodeD.intro

def enumEnv : Solidity.Source.Env := ⟨[Checks.SourceTypes.enumDecl 1]⟩
def enumShape : DeclaredSourceTypeD enumEnv (.enum named) (.value (.unsigned 0)) :=
  .enum rfl (Checks.SourceTypes.enumNode 1) (by decide)
def enumValue : Solidity.Source.Val enumEnv.layout (.enum named) := .enum ⟨1,by decide⟩
example : LocalValue.readScalar (.clean enumValue) enumShape = some (word 1) := rfl

def ctx : Solidity.Source.Ctx :=
  {env:=env,scope:=none,locals:=[("flag",.bool),("memory",.bytes .memory),("small",.int Solidity.Source.IntTy.u8),
    ("byte",.fixedBytes 1 (by decide))]}
def locals : Solidity.Source.Locals env.layout ctx.tys :=
  .cons (.bool true) (.cons (.memRef rfl 64) (.cons small (.cons byteValue .nil)))
example : cleanLocalScalars ctx locals ⟨.boolean,.here⟩ = word 1 := rfl
example : cleanLocalScalars ctx locals ⟨.unsigned 0,.there (.there .here)⟩ = word 1 := rfl
example : cleanLocalScalars ctx locals ⟨.fixedBytes 0,.there (.there (.there .here))⟩ =
    word (171*2^248) := by decide
example : ScalarViewsAgree (localScalarBindings ctx) (cleanLocalScalars ctx locals)
    (SourceScalarView.ofClean locals) := cleanLocalScalars_agree ctx locals

example : (Solidity.Source.Val.memRef (D := env.layout)
    (τ := .bytes .memory) rfl 64).word = none := rfl
example (shape : DeclaredSourceTypeD env (.bytes .memory) (.value .boolean)) : False := by
  have same := DeclaredSourceTypeD.unique shape (.basic (.reference .bytesMemory))
  cases same

def scalarWitness : Nonempty (LocalValue udvtEnv (.udvt named)) :=
  ⟨LocalValue.initializeScalar udvtShape udvtValue⟩
def viewWitness : Nonempty (ScalarView (localExternalTypes ctx)) := ⟨cleanLocalScalars ctx locals⟩
#check @DeclaredSourceTypeD.word_isSome
#check @SourceScalarCell.localWordRead_ofClean
#check @cleanLocalScalars_agree
#print axioms DeclaredSourceTypeD.word_isSome
#print axioms cleanLocalScalars_agree
#eval do
  unless LocalValue.readScalar (.clean negative) i8Shape == some (iword (-128)) &&
      LocalValue.readScalar (.clean byteValue) bytesShape == some (word (171*2^248)) do
    throw (IO.userError "actual Source clean scalar encoding mismatch")
  unless LocalValue.readScalar (.scalar u8Shape (word 257)) u8Shape == some (word 257) do
    throw (IO.userError "raw scalar unexpectedly cleaned")
  unless LocalValue.readScalar (.clean udvtValue) udvtShape == some (word 1) &&
      LocalValue.readScalar (.clean enumValue) enumShape == some (word 1) do
    throw (IO.userError "declared named-value runtime encoding mismatch")
  unless cleanLocalScalars ctx locals ⟨.unsigned 0,.there (.there .here)⟩ == word 1 &&
      cleanLocalScalars ctx locals ⟨.fixedBytes 0,.there (.there (.there .here))⟩ ==
        word (171*2^248) do
    throw (IO.userError "actual generated occurrence runtime encoding mismatch")
  IO.println "CLEAN_LOCAL_COMPILED_PASS: actual Source signed/bytes/UDVT/occurrence encoding; raw257 retained"
end Solidity.Yul.Checks.CleanLocals
