import Solidity.Yul.LocalValues
import Solidity.Yul.Checks.SourceBoundary

/-! Typed local representation controls. These test explicit operations, not
compiler pipeline cleanup or a general Source execution embedding. -/
namespace Solidity.Yul.Checks.LocalValues

def env : Solidity.Source.Env := ⟨[]⟩
def boolShape : DeclaredSourceTypeD env .bool (.value .boolean) := .basic (.scalar .bool)
def u8Shape : DeclaredSourceTypeD env (.int Solidity.Source.IntTy.u8)
    (.value (.unsigned 0)) := .basic (.scalar (.int _ 0 rfl))

def initial : Solidity.Source.Locals env.layout
    [.bool, .int Solidity.Source.IntTy.u8] :=
  .cons (.bool false) (.cons (.int 0 (by decide)) .nil)
def extended := LocalValues.ofClean initial
def dirty := (extended.writeScalar .here boolShape (word 2)).writeScalar
  (.there .here) u8Shape (word 257)

example : (dirty.get .here).scalar? = some (word 2) := rfl
example : (dirty.get (.there .here)).scalar? = some (word 257) := rfl
example : (dirty.get .here).clean? = none := rfl
example : LocalValues.clean? _ dirty = none := rfl
example : LocalValues.clean? _ extended = some initial := LocalValues.clean_ofClean initial
example : (LocalValue.cleanBool (env := env) (word 2)).clean? =
    some (.bool true) := rfl
example : (LocalValue.cleanBool (env := env) (word 0)).clean? =
    some (.bool false) := rfl
example : ((LocalValue.cleanU8 (env := env) (word 257)).clean?).map
    Solidity.Source.Val.key = some (some 1) := by decide
example : (LocalValue.lowBits 0 (word 257)).val = 1 := by decide
example : (LocalValue.lowBits 0 (word (2^256-1))).val = 255 := by decide
example : (LocalValue.lowBits 31 (word (2^256-1))).val = 2^256-1 := by decide
example (raw : Word) :
    ((extended.writeScalar .here boolShape raw).get .here).scalar? = some raw :=
  LocalValues.read_writeScalar extended .here boolShape raw
example : (LocalValue.externalFunction (env := env) [] [] (some .view)
    (word (2^256-1)) (word (2^256-1))).clean? = none := rfl

example : ((extended.writeScalar .here boolShape (word 0)).get .here).clean? = none := rfl
example : ((extended.writeScalar .here boolShape (word 1)).get .here).scalar? =
    some (word 1) := rfl
example : ((LocalValue.cleanU8 (env := env) (word 255)).clean?).map
    Solidity.Source.Val.key = some (some 255) := by decide
example : ((LocalValue.cleanU8 (env := env) (word 256)).clean?).map
    Solidity.Source.Val.key = some (some 0) := by decide
example : ((LocalValue.cleanU8 (env := env) (word (2^256-1))).clean?).map
    Solidity.Source.Val.key = some (some 255) := by decide
example : ((extended.writeScalar .here boolShape (word 2)).get (.there .here)).clean? =
    some (.int 0 (by decide)) := rfl
def repeated : LocalValues env [.bool,.bool] :=
  (.scalar boolShape (word 2), (.scalar boolShape (word 3), ()))
example : ((repeated.set .here (.scalar boolShape (word 4))).get (.there .here)).scalar? =
    some (word 3) := rfl
example : ((repeated.set (.there .here) (.scalar boolShape (word 5))).get .here).scalar? =
    some (word 2) := rfl

/-- Actual S01 occurrence selected by the existing checked Source binding. -/
def actualInitial : LocalValues SourceBoundary.ctx.env SourceBoundary.ctx.tys :=
  (.clean (.bool false), ())
example (raw : Word) :
    SourceBoundary.sourceCell.localRead?
      (SourceBoundary.sourceCell.localWrite actualInitial raw) = some raw :=
  SourceBoundary.sourceCell.localRead_write actualInitial raw

def dirtyWitness : ∃ locals : LocalValues env [.bool,.int Solidity.Source.IntTy.u8],
    (locals.get .here).scalar? = some (word 2) ∧
      (locals.get (.there .here)).scalar? = some (word 257) :=
  ⟨dirty,rfl,rfl⟩
def extendedWitness : Nonempty (LocalValues env [.bool,.int Solidity.Source.IntTy.u8]) :=
  ⟨dirty⟩

#print axioms LocalValues.read_writeScalar
#print axioms LocalValues.clean_ofClean
end Solidity.Yul.Checks.LocalValues
