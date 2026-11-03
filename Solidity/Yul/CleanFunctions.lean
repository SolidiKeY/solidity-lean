import Solidity.Yul.CleanLocals

/-! Canonical clean external-function LOCAL fields, separate from packed ABI
function values and from physical/code-pointer semantics. Address and selector
are two words; raw fields are never masked on write/read. -/
namespace Solidity.Yul

def cleanFunctionFields {D ty} (value : Solidity.Source.Val D ty) :
    Option (Word × Word) := by
  apply Solidity.Source.Val.casesOn (motive := fun _ _ => Option (Word × Word)) value
  case externalFn =>
    intro params rets mutability address selector valid
    exact some (word address.val,word (Solidity.Source.beValue selector))
  all_goals intros; exact none

theorem DeclaredSourceTypeD.function_ty {env ty}
    (shape : DeclaredSourceTypeD env ty .externalFunction) :
    ∃ params rets mutability, ty = .fn true params rets mutability := by
  cases shape with
  | basic basic =>
      cases basic with
      | reference reference =>
          cases reference
          exact ⟨_,_,_,rfl⟩

theorem cleanFunctionFields_total {env ty}
    (shape : DeclaredSourceTypeD env ty .externalFunction)
    (value : Solidity.Source.Val env.layout ty) :
    (cleanFunctionFields value).isSome = true := by
  obtain ⟨params,rets,mutability,rfl⟩ := shape.function_ty
  cases value with
  | externalFn address selector valid => rfl
  | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

namespace LocalValue

def readFunctionFields {env ty} (value : LocalValue env ty)
    (shape : DeclaredSourceTypeD env ty .externalFunction) : Option (Word × Word) := by
  apply LocalValue.casesOn (motive := fun ty _ =>
    DeclaredSourceTypeD env ty .externalFunction → Option (Word × Word)) value
  case clean => intro ty value; exact fun _ => cleanFunctionFields value
  case scalar => intro ty encoding certificate raw; exact fun _ => none
  case externalFunction =>
    intro params rets mutability address selector
    exact fun _ => some (address,selector)
  exact shape

theorem readFunctionFields_clean {env ty}
    (shape : DeclaredSourceTypeD env ty .externalFunction)
    (value : Solidity.Source.Val env.layout ty) :
    readFunctionFields (.clean value) shape = cleanFunctionFields value := rfl

theorem readFunctionFields_raw {env params rets mutability}
    (shape : DeclaredSourceTypeD env (.fn true params rets mutability) .externalFunction)
    (address selector : Word) :
    readFunctionFields (.externalFunction params rets mutability address selector) shape =
      some (address,selector) := rfl

theorem readFunctionFields_total {env ty} (value : LocalValue env ty)
    (shape : DeclaredSourceTypeD env ty .externalFunction) :
    (readFunctionFields value shape).isSome = true := by
  cases value with
  | clean value => exact cleanFunctionFields_total shape value
  | scalar certificate raw =>
      have impossible := DeclaredSourceTypeD.unique certificate shape
      cases impossible
  | externalFunction params rets mutability address selector => rfl

/-- Construct only at an actual external-function Source type. This matches on
the type itself, not an indexed value. It supplies no unknown pointer default. -/
def rawFunction {env} (ty : Solidity.Source.STy) (address selector : Word) :
    Option (LocalValue env ty) :=
  match ty with
  | .fn true params rets mutability =>
      some (.externalFunction params rets mutability address selector)
  | _ => none

theorem rawFunction_total {env ty}
    (shape : DeclaredSourceTypeD env ty .externalFunction) (address selector : Word) :
    (rawFunction (env := env) ty address selector).isSome = true := by
  obtain ⟨params,rets,mutability,rfl⟩ := shape.function_ty
  rfl

theorem rawFunction_read {env ty}
    (shape : DeclaredSourceTypeD env ty .externalFunction) (address selector : Word) :
    readFunctionFields ((rawFunction ty address selector).get
      (rawFunction_total shape address selector)) shape = some (address,selector) := by
  obtain ⟨params,rets,mutability,rfl⟩ := shape.function_ty
  rfl

def initializeFunction {env ty} (shape : DeclaredSourceTypeD env ty .externalFunction)
    (value : Solidity.Source.Val env.layout ty) : LocalValue env ty :=
  let fields := (cleanFunctionFields value).get (cleanFunctionFields_total shape value)
  (rawFunction ty fields.1 fields.2).get (rawFunction_total shape fields.1 fields.2)

theorem initializeFunction_read {env ty}
    (shape : DeclaredSourceTypeD env ty .externalFunction)
    (value : Solidity.Source.Val env.layout ty) :
    readFunctionFields (initializeFunction shape value) shape = cleanFunctionFields value := by
  obtain ⟨params,rets,mutability,rfl⟩ := shape.function_ty
  change some ((cleanFunctionFields value).get (cleanFunctionFields_total shape value)) = _
  exact Option.some_get (cleanFunctionFields_total shape value)

end LocalValue
end Solidity.Yul
