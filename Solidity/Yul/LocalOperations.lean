import Solidity.Yul.LocalWordWrite

/-! Explicit LOCAL operation boundaries using the existing Source value
operations. Raw writes/copies remain raw. These adapters project operands only
when explicitly called; they are not the old Source RExpr/session evaluator or
a universal compiler-pipeline theorem. -/
namespace Solidity.Yul.LocalOperations

def boolShape (env : Solidity.Source.Env) :
    DeclaredSourceTypeD env .bool (.value .boolean) := .basic (.scalar .bool)
def u8Shape (env : Solidity.Source.Env) :
    DeclaredSourceTypeD env (.int Solidity.Source.IntTy.u8) (.value (.unsigned 0)) :=
  .basic (.scalar (.int _ 0 rfl))

def scalarWord {env ty encoding} (value : LocalValue env ty)
    (shape : DeclaredSourceTypeD env ty (.value encoding)) : Word :=
  (value.readScalar shape).get (value.readScalar_total shape)

theorem scalarWord_raw {env ty encoding other} (raw : Word)
    (written : DeclaredSourceTypeD env ty (.value other))
    (read : DeclaredSourceTypeD env ty (.value encoding)) :
    scalarWord (.scalar written raw) read = raw := rfl

theorem scalarWord_clean {env ty encoding} (value : Solidity.Source.Val env.layout ty)
    (shape : DeclaredSourceTypeD env ty (.value encoding)) :
    some (scalarWord (.clean value) shape) = value.word :=
  Option.some_get (x := value.word) (shape.word_isSome value)

def boolInput {env} (value : LocalValue env .bool) : Solidity.Source.Val env.layout .bool :=
  .bool ((scalarWord value (boolShape env)).val != 0)

theorem boolInput_clean {env} (b : Bool) :
    boolInput (env := env) (.clean (.bool b)) = .bool b := by
  cases b <;> rfl

theorem boolInput_raw {env} (raw : Word) :
    boolInput (.scalar (boolShape env) raw) = .bool (raw.val != 0) := rfl

def u8Input {env} (value : LocalValue env (.int Solidity.Source.IntTy.u8)) :
    Solidity.Source.Val env.layout (.int Solidity.Source.IntTy.u8) :=
  let raw := scalarWord value (u8Shape env)
  .int ((raw.val % 256 : Nat) : Int) (by
    have bound := Nat.mod_lt raw.val (by decide : 0 < 256)
    change 0 ≤ ((raw.val % 256 : Nat) : Int) ∧ ((raw.val % 256 : Nat) : Int) ≤ 255
    omega)

/-- Clean, already bounded Source uint8 values are unchanged by the explicit
input projection. Uses the existing Source ABI integer roundtrip theorem. -/
theorem u8Input_clean {env} (value : Int)
    (bound : Solidity.Source.IntTy.u8.lo ≤ value ∧ value ≤ Solidity.Source.IntTy.u8.hi) :
    u8Input (env := env) (.clean (.int value bound)) = .int value bound := by
  let raw := scalarWord (LocalValue.clean (.int value bound)) (u8Shape env)
  have encoded := scalarWord_clean (Solidity.Source.Val.int (D := env.layout) value bound) (u8Shape env)
  have decoded := Solidity.Source.Val.word_int (D := env.layout) value bound
  rw [← encoded] at decoded
  change Solidity.Source.readInt Solidity.Source.IntTy.u8 raw = some value at decoded
  change (if 0 ≤ (raw.val : Int) ∧ (raw.val : Int) ≤ 255 then
    some (raw.val : Int) else none) = some value at decoded
  split at decoded
  · rename_i range
    have equal := Option.some.inj decoded
    have small : raw.val < 256 := by omega
    have modulo := Nat.mod_eq_of_lt small
    change Solidity.Source.Val.int (D := env.layout) ((raw.val % 256 : Nat) : Int) _ = _
    congr 1
    exact (congrArg Int.ofNat modulo).trans equal
  · cases decoded

/-- Actual Source !, returning its typed result or exact Source halt. -/
def boolNot {env} (value : LocalValue env .bool) : Solidity.Source.R (LocalValue env .bool) :=
  (Solidity.Source.unaryVal false .not (boolInput value)).map LocalValue.clean

def boolBinary {env} (op : Solidity.Source.BinOp) (left right : LocalValue env .bool) :
    Solidity.Source.R (LocalValue env .bool) :=
  (Solidity.Source.binVal false op (boolInput left) (boolInput right)).map LocalValue.clean

def boolCompare {env} (op : Solidity.Source.BinOp) (left right : LocalValue env .bool) :
    Solidity.Source.R Bool :=
  Solidity.Source.cmpVal op (boolInput left) (boolInput right)

def u8Binary {env} (checked : Bool) (op : Solidity.Source.BinOp)
    (left right : LocalValue env (.int Solidity.Source.IntTy.u8)) :
    Solidity.Source.R (LocalValue env (.int Solidity.Source.IntTy.u8)) :=
  (Solidity.Source.binVal checked op (u8Input left) (u8Input right)).map LocalValue.clean

theorem boolNot_clean {env} (b : Bool) :
    boolNot (env := env) (.clean (.bool b)) = .ok (.clean (.bool (!b))) := by
  unfold boolNot
  rw [boolInput_clean]
  rfl

theorem boolNot_raw {env} (raw : Word) :
    boolNot (.scalar (boolShape env) raw) =
      .ok (.clean (.bool (!(raw.val != 0)))) := rfl

/-- Actual zero-divisor Source panic, in BOTH arithmetic modes, after the
explicit low-eight-bit operation boundary. Yul's pure div remains zero. -/
theorem u8_div_zero {env} (checked : Bool)
    (left : LocalValue env (.int Solidity.Source.IntTy.u8)) :
    u8Binary checked .div left (.scalar (u8Shape env) (word 256)) =
      .error (.revert (Solidity.Source.panicData .divZero)) := by
  unfold u8Binary u8Input
  simp only [Solidity.Source.binVal,Solidity.Source.intBin,scalarWord_raw]
  have zero : (word 256).val % 256 = 0 := by decide
  rw [zero]
  rfl

theorem u8_mod_zero {env} (checked : Bool)
    (left : LocalValue env (.int Solidity.Source.IntTy.u8)) :
    u8Binary checked .mod left (.scalar (u8Shape env) (word 256)) =
      .error (.revert (Solidity.Source.panicData .divZero)) := by
  unfold u8Binary u8Input
  simp only [Solidity.Source.binVal,Solidity.Source.intBin,scalarWord_raw]
  have zero : (word 256).val % 256 = 0 := by decide
  rw [zero]
  rfl

/-- Compiler pipeline is an explicit input to the LOCAL boundary model.
The concrete unchecked-add slice below records the pinned pipeline difference;
it is not a proof of compiler agreement for arbitrary programs/words. -/
abbrev Pipeline := Solidity.Roadmap.Pipeline

/-- Legacy unchecked arithmetic can leave dirty high bits observable to a later
assembly block. ViaIR's uint8 helper wraps at this boundary. No raw write cleans. -/
def uncheckedU8Add {env} (pipeline : Pipeline)
    (left right : LocalValue env (.int Solidity.Source.IntTy.u8)) :
    Solidity.Source.R (LocalValue env (.int Solidity.Source.IntTy.u8)) :=
  match pipeline with
  | .legacy => .ok (.scalar (u8Shape env)
      (word ((scalarWord left (u8Shape env)).val + (scalarWord right (u8Shape env)).val)))
  | .viaIR => u8Binary false .add left right

theorem uncheckedU8Add_legacy {env} (left right : Word) :
    uncheckedU8Add .legacy (.scalar (u8Shape env) left) (.scalar (u8Shape env) right) =
      .ok (.scalar (u8Shape env) (word (left.val + right.val))) := rfl

theorem uncheckedU8Add_viaIR {env} (left right : LocalValue env (.int Solidity.Source.IntTy.u8)) :
    uncheckedU8Add .viaIR left right = u8Binary false .add left right := rfl

/-- Raw typed copying does not invoke any operand projection. -/
def copy {env ctx ty} (locals : LocalValues env ctx)
    (target source : Solidity.Source.Idx ctx ty) : LocalValues env ctx :=
  locals.set target (locals.get source)

theorem copy_read {env ctx ty} (locals : LocalValues env ctx)
    (target source : Solidity.Source.Idx ctx ty) :
    (copy locals target source).get target = locals.get source :=
  LocalValues.get_set locals target (locals.get source)

/-- Typed assignment of an actual operation result. Errors carry their original
halt; no implicit raw-local cleanup is applied elsewhere. -/
def assign {env ctx ty} (locals : LocalValues env ctx)
    (index : Solidity.Source.Idx ctx ty) (result : Solidity.Source.R (LocalValue env ty)) :
    Solidity.Source.R (LocalValues env ctx) := result.map (locals.set index)

theorem assign_error {env ctx ty} (locals : LocalValues env ctx)
    (index : Solidity.Source.Idx ctx ty) (halt : Solidity.Source.Halt) :
    assign locals index (.error halt) = .error halt := rfl

theorem assign_read {env ctx ty} (locals : LocalValues env ctx)
    (index : Solidity.Source.Idx ctx ty) (value : LocalValue env ty) :
    (assign locals index (.ok value)).map (fun after => after.get index) = .ok value := by
  change Except.ok ((locals.set index value).get index) = _
  rw [LocalValues.get_set]

theorem assign_other {env ctx ty otherTy} (locals : LocalValues env ctx)
    (index : Solidity.Source.Idx ctx ty) (other : Solidity.Source.Idx ctx otherTy)
    (different : index.toNat ≠ other.toNat) (value : LocalValue env ty) :
    (assign locals index (.ok value)).map (fun after => after.get other) =
      .ok (locals.get other) := by
  change Except.ok ((locals.set index value).get other) = _
  rw [LocalValues.get_set_other locals index other value different]

/-- All clean values at the actual uint8 Source type have the existing
bounded integer constructor; explicit input projection is the identity. -/
theorem u8Input_clean_value {env : Solidity.Source.Env}
    (value : Solidity.Source.Val env.layout (.int Solidity.Source.IntTy.u8)) :
    u8Input (.clean value) = value := by
  cases value with
  | int value bound => exact u8Input_clean value bound
  | memRef impossible _ => cases impossible
  | storRef impossible _ => cases impossible
  | cdRef impossible _ => cases impossible

theorem u8Binary_clean {env : Solidity.Source.Env} (checked : Bool) (op : Solidity.Source.BinOp)
    (left right : Solidity.Source.Val env.layout (.int Solidity.Source.IntTy.u8)) :
    u8Binary checked op (.clean left) (.clean right) =
      (Solidity.Source.binVal checked op left right).map LocalValue.clean := by
  unfold u8Binary
  rw [u8Input_clean_value,u8Input_clean_value]

end Solidity.Yul.LocalOperations
