import Solidity.Yul.SourceTypes
import Solidity.Yul.ScalarLocals
import Solidity.Yul.Words
import Solidity.Source.Machine

/-! Typed LOCAL extension for assembly. Raw writes preserve all bits. The old
Source value and local types are unchanged. Explicit cleaning operations below
are mathematical projections, not an assertion about a compiler pipeline. -/
namespace Solidity.Yul

inductive LocalValue (env : Solidity.Source.Env) : Solidity.Source.STy → Type where
  | clean {ty} : Solidity.Source.Val env.layout ty → LocalValue env ty
  | scalar {ty encoding} : DeclaredSourceTypeD env ty (.value encoding) →
      Word → LocalValue env ty
  | externalFunction (params rets mutability) (address selector : Word) :
      LocalValue env (.fn true params rets mutability)

namespace LocalValue

def clean? {env ty} (value : LocalValue env ty) :
    Option (Solidity.Source.Val env.layout ty) := by
  apply LocalValue.casesOn (motive := fun ty _ =>
    Option (Solidity.Source.Val env.layout ty)) value
  case clean => intro ty clean; exact some clean
  case scalar => intro ty encoding shape raw; exact none
  case externalFunction => intro params rets mutability address selector; exact none

def scalar? {env ty} (value : LocalValue env ty) : Option Word := by
  apply LocalValue.casesOn (motive := fun _ _ => Option Word) value
  case clean => intro ty clean; exact none
  case scalar => intro ty encoding shape raw; exact some raw
  case externalFunction => intro params rets mutability address selector; exact none

/-- Assignment preserves the declared type evidence and every raw bit. -/
def writeScalar {env ty encoding}
    (shape : DeclaredSourceTypeD env ty (.value encoding)) (raw : Word) :
    LocalValue env ty := .scalar shape raw

theorem read_write {env ty encoding}
    (shape : DeclaredSourceTypeD env ty (.value encoding)) (raw : Word) :
    (writeScalar shape raw).scalar? = some raw := rfl

theorem raw_not_clean {env ty encoding}
    (shape : DeclaredSourceTypeD env ty (.value encoding)) (raw : Word) :
    (writeScalar shape raw).clean? = none := rfl

/-- Explicit boolean cleanup. Calling this operation changes the representation;
it never runs implicitly on an assembly write. -/
def cleanBool {env : Solidity.Source.Env} (raw : Word) : LocalValue env .bool :=
  .clean (.bool (raw.val != 0))

theorem cleanBool_key {env : Solidity.Source.Env} (raw : Word) :
    ((cleanBool (env := env) raw).clean?).map Solidity.Source.Val.key =
      some (some (if raw.val != 0 then 1 else 0)) := rfl

/-- Explicit uint8 projection into the existing bounded Source value. -/
def cleanU8 {env : Solidity.Source.Env} (raw : Word) :
    LocalValue env (.int Solidity.Source.IntTy.u8) :=
  .clean (.int ((raw.val % 256 : Nat) : Int) (by
    have bound := Nat.mod_lt raw.val (by decide : 0 < 256)
    have lo : Solidity.Source.IntTy.u8.lo = 0 := by decide
    have hi : Solidity.Source.IntTy.u8.hi = 255 := by decide
    rw [lo, hi]
    omega))

theorem cleanU8_key {env : Solidity.Source.Env} (raw : Word) :
    ((cleanU8 (env := env) raw).clean?).map Solidity.Source.Val.key =
      some (some ((raw.val % 256 : Nat) : Int)) := rfl

/-- An explicit unsigned low-bit projection, retaining a full word result.
No raw assignment invokes it. -/
def lowBits (width : Fin 32) (raw : Word) : Word :=
  word (raw.val % (2 ^ (8 * (width.val + 1))))

theorem lowBits_val (width : Fin 32) (raw : Word) :
    (lowBits width raw).val = raw.val % (2 ^ (8 * (width.val + 1))) := by
  have bound : 2 ^ (8 * (width.val + 1)) ≤ 2 ^ 256 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos (by decide))) bound)

end LocalValue

/-- A context-computed environment: no additional indexed local-list AST. -/
def LocalValues (env : Solidity.Source.Env) : Solidity.Source.RCtx → Type
  | [] => Unit
  | ty :: ctx => LocalValue env ty × LocalValues env ctx

namespace LocalValues

def get {env ctx ty} (locals : LocalValues env ctx)
    (index : Solidity.Source.Idx ctx ty) : LocalValue env ty := by
  apply Solidity.Source.Idx.casesOn (motive := fun ctx ty _ =>
    LocalValues env ctx → LocalValue env ty) index
  case here => intro ty ctx; exact fun locals => locals.1
  case there =>
    intro head ty ctx previous
    exact fun locals => get locals.2 previous
  exact locals
termination_by structural index

def set {env ctx ty} (locals : LocalValues env ctx)
    (index : Solidity.Source.Idx ctx ty) (value : LocalValue env ty) :
    LocalValues env ctx := by
  apply Solidity.Source.Idx.casesOn (motive := fun ctx ty _ =>
    LocalValues env ctx → LocalValue env ty → LocalValues env ctx) index
  case here => intro ty ctx; exact fun locals value => (value, locals.2)
  case there =>
    intro head ty ctx previous
    exact fun locals value => (locals.1, set locals.2 previous value)
  exact locals
  exact value
termination_by structural index

def ofClean {env ctx} (locals : Solidity.Source.Locals env.layout ctx) :
    LocalValues env ctx := by
  apply Solidity.Source.Locals.casesOn (motive := fun ctx _ => LocalValues env ctx) locals
  case nil => exact ()
  case cons =>
    intro ty ctx value rest
    exact (.clean value, ofClean rest)
termination_by structural locals

/-- Raw constructors are never implicitly converted, even at clean bit values. -/
def clean? {env} : (ctx : Solidity.Source.RCtx) → LocalValues env ctx →
    Option (Solidity.Source.Locals env.layout ctx)
  | [], _ => some .nil
  | _ :: ctx, locals => do
      let value ← locals.1.clean?
      let rest ← clean? ctx locals.2
      pure (.cons value rest)

theorem clean_ofClean {env : Solidity.Source.Env} {ctx}
    (locals : Solidity.Source.Locals env.layout ctx) :
    clean? ctx (ofClean locals) = some locals := by
  induction locals with
  | nil => rfl
  | cons value rest ih =>
      change (do
        let tail ← clean? _ (ofClean rest)
        pure (Solidity.Source.Locals.cons value tail)) = _
      rw [ih]
      rfl

theorem get_set {env ctx ty} (locals : LocalValues env ctx)
    (index : Solidity.Source.Idx ctx ty) (value : LocalValue env ty) :
    (set locals index value).get index = value := by
  induction index with
  | here => rfl
  | there index ih => exact ih locals.2 value

theorem get_ofClean {env : Solidity.Source.Env} {ctx ty}
    (locals : Solidity.Source.Locals env.layout ctx)
    (index : Solidity.Source.Idx ctx ty) :
    (ofClean locals).get index = .clean (locals.get index) := by
  induction index with
  | here => cases locals; rfl
  | there index ih => cases locals with
    | cons old rest => exact ih rest

/-- A full raw write at an actual typed Source index. -/
def writeScalar {env ctx ty encoding} (locals : LocalValues env ctx)
    (index : Solidity.Source.Idx ctx ty)
    (shape : DeclaredSourceTypeD env ty (.value encoding)) (raw : Word) :
    LocalValues env ctx := locals.set index (.scalar shape raw)

theorem read_writeScalar {env ctx ty encoding} (locals : LocalValues env ctx)
    (index : Solidity.Source.Idx ctx ty)
    (shape : DeclaredSourceTypeD env ty (.value encoding)) (raw : Word) :
    ((locals.writeScalar index shape raw).get index).scalar? = some raw := by
  rw [writeScalar, get_set]
  rfl

end LocalValues
namespace SourceScalarCell

def localRead? {ctx} (cell : SourceScalarCell ctx)
    (locals : LocalValues ctx.env ctx.tys) : Option Word :=
  (locals.get cell.ref.index).scalar?

def localWrite {ctx} (cell : SourceScalarCell ctx)
    (locals : LocalValues ctx.env ctx.tys) (raw : Word) : LocalValues ctx.env ctx.tys :=
  locals.writeScalar cell.ref.index cell.shape raw

theorem localRead_write {ctx} (cell : SourceScalarCell ctx)
    (locals : LocalValues ctx.env ctx.tys) (raw : Word) :
    cell.localRead? (cell.localWrite locals raw) = some raw :=
  LocalValues.read_writeScalar locals cell.ref.index cell.shape raw

end SourceScalarCell
end Solidity.Yul
