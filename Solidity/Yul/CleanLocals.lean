import Solidity.Yul.LocalValues
import Solidity.Yul.LocalProjection
import Solidity.Source.ExprProgress

/-! Canonical clean scalar initialization uses the ACTUAL Source.Val.word,
including signed extension and left-aligned bytes. Raw assignments do not
invoke this encoder. Compiler/Source-session correspondence is separate. -/
namespace Solidity.Yul

theorem source_intWord (value : Int) : Solidity.Source.intWord value = iword value := by
  have two : ((2 : Nat) : Int) = (2 : Int) := rfl
  simp only [Solidity.Source.intWord,Solidity.Source.toWord,iword,word,Int.natCast_pow,two]

theorem SourceScalarD.keyable {ty encoding} (shape : SourceScalarD ty encoding) :
    ty.keyable = true := by cases shape <;> rfl

theorem SourceScalarD.word_isSome {D ty encoding} (shape : SourceScalarD ty encoding)
    (value : Solidity.Source.Val D ty) : value.word.isSome = true :=
  Solidity.Source.Val.word_isSome shape.keyable value

theorem declared_underlying {env : Solidity.Source.Env} {name decl elem}
    (lookup : env.declOf .udvt name = some decl) (node : UdvtNodeD decl.node elem) :
    env.layout.underlying name = elem.ty .memory := by
  have found := List.find?_some lookup
  simp only [Bool.and_eq_true,beq_iff_eq] at found
  rcases decl with ⟨kind,declName,scope,top,term⟩
  have same : kind = .udvt := found.1.1
  subst kind
  cases term <;> cases node <;> simp only [Solidity.Source.Env.layout,lookup]

theorem DeclaredSourceTypeD.word_isSome {env ty encoding}
    (shape : DeclaredSourceTypeD env ty (.value encoding))
    (value : Solidity.Source.Val env.layout ty) : value.word.isSome = true := by
  cases shape with
  | basic basic =>
      cases basic with
      | scalar scalar => exact scalar.word_isSome value
      | reference reference => cases reference
  | enum lookup node range => exact Solidity.Source.Val.word_isSome rfl value
  | udvt lookup node scalar =>
      have underlying := declared_underlying lookup node
      cases value with
      | udvt inner =>
          change inner.word.isSome = true
          exact (underlying.symm ▸ scalar).word_isSome inner
      | memRef impossible _ | storRef impossible _ | cdRef impossible _ => cases impossible

namespace LocalValue

/-- Read raw constructors unchanged; only existing clean constructors use the
existing Source encoder. No write cleanup or physical/function pointer guess. -/
def readScalar {env ty encoding} (value : LocalValue env ty)
    (shape : DeclaredSourceTypeD env ty (.value encoding)) : Option Word := by
  apply LocalValue.casesOn (motive := fun ty _ =>
    DeclaredSourceTypeD env ty (.value encoding) → Option Word) value
  case clean => intro ty value; exact fun _ => value.word
  case scalar => intro ty other certificate raw; exact fun _ => some raw
  case externalFunction => intro params rets mutability address selector; exact fun _ => none
  exact shape

theorem readScalar_clean {env ty encoding} (value : Solidity.Source.Val env.layout ty)
    (shape : DeclaredSourceTypeD env ty (.value encoding)) :
    readScalar (.clean value) shape = value.word := rfl

theorem readScalar_raw {env ty encoding other}
    (written : DeclaredSourceTypeD env ty (.value other))
    (read : DeclaredSourceTypeD env ty (.value encoding)) (raw : Word) :
    readScalar (.scalar written raw) read = some raw := rfl

def initializeScalar {env ty encoding}
    (shape : DeclaredSourceTypeD env ty (.value encoding))
    (value : Solidity.Source.Val env.layout ty) : LocalValue env ty :=
  .scalar shape (value.word.get (shape.word_isSome value))

theorem initialize_read {env ty encoding}
    (shape : DeclaredSourceTypeD env ty (.value encoding))
    (value : Solidity.Source.Val env.layout ty) :
    readScalar (initializeScalar shape value) shape = value.word := by
  exact Option.some_get (shape.word_isSome value)

theorem clean_read_total {env ty encoding}
    (shape : DeclaredSourceTypeD env ty (.value encoding))
    (value : Solidity.Source.Val env.layout ty) :
    (readScalar (.clean value) shape).isSome = true := shape.word_isSome value

end LocalValue

namespace SourceScalarCell
def localWordRead? {ctx} (cell : SourceScalarCell ctx)
    (locals : LocalValues ctx.env ctx.tys) : Option Word :=
  (locals.get cell.ref.index).readScalar cell.shape

theorem localWordRead_write {ctx} (cell : SourceScalarCell ctx)
    (locals : LocalValues ctx.env ctx.tys) (raw : Word) :
    cell.localWordRead? (cell.localWrite locals raw) = some raw := by
  unfold localWordRead? localWrite LocalValues.writeScalar
  rw [LocalValues.get_set]
  rfl

theorem localWordRead_ofClean {ctx} (cell : SourceScalarCell ctx)
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) :
    cell.localWordRead? (LocalValues.ofClean locals) =
      (locals.get cell.ref.index).word := by
  unfold localWordRead?
  rw [LocalValues.get_ofClean]
  rfl
def cleanWord {ctx} (cell : SourceScalarCell ctx)
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) : Word :=
  (locals.get cell.ref.index).word.get (cell.shape.word_isSome _)

theorem cleanWord_read {ctx} (cell : SourceScalarCell ctx)
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) :
    some (cell.cleanWord locals) = cell.localWordRead? (LocalValues.ofClean locals) := by
  rw [localWordRead_ofClean]
  exact Option.some_get (cell.shape.word_isSome _)

end SourceScalarCell
def SourceScalarView.ofClean {ctx}
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) : SourceScalarView ctx :=
  fun cell => cell.cleanWord locals

/-- The actual generated local context and reverse occurrence map, initialized
from real clean Source locals. No abstract snapshot/agreement premise. -/
def cleanLocalScalars (ctx : Solidity.Source.Ctx)
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) :
    ScalarView (localExternalTypes ctx) :=
  projectLocalScalars ctx (SourceScalarView.ofClean locals)

theorem cleanLocalScalars_agree (ctx : Solidity.Source.Ctx)
    (locals : Solidity.Source.Locals ctx.env.layout ctx.tys) :
    ScalarViewsAgree (localScalarBindings ctx) (cleanLocalScalars ctx locals)
      (SourceScalarView.ofClean locals) :=
  projectLocalScalars_agree ctx (SourceScalarView.ofClean locals)

end Solidity.Yul
