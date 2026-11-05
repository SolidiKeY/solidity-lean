import Solidity.Yul.Words

/-!
# Intrinsic Yul syntax

Local contexts count words; function contexts contain input/output arities.
Control contexts make misplaced leave/break/continue unrepresentable.
Function bodies have exactly their own parameters and zeroed return slots;
they cannot capture outer locals, but retain permitted global Solidity references.
-/
namespace Solidity.Yul

structure Sig where
  args : Nat
  rets : Nat
  deriving DecidableEq, Repr

/-- Positional membership with the selected type in the index. -/
inductive Member {α : Type} : List α → α → Type where
  | here {a : α} {as : List α} : Member (a :: as) a
  | there {a b : α} {as : List α} : Member as a → Member (b :: as) a
  deriving Repr

/-- Value encodings retain width and alignment; they do not clean the raw word.
The `bytes` field stores the byte count MINUS ONE (1–32 bytes). -/
inductive Encoding where
  | unsigned (bytes : Fin 32)
  | signed (bytes : Fin 32)
  | fixedBytes (bytes : Fin 32)
  | boolean
  | address
  deriving DecidableEq, Repr

/-- The actual encoded byte count (numeric fields store width minus one). -/
def Encoding.byteWidth : Encoding → Nat
  | .unsigned w | .signed w | .fixedBytes w => w.val + 1
  | .boolean => 1
  | .address => 20

/-- Solidity declarations available through `externalReferences`. Storage locality
controls assignment to `.slot`; dynamic calldata has two independently writable fields. -/
inductive ExternalType where
  | value (encoding : Encoding)
  | memory
  | calldataStatic
  | calldataDynamic
  | storage (isLocal : Bool) (transient : Bool)
  | externalFunction
  | internalFunction
  | constant (value : Word)
  | library
  deriving DecidableEq, Repr

/-- Global Solidity references remain visible inside a Yul function. Local
value, memory, calldata, storage-pointer and function-pointer variables do not. -/
def ExternalType.isGlobal : ExternalType → Bool
  | .storage false _ | .constant _ | .library => true
  | _ => false

def globals (X : List ExternalType) : List ExternalType := X.filter ExternalType.isGlobal

inductive Attribute where
  | plain | slot | offset | length | selector | address
  deriving DecidableEq, Repr

/-- The documented read/write capabilities, independent of execution support. -/
inductive Access : ExternalType → Attribute → Bool → Type where
  | valueRead {e : Encoding} : Access (.value e) .plain false
  | valueWrite {e : Encoding} : Access (.value e) .plain true
  | memoryRead : Access .memory .plain false
  | memoryWrite : Access .memory .plain true
  | staticRead : Access .calldataStatic .plain false
  | staticWrite : Access .calldataStatic .plain true
  | offsetRead : Access .calldataDynamic .offset false
  | offsetWrite : Access .calldataDynamic .offset true
  | lengthRead : Access .calldataDynamic .length false
  | lengthWrite : Access .calldataDynamic .length true
  | slotRead {l t : Bool} : Access (.storage l t) .slot false
  | slotWrite {t : Bool} : Access (.storage true t) .slot true
  | storageOffset {l t : Bool} : Access (.storage l t) .offset false
  | selectorRead : Access .externalFunction .selector false
  | selectorWrite : Access .externalFunction .selector true
  | addressRead : Access .externalFunction .address false
  | addressWrite : Access .externalFunction .address true
  | constantRead {w : Word} : Access (.constant w) .plain false
  | libraryRead : Access .library .plain false
  | internalRead : Access .internalFunction .plain false
  | internalWrite : Access .internalFunction .plain true
  deriving Repr

structure ExternalRef (X : List ExternalType) (write : Bool) where
  {ty : ExternalType}
  index : Member X ty
  attr : Attribute
  access : Access ty attr write

structure Control where
  function : Bool
  loop : Bool
  deriving DecidableEq, Repr

/-- Expressions are indexed by their exact number of returned words. Operands
are single-valued; multi-return calls are admitted only at multi-value sites. -/
inductive Expr (F : List Sig) (X : List ExternalType) (n : Nat) : Nat → Type where
  | literal : Word → Expr F X n 1
  | «local» : Fin n → Expr F X n 1
  | external : ExternalRef X false → Expr F X n 1
  | builtin {a r : Nat} : Builtin a r → (Fin a → Expr F X n 1) → Expr F X n r
  | call {s : Sig} : Member F s → (Fin s.args → Expr F X n 1) → Expr F X n s.rets

inductive Target (X : List ExternalType) (n : Nat) where
  | «local» : Fin n → Target X n
  | external : ExternalRef X true → Target X n

mutual
/-- A statement preserves its surrounding local context; binders own the rest
of their lexical scope. Function groups are hoisted over their entire block. -/
inductive Stmt : List Sig → List ExternalType → Control → Nat → Type where
  | skip {F X c n} : Stmt F X c n
  | seq {F X c n} : Stmt F X c n → Stmt F X c n → Stmt F X c n
  | assign {F X c n r} : (Fin r → Target X n) → Expr F X n r → Stmt F X c n
  | discard {F X c n} : Expr F X n 0 → Stmt F X c n
  | let_ {F X c n} (r : Nat) : Expr F X n r → Stmt F X c (r + n) → Stmt F X c n
  | zero {F X c n} (r : Nat) : Stmt F X c (r + n) → Stmt F X c n
  | if_ {F X c n} : Expr F X n 1 → Stmt F X c n → Stmt F X c n
  | switch {F X c n} : Expr F X n 1 → Cases F X c n →
      Stmt F X c n → Stmt F X c n
  | for_ {F X c n} : Stmt F X ⟨c.function, false⟩ n → Expr F X n 1 →
      Stmt F X ⟨c.function, false⟩ n → Stmt F X ⟨c.function, true⟩ n → Stmt F X c n
  | leave {F X l n} : Stmt F X ⟨true, l⟩ n
  | break_ {F X f n} : Stmt F X ⟨f, true⟩ n
  | continue_ {F X f n} : Stmt F X ⟨f, true⟩ n
  | functions {F X c n} (ss : List Sig) : Bodies (ss ++ F) (globals X) ss → Stmt (ss ++ F) X c n → Stmt F X c n

/-- Switch arms share the surrounding context. Duplicate labels are a static
checker obligation, not an arbitrary priority rule. -/
inductive Cases : List Sig → List ExternalType → Control → Nat → Type where
  | nil {F X c n} : Cases F X c n
  | cons {F X c n} : Word → Stmt F X c n → Cases F X c n → Cases F X c n

/-- Every body sees the whole function group and global externals, but no enclosing locals. -/
inductive Bodies : List Sig → List ExternalType → List Sig → Type where
  | nil {F G} : Bodies F G []
  | cons {F G s ss} : Stmt F G ⟨true, false⟩ (s.args + s.rets) → Bodies F G ss → Bodies F G (s :: ss)
end

end Solidity.Yul
