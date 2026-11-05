import Solidity.Yul.Builtins

/-!
# solc 0.8.38 object-dialect operation interface

EVM operations reuse the owner's arity-indexed builtin type. Object-dialect
string literals are metadata, never word-valued arguments. This interface
is syntax only: it does not assert execution, optimizer, layout or gas adequacy.
-/
namespace Solidity.SolcValidation

/-- Compiler-only operations absent from inline-assembly builtin syntax.
Indices count dynamic word arguments and results; literal labels are fields. -/
inductive ObjectOp : Nat → Nat → Type where
  | datasize (label : String) : ObjectOp 0 1
  | dataoffset (label : String) : ObjectOp 0 1
  | datacopy : ObjectOp 3 0
  | setimmutable (label : String) : ObjectOp 2 0
  | loadimmutable (label : String) : ObjectOp 0 1
  | linkersymbol (symbol : String) : ObjectOp 0 1
  | memoryguard (size : Fin (2 ^ 256)) : ObjectOp 0 1
  deriving Repr

/-- Preserve the core EVM vocabulary rather than copying its builtin census. -/
inductive Op : Nat → Nat → Type where
  | evm {a r : Nat} : Solidity.Yul.Builtin a r → Op a r
  | object {a r : Nat} : ObjectOp a r → Op a r

def ObjectOp.name {a r : Nat} (op : ObjectOp a r) : String :=
  ObjectOp.casesOn (motive := fun _ _ _ => String) op
    (datasize := fun _ => "datasize")
    (dataoffset := fun _ => "dataoffset")
    (datacopy := "datacopy")
    (setimmutable := fun _ => "setimmutable")
    (loadimmutable := fun _ => "loadimmutable")
    (linkersymbol := fun _ => "linkersymbol")
    (memoryguard := fun _ => "memoryguard")

def Op.name {a r : Nat} (op : Op a r) : String :=
  Op.casesOn (motive := fun _ => String) op
    (evm := Solidity.Yul.Builtin.name) (object := ObjectOp.name)

/-- Retain the import mode. The eventual matcher must additionally require
unoptimized input and establish exact compiler-output provenance. -/
inductive IrMode where
  | unoptimized | optimized
  deriving DecidableEq, Repr

def compilerVersion : String := "0.8.38+commit.1835d247.Emscripten.clang"
def compilerSha256 : String :=
  "6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390"

/-- An object tree carries the consumer's already intrinsic code type.
No untyped statement representation or assumed object-layout proof is added. -/
inductive Object (Code : Type) where
  | object (name : String) (code : Code) (children : List (Object Code))
  | data (name : String) (bytes : List (Fin 256))

/-- A retained artifact records which compiler output channel supplied it.
Compiler authentication and exact-byte parser derivations are separate gates. -/
structure IrArtifact (Code : Type) where
  mode : IrMode
  source : List (Fin 256)
  name : String
  code : Code
  children : List (Object Code)

/-- The artifact root is always code-bearing, never a data member. -/
def IrArtifact.root {Code : Type} (artifact : IrArtifact Code) : Object Code :=
  .object artifact.name artifact.code artifact.children

/-- Embedding an EVM builtin preserves its exact spelling. -/
theorem evm_name {a r : Nat} (op : Solidity.Yul.Builtin a r) :
    (Op.evm op).name = op.name := rfl

/-- The two mode constructors are distinct; this is not a provenance theorem. -/
theorem mode_distinct : IrMode.optimized ≠ IrMode.unoptimized := by
  intro h
  cases h

end Solidity.SolcValidation
