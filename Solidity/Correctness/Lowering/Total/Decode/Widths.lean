import Solidity.Correctness.Lowering.Total.Decode.Tables

namespace Solidity.Correctness.Lowering.Total.Decode

open Source (Syn SCtx STy)

/-! ### Widths

`tablesW`: a primitive at its declared width. A local `uint8 x` is
`LocalTy.val .uint 8`, a state variable's width is its own row of the
contract's width table, a declaration names its type. -/

/-- The Source elementary type of a model primitive at a width: `bool`, or
`uintN`/`intN` for a width that is a multiple of 8 in `8 … 256`. -/
def primElem : PrimTy → Nat → Option Source.Elem
  | .bool, bits => if bits = 256 then some .bool else none
  | .uint, bits =>
    if h : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 then some (.int false bits h) else none
  | .int, bits =>
    if h : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 then some (.int true bits h) else none

/-- The Source type of a model primitive at a width. -/
def primTy (p : PrimTy) (bits : Nat) : Option STy := (primElem p bits).map (Source.Elem.ty .memory)

/-- Declaration types by name: `bool`, `uint`/`int` (256 bits) and the narrow
`uintN`/`intN`. `address`, `bytesN`, enums, references and user types are gaps. -/
def typeNameW : RawTy → Option (Syn .typeName)
  | .named s =>
    if s = "bool" then some (.elem .bool)
    else if s = "uint" ∨ s = "uint256" then (primElem .uint 256).map .elem
    else if s = "int" ∨ s = "int256" then (primElem .int 256).map .elem
    else match narrowTy? s with
      | some (p, bits) => (primElem p bits).map .elem
      | none => none
  | _ => none

/-- A model local at its declared width, with no shape rows. A local carrying
a shape (the marker of an erased `address`, `bytesN`, enum or function type),
a reference and a formula local are gaps. Not a gap, and possibly a wrong
Source type: a local the elaborator declares without a marker (a pushed value
`T x = b.push()`, a self-call or `try` return, a cast capture) has an empty
shape even when its declared type was `address` or `bytesN`, and is read here
as the integer `uintN` the model also takes it for. A request's locals are
also not tied to any elaborator run. -/
def localTyW : LocalTy → Option STy
  | .val p bits [] => primTy p bits
  | _ => none

/-- The width of a state variable: its row in the width table, or 256. -/
def stateBits (widths : List (Name × Nat)) (x : Name) : Nat :=
  (Semantics.lookupBy x widths).getD 256

/-- The state variables, in declaration order, each a primitive at its width. -/
def stateVarsW (widths : List (Name × Nat)) :
    List (Name × Ty) → Option (Syn (.list (.part false)))
  | [] => some .nil
  | (x, .prim p) :: rest => do
      pure (.cons (.stateVar (.elem (← primElem p (stateBits widths x))) none none none false x
        .none) (← stateVarsW widths rest))
  | _ => none

/-- A width key that is a state variable's own row: no marker (`#`) and no
position below a reference (`[`, `{`). -/
def plainKey (k : String) : Bool := k.data.all fun c => c != '#' && c != '[' && c != '{'

/-- The canonical unit at widths. Transient roots, functions, enums, the
constructor and initializers are gaps, and so are a state variable of a
reference type, a width that is no integer type's (or any width but 256 on a
`bool`), a width table with a marker row or a row below a reference, and a
state variable named like one. A row whose key is no state variable is not
read, as the model does not read it. -/
def unitW (C : Contract) : Option (Syn .unit) :=
  if C.transientRoots.isEmpty && C.funs.isEmpty && C.enums.isEmpty && C.ctor.isNone &&
      C.inits.isEmpty && (C.widths.all fun w => plainKey w.1) &&
      (C.vars.all fun v => plainKey v.1) then
    (stateVarsW C.widths C.vars).map fun parts =>
      .unit (.cons (.contract false contractName .none .nil parts) .nil)
  else none

/-- The width-aware decoder's tables. -/
def tablesW : Tables := ⟨typeNameW, localTyW, unitW, env⟩

end Solidity.Correctness.Lowering.Total.Decode
