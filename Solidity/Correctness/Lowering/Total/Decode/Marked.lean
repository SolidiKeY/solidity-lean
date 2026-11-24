import Solidity.Correctness.Lowering.Total.Decode.Widths

namespace Solidity.Correctness.Lowering.Total.Decode

open Source (Syn SCtx STy)

/-! ### Addresses

`tablesA`: as `tablesW`, and an erased `address` where the model marks one. A
local marked `#address` (20 bytes, at 256 bits) and a state variable with the
row `x#address` are Source `address`; so is a declaration named `address`.
`address payable` is read as `address`: the model does not record the
difference. Environment reads are the landed ones (`Decode.env`), so `msg.sender`,
`address(this)` and address casts stay gaps. A captured address, whose shape
carries the marker twice, is a gap; and the caveat at `localTyW` still
applies: a local declared without a marker is read as a plain integer. -/

/-- The marker rows of an erased `address`. -/
def addressShape : List (String × Nat) := [("#address", 20)]

/-- Declaration types by name: `address`, or as `typeNameW`. -/
def typeNameA : RawTy → Option (Syn .typeName)
  | .named s => if s = "address" then some (.elem .address) else typeNameW (.named s)
  | T => typeNameW T

/-- A model local: an `address` where the shape is exactly the address marker
on a full-width `uint`, or as `localTyW`. -/
def localTyA : LocalTy → Option STy
  | .val .uint 256 [("#address", 20)] => some (.address false)
  | t => localTyW t

/-- Whether the width table marks the state variable `x` as an address. -/
def isAddress (widths : List (Name × Nat)) (x : Name) : Bool :=
  Semantics.lookupBy (x ++ "#address") widths == some 20

/-- The elementary type of a state variable: an address where the table
marks one (it must then be a `uint` with no width row of its own), or the
primitive at its width. -/
def elemA (widths : List (Name × Nat)) (x : Name) (p : PrimTy) : Option Source.Elem :=
  if isAddress widths x then
    (if p = .uint ∧ Semantics.lookupBy x widths = none then some .address else none)
  else primElem p (stateBits widths x)

/-- The state variables, an address where the table marks one. -/
def stateVarsA (widths : List (Name × Nat)) :
    List (Name × Ty) → Option (Syn (.list (.part false)))
  | [] => some .nil
  | (x, .prim p) :: rest => do
      pure (.cons (.stateVar (.elem (← elemA widths x p)) none none none false x .none)
        (← stateVarsA widths rest))
  | _ => none

/-- A width key the address version reads: a plain key, or the address marker
of a state variable. -/
def keyA (vars : List (Name × Ty)) (w : Name × Nat) : Bool :=
  plainKey w.1 || vars.any fun v => w.1 == v.1 ++ "#address" && w.2 == 20

/-- The canonical unit with addresses: as `unitW`, but address marker rows of
state variables are read instead of being gaps. -/
def unitA (C : Contract) : Option (Syn .unit) :=
  if C.transientRoots.isEmpty && C.funs.isEmpty && C.enums.isEmpty && C.ctor.isNone &&
      C.inits.isEmpty && (C.widths.all fun w => keyA C.vars w) &&
      (C.vars.all fun v => plainKey v.1) then
    (stateVarsA C.widths C.vars).map fun parts =>
      .unit (.cons (.contract false contractName .none .nil parts) .nil)
  else none

/-- The address-aware decoder's tables. -/
def tablesA : Tables := ⟨typeNameA, localTyA, unitA, env⟩

/-! ### Canonical units from an element table

Later versions build their unit from one function: which elementary type a
state variable has. `unitOf` constructs the canonical unit over that table. -/

/-- The state variables, each at the elementary type `el` gives it. -/
def stateVarsOf (el : Name → PrimTy → Option Source.Elem) :
    List (Name × Ty) → Option (Syn (.list (.part false)))
  | [] => some .nil
  | (x, .prim p) :: rest => do
      pure (.cons (.stateVar (.elem (← el x p)) none none none false x .none)
        (← stateVarsOf el rest))
  | _ => none

/-- The canonical unit of a contract that passes `ok`, over an element table.
Transient roots, functions, enums, the constructor and initializers are gaps,
and so are a state variable of a reference type, one the table gives no
elementary type, and one named like a marker row. -/
def unitOf (ok : Contract → Bool) (el : Contract → Name → PrimTy → Option Source.Elem)
    (C : Contract) : Option (Syn .unit) :=
  if C.transientRoots.isEmpty && C.funs.isEmpty && C.enums.isEmpty && C.ctor.isNone &&
      C.inits.isEmpty && ok C && (C.vars.all fun v => plainKey v.1) then
    (stateVarsOf (el C) C.vars).map fun parts =>
      .unit (.cons (.contract false contractName .none .nil parts) .nil)
  else none

/-! ### Fixed bytes

`tablesB`: as `tablesA`, and an erased `bytesN` where the model marks one. A
local of `8N` bits marked `#bytes ↦ N`, a state variable with the row
`x#bytes ↦ N` (and its own row `x ↦ 8N` when `N < 32`), and a declaration
named `bytesN` are Source `bytesN`. The model holds a `bytesN` as the number
its bytes spell big-endian, right-aligned in a `uint` of `8N` bits
(`Syntax/Raw.lean`, at `bytesTy?`); that is the reading here, not the
left-aligned word of `Source.Observe`.

Environment reads are the landed ones (`Decode.env`). Between marked operands expressions spell, and
Source types, indexing `b[i]`, `b.length`, `==`, `!=`, the orderings, `&`,
`|`, `^`, `~`, the shifts, their compound assignments and implicit widening:
these are in the fragment, so their agreement with the model is part of the
simulation obligation. `bytesN(e)` casts and bytes literals are gaps. A
captured `bytesN`, whose shape carries the marker twice, is a gap, and the
caveat at `localTyW` still applies. -/

/-- `bytesN` for `N` in `1 … 32`. -/
def bytesElem (n : Nat) : Option Source.Elem :=
  if h : 1 ≤ n ∧ n ≤ 32 then some (.fixedBytes n h) else none

/-- Declaration types by name: `bytesN`, or as `typeNameA`. -/
def typeNameB : RawTy → Option (Syn .typeName)
  | .named s => match bytesTy? s with
    | some n => (bytesElem n).map .elem
    | none => typeNameA (.named s)
  | T => typeNameA T

/-- A model local: a `bytesN` where the shape is exactly the bytes marker on a
`uint` of `8N` bits, or as `localTyA`. -/
def localTyB : LocalTy → Option STy
  | .val .uint bits [("#bytes", n)] =>
    if bits = 8 * n then (bytesElem n).map (Source.Elem.ty .memory) else none
  | t => localTyA t

/-- The elementary type of a state variable: `bytesN` where the table marks
one (a `uint` whose width is `8N` and that is not also marked an address), or
as `elemA`. -/
def elemB (widths : List (Name × Nat)) (x : Name) (p : PrimTy) : Option Source.Elem :=
  match Semantics.lookupBy (x ++ "#bytes") widths with
  | some n =>
    if p = .uint ∧ stateBits widths x = 8 * n ∧ isAddress widths x = false then bytesElem n
    else none
  | none => elemA widths x p

/-- A width key the bytes version reads: as `keyA`, or the bytes marker of a
state variable. -/
def keyB (vars : List (Name × Ty)) (w : Name × Nat) : Bool :=
  keyA vars w || vars.any fun v => w.1 == v.1 ++ "#bytes"

/-- The canonical unit with fixed bytes. -/
def unitB : Contract → Option (Syn .unit) :=
  unitOf (fun C => C.widths.all fun w => keyB C.vars w) fun C => elemB C.widths

/-- The bytes-aware decoder's tables. -/
def tablesB : Tables := ⟨typeNameB, localTyB, unitB, env⟩

/-! ### The caller

`tablesS`: as `tablesB`, and `msg.sender` is read as the Source `msg.sender`,
an `address`. Relating this read to the model caller requires a state
relation. `address(this)` and its balance stay gaps. -/

/-- Environment reads with the caller. -/
def envS : EnvKey → Option (Syn .expr)
  | .msgSender => some (.member (.ident "msg") "sender")
  | k => env k

/-- The caller-aware decoder's tables. -/
def tablesS : Tables := { tablesB with env := envS }

end Solidity.Correctness.Lowering.Total.Decode
