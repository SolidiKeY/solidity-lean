import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

/-!
# Internal function types

A function type is not a type of the syntax (`docs/semantic-gaps.md`,
"Function types"): a value of one is a `uint`, the tag of a function of the
contract (its position in `Contract.funs`, from `1`; `0` is unassigned), and
a call through it is a dispatch over the contract's functions of its
signature declared before the caller (`fnDispatch`, `Syntax/Elab.lean`), the
last branch `revert();`: an unassigned value panics (solc's `Panic(0x51)`),
which the model reads as a revert, as it reads an index out of range.  The marker row beside the `uint` records the type
(`op#function(uint)returns(uint)`, as `bytesN`'s `#bytes`).

* §1 — values in locals, parameters, returns and state variables;
* §2 — the default value, `delete`, `==`.
-/

namespace Solidity.Examples.Tactics.FunctionTypes

open scoped Scoped

/-- A contract whose functions take, return and store function values. -/
def Ops : Contract := contract!{
  function (uint) pure returns (uint) op;
  function double(uint x) pure returns (uint r) { r = 2 * x; }
  function triple(uint x) pure returns (uint r) { r = 3 * x; }
  function apply(function (uint) pure returns (uint) h, uint x) pure returns (uint r) { r = h(x); }
  function compose(function (uint) pure returns (uint) f, function (uint) pure returns (uint) g,
      uint x) pure returns (uint r) {
    r = g(f(x));
  }
  function choose(bool b) pure returns (function (uint) pure returns (uint) r) {
    if (b) { r = double; } else { r = triple; }
  }
  function setOp(bool b) { op = b ? double : triple; }
  function runOp(uint x) returns (uint r) { r = op(x); }
  struct Holder { uint k; function (uint) pure returns (uint) f; }
  Holder hold;
  function (uint) pure returns (uint)[] fs;
}

example : Ops.widths =
    [("op#function(uint)returns(uint)", 0), ("fs[]#function(uint)returns(uint)", 0)] := rfl

/-- A parameter's and a return's marker, keyed by its name as a width is. -/
example : (Ops.funs.map fun (n, d) => (n, d.widths)) =
    [("double", []), ("triple", []), ("apply", [("h#function(uint)returns(uint)", 0)]),
     ("compose", [("f#function(uint)returns(uint)", 0), ("g#function(uint)returns(uint)", 0)]),
     ("choose", [("r#function(uint)returns(uint)", 0)]), ("setOp", []), ("runOp", [])] := rfl

local instance : InContract := ⟨Ops⟩

/-! ## 1 · Function values -/

/-- A function value in a local: `h(2)` dispatches to `triple`. -/
theorem local_ : ⊨ᶠ dl!{ ⟨ function (uint) pure returns (uint) h = triple; uint y = h(2); ⟩
    y == 6 } := by
  sol_symex
  sol_close

/-- A function value as an argument. -/
theorem apply_ : ⊨ᶠ dl!{ ⟨ uint y = apply(double, 3); ⟩ y == 6 } := by
  sol_symex
  sol_close

/-- Two, composed: `triple(double(1))`. -/
theorem compose_ : ⊨ᶠ dl!{ ⟨ uint y = compose(double, triple, 1); ⟩ y == 6 } := by
  sol_symex
  sol_close

/-- A function value returned. -/
theorem choose_ : ⊨ᶠ dl!{ ⟨ function (uint) pure returns (uint) h = choose(false); uint y = h(4); ⟩
    y == 12 } := by
  sol_symex
  sol_close

/-- A function value stored, chosen by a flag, then called from storage. -/
theorem stored : ⊨ᶠ dl!{ ⟨ setOp(true); uint y = runOp(5); ⟩ y == 10 } := by
  sol_symex
  sol_close

/-- A struct member of a function type is its tag, a `uint` with its
marker (the struct spells its type, `Semantics.StructEnc`): called through
a local of the type. -/
theorem member : ⊨ᶠ dl!{ ⟨ hold.f = triple; function (uint) pure returns (uint) g = hold.f;
    uint y = g(3); ⟩ y == 9 } := by
  sol_symex
  sol_close

/-- A call through a value that is not a name (`callValueName`): the
callee is captured into a fresh local of its type first, then called as a
name is.  A struct member, `hold.f(3)`: -/
theorem memberCall : ⊨ᶠ dl!{ ⟨ hold.f = triple; uint y = hold.f(3); ⟩ y == 9 } := by
  sol_symex
  sol_close

/-- An array element, `fs[0](4)`. -/
theorem elementCall : ⊨ᶠ dl!{ ⟨ fs.push(triple); fs[0] = double; uint y = fs[0](4); ⟩
    y == 8 } := by
  sol_symex
  sol_decide

/-- A call's value, `choose(true)(4)`, and a call statement through a member. -/
theorem callCall : ⊨ᶠ dl!{ ⟨ uint y = choose(true)(4); hold.f = double; hold.f(1); ⟩ y == 8 } := by
  sol_symex
  sol_decide

/-- At a symbolic argument: only the branch of the value's tag is reached. -/
theorem symbolic : ⊨ᶠ dl!{ x < 100 → ⟨ function (uint) pure returns (uint) h = triple;
    assert(h(x) == 3 * x); ⟩ true } := by
  sol_symex
  sol_close

/-! ## 2 · The default value, `delete`, `==` -/

/-- An unassigned value panics when called: the run reverts. -/
theorem unassigned : ⊨ᶠ dl!{ [ function (uint) pure returns (uint) h; uint y = h(1); ] false } := by
  sol_symex
  sol_close

/-- `delete` unassigns: the stored value is `0` again, and a call panics. -/
theorem deleted : ⊨ᶠ dl!{ [ op = double; delete op; uint y = op(1); ] false } := by
  sol_symex
  sol_close

/-- `==` compares the functions: a function equals itself, not another. -/
theorem equality : ⊨ᶠ dl!{ ⟨ function (uint) pure returns (uint) h = double; bool a = h == double;
    bool b = h == triple; ⟩ a == true && b == false } := by
  sol_symex
  sol_close

/-! ## 3 · External function values

A value of an external function type is an address and a selector, packed
as the ABI's `bytes24` packs them: `address * 2^32 + selector` (`fnPure`).
`this.g` is the contract's address and `g`'s selector, the first four bytes
of the Keccak-256 of its signature, folded as solc folds it
(`fnSelector?`); a call through such a value is an external call to its
address, dispatched on its selector, so that a call to `this` of a function
declared before the caller runs it (O8, `extDispatch`). -/

/-- A contract that takes its own functions as external values. -/
def Ext : Contract := contract!{
  function double(uint x) returns (uint r) { r = 2 * x; }
  function viaThis(uint x) returns (uint r) {
    function (uint) external returns (uint) h = this.double;
    r = h(x);
  }
}

-- solc's selector of `double(uint256)`
#guard fnSelector? Ext "double" == some 0xeee97206

/-- A signature's types, read off the markers: an own struct is the tuple
of its members, an enum `uint8`, a function type `function`. -/
def Sig : Contract := contract!{
  struct P { address a; uint8 b; }
  enum E { A }
  function g(P memory p, E e, bytes4 s, string memory t, bytes memory u, int16 i,
      uint8[] memory xs, function (uint) external returns (uint) h) { }
}

-- solc's signature and selector (`evm.methodIdentifiers`)
#guard fnSignature? Sig "g" ==
  some "g((address,uint8),uint8,bytes4,string,bytes,int16,uint8[],function)"
#guard fnSelector? Sig "g" == some 0xa1570dcc

/-- The last local's value after a run of `P` from `Ext`'s initial state at
the address `7` (a call to address `0` reverts: no code there). -/
def runLast {Γ : Ctx} (P : Prog Ext [] (.val .uint :: Γ)) : Option Int :=
  let σ := State.ofStorage (Storage.init Ext)
  match Prog.run { σ with tx := { σ.tx with selfAddress := ⟨7, by decide⟩ } } P with
  | .ok o => some (TEnv.get .here o.st.env : PrimTy.uint.Denote).1
  | .error _ => none

-- `h.selector` of `this.double` is its selector, `h.address` the contract's
#guard runLast (sol[Ext]{ function (uint) external returns (uint) h = this.double;
    uint s = h.selector; }) == some 0xeee97206
#guard runLast (sol[Ext]{ function (uint) external returns (uint) h = this.double;
    uint a = h.address; }) == some 7

-- a call through `this.double` runs `double`: a self-call (O8)
#guard runLast (sol[Ext]{ uint y = viaThis(3); }) == some 6

/-- The native API deliberately admits addresses wider than the EVM's 160
bits. Native function-value calls keep that address and still dispatch to self. -/
private def runLastAt {D : Contract} {Γ : Ctx} (a : PrimTy.uint.Denote)
    (P : Prog D [] (.val .uint :: Γ)) : Option Int :=
  let σ := State.ofStorage (Storage.init D)
  match Prog.run { σ with tx := { σ.tx with selfAddress := a } } P with
  | .ok o => some (TEnv.get .here o.st.env : PrimTy.uint.Denote).1
  | .error _ => none

#guard runLastAt ⟨2^200, by decide +kernel⟩
    (sol[Ext]{ uint y = viaThis(3); }) == some 6

/-- Source metadata selects address cleanup without changing the callable
bodies. This isolated lowering control supplements the actual compiler-import
`externalValue` regression in the source FunctionTypes suite. -/
private def SourceExt : Contract :=
  { Ext with funs := Ext.funs.map fun (name, d) =>
      (name, { d with sourceDecl := some {
        name := name
        signature := fnSignature? Ext name
        callable := .abi .publicFn .selected none } }) }

-- At a genuine EVM address, cleanup preserves the selector and self-call.
#guard runLastAt ⟨7, by decide⟩
    (sol[SourceExt]{ uint y = viaThis(3); }) == some 6

-- This intentionally out-of-EVM state exposes the conversion: the source
-- receiver becomes zero and reverts, while the native control above returns.
#guard runLastAt ⟨2^200, by decide +kernel⟩
    (sol[SourceExt]{ uint y = viaThis(3); }) == none

/-- `this.double` and the value it names, as the elaborator writes them. -/
example : Prog.toStr [] (sol[Ext]{ function (uint) external returns (uint) h = this.double;
    uint s = h.selector; }) =
    "uint h = (address(this) * 4294967296) + 4008276486; \
     uint s = h - ((h / 4294967296) * 4294967296);" := rfl

/-- `h.address` of `this.double` is the contract's address: the closer reads
`(address(this) * 2^32 + s) / 2^32` back (`Facts.cancelDiv`, Lean only). -/
theorem addressOfValue : ⊨ᶠ dl[Ext]{ [ function (uint) external returns (uint) h = this.double;
    uint a = h.address; uint t = address(this); ] a == t } := by
  sol_symex
  sol_decide

/-- `h.selector` of `this.double` is its selector in every typed initial
state where packing returns. The box also retains packing failure: after
`cancelDiv` the selector read is `(address(this) * 2^32 + s) - address(this) * 2^32`. -/
theorem selectorOfValue : ⊨ᶠ dl[Ext]{ [ function (uint) external returns (uint) h = this.double;
    uint s = h.selector; ] s == 4008276486 } := by
  sol_symex
  sol_decide

/-- Successful packing and selector projection at address `7` give a normal
result, independently of the universally quantified box proof. -/
theorem selectorOfValue_returns :
    runLast (sol[Ext]{ function (uint) external returns (uint) h = this.double;
      uint s = h.selector; }) = some 4008276486 := by
  decide +kernel

section Cancellation

private def noFacts : Decide.Facts Ext := {}
private def uOne : Decide.LTm Ext (.val .uint) := .lit ⟨1, rfl⟩
private def uTwo : Decide.LTm Ext (.val .uint) := .lit ⟨2, rfl⟩
private def uMax : Decide.LTm Ext (.val .uint) := .lit ⟨2 ^ 256 - 1, by decide +kernel⟩
private def iMin : Decide.LTm Ext (.val .int) := .lit ⟨-(2 ^ 255), by decide +kernel⟩
private def iNegOne : Decide.LTm Ext (.val .int) := .lit ⟨-1, by decide⟩
private def iOne : Decide.LTm Ext (.val .int) := .lit ⟨1, by decide⟩
private def uSum (a b : Decide.LTm Ext (.val .uint)) : Decide.LTm Ext (.val .uint) :=
  .app2 (.binop .add rfl) a b
private def iSum (a b : Decide.LTm Ext (.val .int)) : Decide.LTm Ext (.val .int) :=
  .app2 (.binop .add rfl) a b

/-- `(1 + 2) - 1` takes the new left-summand branch. -/
example : noFacts.cancel (uSum uOne uTwo) uOne = some uTwo := by rfl

/-- `(1 + 2) - 2` retains the original right-summand branch. -/
example : noFacts.cancel (uSum uOne uTwo) uTwo = some uOne := by rfl

/-- Both orders also return the surviving signed operand. -/
example : noFacts.cancel (iSum iNegOne iOne) iNegOne = some iOne ∧
    noFacts.cancel (iSum iNegOne iOne) iOne = some iNegOne := by
  exact ⟨rfl, rfl⟩

/-- Both operands return, but their unsigned sum overflows: neither
cancellation is permitted to erase that failure. -/
example : noFacts.returns uMax = true ∧ noFacts.returns uOne = true ∧
    noFacts.returns (uSum uMax uOne) = false ∧
    noFacts.cancel (uSum uMax uOne) uMax = none ∧
    noFacts.cancel (uSum uMax uOne) uOne = none := by
  exact ⟨by decide +kernel, rfl, by decide +kernel,
    Option.isNone_iff_eq_none.mp (by decide +kernel),
    Option.isNone_iff_eq_none.mp (by decide +kernel)⟩

/-- Signed underflow is retained too, in either cancellation direction. -/
example : noFacts.returns iMin = true ∧ noFacts.returns iNegOne = true ∧
    noFacts.returns (iSum iMin iNegOne) = false ∧
    noFacts.cancel (iSum iMin iNegOne) iMin = none ∧
    noFacts.cancel (iSum iMin iNegOne) iNegOne = none := by
  exact ⟨by decide +kernel, rfl, by decide +kernel,
    Option.isNone_iff_eq_none.mp (by decide +kernel),
    Option.isNone_iff_eq_none.mp (by decide +kernel)⟩

/-- A failed operand cannot disappear even when it is the cancelled summand. -/
example : noFacts.cancel (uSum .err uOne) .err = none ∧
    noFacts.cancel (uSum uOne .err) uOne = none := by
  exact ⟨rfl, rfl⟩

/-- `(maxUint + 1) - maxUint` cannot establish a diamond: cancellation
must preserve the overflow before subtraction. -/
theorem cancelOverflowDiamond : ¬ (⊨ᶠ dl[Ext]{
    ⟨ uint a = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
      uint z = (a + 1) - a; ⟩ z == 1 }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)

/-- A signed overflowing sum cannot establish a diamond either. -/
theorem cancelSignedOverflowDiamond : ¬ (⊨ᶠ dl[Ext]{
    ⟨ int a = -57896044618658097711785492504343953926634992332820282019728792003956564819968;
      int z = (a + (-1)) - a; ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)

end Cancellation

/-! ## 4 · Recursion through a value

A call through a value is a call of each function it may reach
(`FunDecl.valueCallees`), so a function that calls itself through a value
is recursive (`isRecursiveC`) and its calls are `Stmt.callRec`'s
(`Examples/Tactics/Recursion.lean`). -/

def RecValues : Contract := contract!{
  function apply(function (uint) returns (uint) h, uint x) returns (uint r) { r = h(x); }
  function fact(uint n) returns (uint r) {
    if (n == 0) { r = 1; } else { r = n * apply(fact, n - 1); }
  }
}

#guard isRecursiveC RecValues "fact" && isRecursiveC RecValues "apply"

-- `fact(3)` through `apply` is `6` (run, as `#run` runs it)
#guard (match Prog.run (State.ofStorage (Storage.init RecValues))
      (sol[RecValues]{ uint z = fact(3); }) with
    | .ok o => some (TEnv.get .here o.st.env : PrimTy.uint.Denote).1
    | .error _ => none) == some 6

/-! ## 5 · What is refused -/

/-- error: Solidity elaboration failed: h(…): a function type with a uint[] parameter or return is not modelled (docs/semantic-gaps.md, "Function types") -/
#guard_msgs in #check sol{ function (uint[]) pure h; h(1); }

/-- A function declared after a caller that calls through a value of its
type, and named as a value in the contract, is refused: the caller's
dispatch could not inline it. -/
def Late : Contract := contract!{
  function apply(function (uint) pure returns (uint) h, uint x) pure returns (uint r) { r = h(x); }
  function double(uint x) pure returns (uint r) { r = 2 * x; }
  function use(uint x) pure returns (uint r) { r = apply(double, x); }
}

/-- error: Solidity elaboration failed: se3(…) may call double, which is not declared before this function: declare the functions of type function(uint)returns(uint) first -/
#guard_msgs in #check sol[Late]{ uint y = use(1); }

/-- One named as a value only outside the contract is refused there. -/
def Late2 : Contract := contract!{
  function apply(function (uint) pure returns (uint) h, uint x) pure returns (uint r) { r = h(x); }
  function double(uint x) pure returns (uint r) { r = 2 * x; }
}

/-- error: Solidity elaboration failed: double is taken as a value only outside the contract's functions, and a function declared before it calls through a function value: name it as a value in the contract -/
#guard_msgs in #check sol[Late2]{ uint y = apply(double, 1); }

/-! ## 6 · Memory- and storage-array arguments

A function type with a memory- or storage-array parameter of a plain value
element, `function (uint[] memory) returns (uint)`, spells its parameter with
its location (`uint[]memory`, `uint[]storage`, `FunDecl.sigTy?`); only
functions whose parameter is an array of that element at that location are
candidates. A storage operand of a storage parameter is captured as an alias. The dispatch captures each
argument once, left to right (`fnDispatch`): a memory operand as the
reference itself, so the callee's writes reach the caller, and a storage
operand as a copy taken at its position, before a later argument runs. The
tag is read after the arguments, as solc's legacy pipeline reads the callee. -/

def MemArgs : Contract := contract!{
  uint calls;
  uint[] values;
  function (uint[] memory) returns (uint) op;
  function sum2(uint[] memory xs) returns (uint r) { r = xs[0] + xs[1]; }
  function bump(uint[] memory xs) returns (uint r) {
    calls = calls + 1; xs[0] = xs[0] + 10; r = xs[0];
  }
  function scalar(uint x) returns (uint r) { r = x; }
  function stored(uint[] storage xs) returns (uint r) { xs[0] = xs[0] + 5; r = xs[0]; }
  function bytesArg(bytes memory xs) returns (uint r) { r = xs.length; }
  function narrow(uint8[] memory xs) returns (uint r) { r = xs[0]; }
  function pair(uint[] memory xs, uint k) returns (uint r) { r = xs[0] * 100 + k; }
  function setFirst() returns (uint) { values[0] = 9; return 1; }
  function setOp(bool b) { op = b ? bump : sum2; }
  Token tok;
  function tokPlus(Token memory t) returns (uint r) { t.value = t.value + 1; r = t.value; }
  function tokStored(Token storage t) returns (uint r) { t.value = t.value + 7; r = t.value; }
  function tokOther(Account memory a) returns (uint r) { r = a.balance; }
  function viaParam(function (uint[] memory) returns (uint) h, uint[] memory xs)
      returns (uint r) { r = h(xs); }
}

local instance : InContract := ⟨MemArgs⟩

-- The signatures: the location is kept, so storage, `bytes` and scalar
-- parameters are not memory-array candidates; a narrow element is not spelled
-- (its width rows are not carried by a capture), so it is no candidate.
#guard (MemArgs.funs.map fun (n, d) => (n, FunDecl.sigTy? MemArgs d)) ==
    [("sum2", some "function(uint[]memory)returns(uint)"),
     ("bump", some "function(uint[]memory)returns(uint)"),
     ("scalar", some "function(uint)returns(uint)"),
     ("stored", some "function(uint[]storage)returns(uint)"), ("bytesArg", none),
     ("narrow", none),
     ("pair", some "function(uint[]memory,uint)returns(uint)"),
     ("setFirst", some "function()returns(uint)"),
     ("setOp", some "function(bool)"),
     ("tokPlus", some "function(Tokenmemory)returns(uint)"),
     ("tokStored", some "function(Tokenstorage)returns(uint)"),
     ("tokOther", some "function(Accountmemory)returns(uint)"),
     ("viaParam", some "function(function(uint[]memory)returns(uint),uint[]memory)returns(uint)")]

/-- The dispatch of `h(xs)` as the elaborator writes it: the argument is
captured as a memory local, then each candidate of the exact signature is a
branch, `bump` and `sum2` (not `scalar` nor `narrow`); an unassigned tag reverts. -/
example : Prog.toStr [] (sol[MemArgs]{ uint[] memory xs = new uint[](2);
    function (uint[] memory) returns (uint) h = bump; uint r = h(xs); }) =
    "uint[] memory xs = new uint[](2); uint h = 2; uint r; uint[] memory se1 = xs; \
     if (h == 1) { r = sum2(se1); } else { if (h == 2) { r = bump(se1); } else { revert(); } }" := rfl

/-- Aliasing: `bump` writes through the caller's array. -/
private def memAlias := sol[MemArgs]{
  uint[] memory xs = new uint[](2); xs[0] = 1; xs[1] = 2;
  function (uint[] memory) returns (uint) h = bump;
  uint r = h(xs);
  assert(r == 11); assert(xs[0] == 11); assert(calls == 1);
}

/-- `h(xs)` with `h = bump`: the run returns, its asserts `r == 11`, `xs[0] == 11` hold. -/
theorem memAlias_run : (Prog.run (State.init MemArgs) memAlias).toOption.isSome = true := by
  decide +kernel

/-- The direct call observes the same. That the dispatch's arm for `bump`'s
tag is this call holds by construction of the elaborator, not by a theorem:
`DispatchArm.chain_tag` assumes the guard semantics (`finite-dispatch.md`). -/
private def memDirect := sol[MemArgs]{
  uint[] memory xs = new uint[](2); xs[0] = 1; xs[1] = 2;
  uint r = bump(xs);
  assert(r == 11); assert(xs[0] == 11); assert(calls == 1);
}

/-- `bump(xs)` called directly on the same input: the same asserts hold. -/
theorem memDirect_run : (Prog.run (State.init MemArgs) memDirect).toOption.isSome = true := by
  decide +kernel

/-- A storage operand is copied: `bump` leaves `values` unchanged. -/
private def memCopy := sol[MemArgs]{
  values.push(1); values.push(2);
  function (uint[] memory) returns (uint) h = bump;
  uint r = h(values);
  assert(r == 11); assert(values[0] == 1);
}

/-- `h(values)` with `h = bump`: the storage operand is copied, `values[0] == 1`. -/
theorem memCopy_run : (Prog.run (State.init MemArgs) memCopy).toOption.isSome = true := by
  decide +kernel

/-- Argument order: `values` is copied before `setFirst()` writes it. -/
private def memOrder := sol[MemArgs]{
  values.push(1);
  function (uint[] memory, uint) returns (uint) h = pair;
  uint r = h(values, setFirst());
  assert(r == 101); assert(values[0] == 9);
}

/-- `h(values, setFirst())`: `values` is copied before `setFirst()` writes it, `r == 101`. -/
theorem memOrder_run : (Prog.run (State.init MemArgs) memOrder).toOption.isSome = true := by
  decide +kernel

/-- Both branches of a stored value, and a value passed as a parameter. -/
private def memBranches := sol[MemArgs]{
  uint[] memory xs = new uint[](2); xs[0] = 3; xs[1] = 4;
  setOp(false); uint a = op(xs);
  setOp(true); uint b = op(xs);
  uint c = viaParam(sum2, xs);
  assert(a == 7); assert(b == 13); assert(xs[0] == 13); assert(c == 17);
}

/-- `op(xs)` after `setOp(false)` and `setOp(true)`, and `viaParam(sum2, xs)`. -/
theorem memBranches_run :
    (Prog.run (State.init MemArgs) memBranches).toOption.isSome = true := by
  decide +kernel

/-- A storage-array argument is an alias: `stored` writes `values`. -/
private def storAlias := sol[MemArgs]{
  values.push(1);
  function (uint[] storage) returns (uint) h = stored;
  uint r = h(values);
  assert(r == 6); assert(values[0] == 6);
}

/-- `h(values)` with `h = stored`: the storage alias is written, `values[0] == 6`. -/
theorem storAlias_run : (Prog.run (State.init MemArgs) storAlias).toOption.isSome = true := by
  decide +kernel

/-- A struct argument is nominal and keeps its location: `tokPlus` writes
the caller's memory struct, `tokStored` the storage one; `tokOther` (an
`Account`) is no candidate of `function (Token memory)`. -/
private def structArgs := sol[MemArgs]{
  Token memory t; t.value = 1;
  function (Token memory) returns (uint) h = tokPlus;
  uint r = h(t);
  assert(r == 2); assert(t.value == 2);
  tok.value = 1;
  function (Token storage) returns (uint) g = tokStored;
  uint s = g(tok);
  assert(s == 8); assert(tok.value == 8);
  Token memory c = tok; uint u = h(c);
  assert(u == 9); assert(tok.value == 8);
}

/-- `h(t)`, `g(tok)`, `h(c)`: struct arguments by reference at their location. -/
theorem structArgs_run :
    (Prog.run (State.init MemArgs) structArgs).toOption.isSome = true := by
  decide +kernel

/-- Model-only behaviour on a program solc rejects (`h = tokOther` is a
type error there): an `Account` function's tag has no arm in a
`function (Token memory)` dispatch, so the call reverts. -/
theorem structWrongNominal : ¬ (⊨ᶠ dl!{ ⟨ Token memory t;
    function (Token memory) returns (uint) h = tokOther; uint r = h(t); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)

/-- A never-assigned storage function value reverts. solc's IR pipeline
raises `Panic(0x51)`; its legacy pipeline jumps to an invalid destination
(finite-dispatch.md, "Recorded deviations"): both are failures. -/
theorem memUnassigned : ¬ (⊨ᶠ dl!{ ⟨ uint[] memory xs = new uint[](1); uint r = op(xs); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)

/-- The false observation that the callee's write is not visible fails. -/
theorem memNoCopy : ¬ (⊨ᶠ dl!{ ⟨ uint[] memory xs = new uint[](1);
    function (uint[] memory) returns (uint) h = bump; uint r = h(xs); assert(xs[0] == 0); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)

/-- Model-only behaviour on a program solc rejects (`h = scalar` is a type
error there): the elaborator does not type-check a function value's
assignment, and the dispatch has no arm for a scalar function's tag, so the
call reverts. -/
theorem memWrongCandidate : ¬ (⊨ᶠ dl!{ ⟨ uint[] memory xs = new uint[](1);
    function (uint[] memory) returns (uint) h = scalar; uint r = h(xs); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)

/-- One candidate, `add10`, so the symbolic run stays small. -/
def MemAlias : Contract := contract!{
  function add10(uint[] memory xs) returns (uint r) { xs[0] = xs[0] + 10; r = xs[0]; }
}

/-- In every typed state, `h(xs)` with `h = add10` writes the caller's
array: `uint[] memory xs = new uint[](1); xs[0] = 1; uint r = h(xs);` leaves
`xs[0] == 11` and `r == 11`. -/
theorem memAlias_valid : ⊨ᶠ dl[MemAlias]{ ⟨ uint[] memory xs = new uint[](1); xs[0] = 1;
    function (uint[] memory) returns (uint) h = add10; uint r = h(xs); ⟩ xs[0] == 11 && r == 11 } := by
  sol_symex
  sol_decide

end Solidity.Examples.Tactics.FunctionTypes
