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
theorem local_ : ⊨ dl!{ ⟨ function (uint) pure returns (uint) h = triple; uint y = h(2); ⟩
    y == 6 } := by
  sol_symex
  sol_close

/-- A function value as an argument. -/
theorem apply_ : ⊨ dl!{ ⟨ uint y = apply(double, 3); ⟩ y == 6 } := by
  sol_symex
  sol_close

/-- Two, composed: `triple(double(1))`. -/
theorem compose_ : ⊨ dl!{ ⟨ uint y = compose(double, triple, 1); ⟩ y == 6 } := by
  sol_symex
  sol_close

/-- A function value returned. -/
theorem choose_ : ⊨ dl!{ ⟨ function (uint) pure returns (uint) h = choose(false); uint y = h(4); ⟩
    y == 12 } := by
  sol_symex
  sol_close

/-- A function value stored, chosen by a flag, then called from storage. -/
theorem stored : ⊨ dl!{ ⟨ setOp(true); uint y = runOp(5); ⟩ y == 10 } := by
  sol_symex
  sol_close

/-- A struct member of a function type is its tag, a `uint` with its
marker (the struct spells its type, `Semantics.StructEnc`): called through
a local of the type. -/
theorem member : ⊨ dl!{ ⟨ hold.f = triple; function (uint) pure returns (uint) g = hold.f;
    uint y = g(3); ⟩ y == 9 } := by
  sol_symex
  sol_close

/-- A call through a value that is not a name (`callValueName`): the
callee is captured into a fresh local of its type first, then called as a
name is.  A struct member, `hold.f(3)`: -/
theorem memberCall : ⊨ dl!{ ⟨ hold.f = triple; uint y = hold.f(3); ⟩ y == 9 } := by
  sol_symex
  sol_close

/-- An array element, `fs[0](4)`. -/
theorem elementCall : ⊨ dl!{ ⟨ fs.push(triple); fs[0] = double; uint y = fs[0](4); ⟩
    y == 8 } := by
  sol_symex
  sol_decide

/-- A call's value, `choose(true)(4)`, and a call statement through a member. -/
theorem callCall : ⊨ dl!{ ⟨ uint y = choose(true)(4); hold.f = double; hold.f(1); ⟩ y == 8 } := by
  sol_symex
  sol_close

/-- At a symbolic argument: only the branch of the value's tag is reached. -/
theorem symbolic : ⊨ dl!{ x < 100 → ⟨ function (uint) pure returns (uint) h = triple;
    assert(h(x) == 3 * x); ⟩ true } := by
  sol_symex
  sol_close

/-! ## 2 · The default value, `delete`, `==` -/

/-- An unassigned value panics when called: the run reverts. -/
theorem unassigned : ⊨ dl!{ [ function (uint) pure returns (uint) h; uint y = h(1); ] false } := by
  sol_symex
  sol_close

/-- `delete` unassigns: the stored value is `0` again, and a call panics. -/
theorem deleted : ⊨ dl!{ [ op = double; delete op; uint y = op(1); ] false } := by
  sol_symex
  sol_close

/-- `==` compares the functions: a function equals itself, not another. -/
theorem equality : ⊨ dl!{ ⟨ function (uint) pure returns (uint) h = double; bool a = h == double;
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

/-- `this.double` and the value it names, as the elaborator writes them. -/
example : Prog.toStr [] (sol[Ext]{ function (uint) external returns (uint) h = this.double;
    uint s = h.selector; }) =
    "uint h = (address(this) * 4294967296) + 4008276486; \
     uint s = h - ((h / 4294967296) * 4294967296);" := rfl

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

end Solidity.Examples.Tactics.FunctionTypes
