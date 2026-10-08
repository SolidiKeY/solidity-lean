import Solidity.Tools.Run
import Solidity.Tools.Inspect
import Solidity.Tools.DiffTest
import Solidity.Examples.Benchmark.Coin

/-!
# The tools, pinned

The commands of `Tools/` at work, as `#guard_msgs` tests: `#run` calls a
function in the interpreter (`Tools/Run.lean`); `#wp`, `#step` and `#taclet`
look inside the calculus (`Tools/Inspect.lean`); `#difftest` runs the
interpreter against the compiled code from random storages
(`Tools/DiffTest.lean`).  If a command's output changes, these fail.
-/

namespace Solidity.Examples.Tools

/-! ## `#run`

A returning call prints the value it returns; every call prints the
storage it leaves, one root per line.  `addTwo(3)` calls `addOne` twice;
`credit(1, 5)` writes a mapping entry and a counter. -/

/--
info: ok
returns 5
total = 0
count = 0
balances = {_: 0}
-/
#guard_msgs in #run CallsExample.addTwo(3)

/--
info: ok
total = 5
count = 0
balances = {1: 5, _: 0}
-/
#guard_msgs in #run CallsExample.credit(1, 5)

/-! A function of several returns lands them in `_r0`, `_r1`, …. -/

def Ordered : Contract := contract!{
  uint n;
  function ordered(uint x, uint y) returns (uint lo, uint hi) {
    if (x < y) { return (x, y); }
    return (y, x);
  }
}

/--
info: ok
returns (2, 5)
n = 0
-/
#guard_msgs in #run Ordered.ordered(5, 2)

/-! `mint` requires the caller to be the minter, who is `0` in a fresh
contract: anyone else reverts. -/

/-- info: revert -/
#guard_msgs in #run Benchmark.Coin.Coin.mint(1, 5) with msg.sender := 7

/--
info: ok
minter = 0
balances = {1: 5, _: 0}
-/
#guard_msgs in #run Benchmark.Coin.Coin.mint(1, 5) with msg.sender := 0

/-! A state variable of a value type is set in the `with` list; any other
start state is given whole, with `from`. -/

/--
info: ok
total = 0
count = 42
balances = {_: 0}
-/
#guard_msgs in #run CallsExample.bump() with count := 41

/--
info: ok
total = 0
count = 42
balances = {_: 0}
-/
#guard_msgs in
#run CallsExample.bump() from
  { storage := [("total", .int 0), ("count", .int 41), ("balances", .map [] (.int 0))] }

/-! ## `#wp` and `#step` -/

section Inspect

local instance : InContract := ⟨StandardExample⟩

/-! The formulas read the scoped calculus (`open scoped
Solidity.Core.Surface`, `Tools/Inspect.lean`): a parameter is bound by
`∀`, and `#step` names the rule `Stmt.step` fires. -/

open scoped Solidity.Core.Surface

/-! What symbolic execution leaves is a formula of updates; reduced, it
reads the initial state alone: it holds wherever `alice.age` is a location
(`has`), where the write returns and the read gives `42`.  `(d; a)` is `a`
where `d` returns. -/

/--
info: symbolic execution leaves:
    dl{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } x = 42 }
update-free:
    has(storage, alice.age) = has(storage, alice.age) → (has(storage, alice.age); 42) = (has(storage, alice.age); 42) → (has(storage, alice.age); 42) = 42
-/
#guard_msgs in #wp dl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 }


/-! Memory is pushed in as one term (`LMem`), printed as KeY writes it: a
copy from storage under its guard (`copyOk`, the subtree copies), the `k`-th
allocation `addM(m, shaped(idpk, T))` and its objects `idC(idpk, flds)`, a
`new T[](n)` as the allocation and the write of its `size`, and a copy of
memory into storage `save(s, p, copyMem(mtSt, m, i))`, read through its
view. -/

/--
info: symbolic execution leaves:
    dl{
  { carol := freshId(copySt(memory, find(storage, alice))) ‖ memory := copySt(memory, find(storage, alice)) }
    { x := read(memory, carol.age) } x = find(storage, alice.age) }
update-free:
    (copyOk(storage, alice); if(orElse((find(storage, alice); true), false)) then err else true) = (copyOk(storage, alice); if(orElse((find(storage, alice); true), false)) then err else true) → find(storage, alice.age) = find(storage, alice.age) → find(storage, alice.age) = find(storage, alice.age)
-/
#guard_msgs in #wp dl!{ [ Person memory carol = alice; uint x = carol.age; ] x == alice.age }

/--
info: symbolic execution leaves:
    dl{
  ∀ uint i;
    ∀ uint n;
      { xs := freshId(copySt(memory, newArr(uint[], n))) ‖ memory := copySt(memory, newArr(uint[], n)) }
        { memory := write(memory, xs[i], 7) }
          { storage := save(storage, values, copyMem(mtSt, memory, xs)) } find(storage, values[i]) = 7 }
update-free:
    ∀ uint i; ∀ uint n; (if(n = n) then true else true) = (if(n = n) then true else true) → ((if(i = i) then true else true); if((0 <= i) && (i < (if(n < 0) then 0 else n))) then true else err) = ((if(i = i) then true else true); if((0 <= i) && (i < (if(n < 0) then 0 else n))) then true else err) → ((if(n = n) then true else true), (if((0 <= i) && (i < (if(n < 0) then 0 else n))) then true else err); has(storage, values)) = ((if(n = n) then true else true), (if((0 <= i) && (i < (if(n < 0) then 0 else n))) then true else err); has(storage, values)) → ((if(n = n) then true else true), (if((0 <= i) && (i < (if(n < 0) then 0 else n))) then true else err), has(storage, values), ok(values[i]); if(orElse((err; true), false)) then find(save(storage, values, copyMem(mtSt, write(write(addM(memory, shaped(idp0, uint[])), idC(idp0, nil), size, n), idC(idp0, nil), at(i), 7), idC(idp0, nil))), values[i]) else if(i = i) then 7 else ((if((0 <= i) && (i < n)) then true else err); 0)) = 7
-/
#guard_msgs in
#wp dl!{ [ uint[] memory xs = new uint[](n); xs[i] = 7; values = xs; ] values[i] == 7 }

/--
info:   ~[storageFieldWriteSave]~>
    dl{ { storage := save(storage, alice.age, 42) } [ uint x = alice.age; ] x = 42 }
-/
#guard_msgs in #step dl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 }

/-- info: no modality left: `close` -/
#guard_msgs in #step dl!{ x == 42 }

/-! A void function's obligation is solkey's `f(x̄)@C;`, a call with no
target: `functionBodyExpand`'s, as a tuple assignment's call is. -/

/--
info:   ~[functionBodyExpand]~>
    dl{
  ((0 <= receiver ∧ receiver <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
        (0 <= amount ∧ amount <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
          (0 <= find(storage, minter) ∧
                find(storage, minter) <=
                  115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
            (∀ uint k1;
                  0 <= find(storage, balances[k1]) ∧
                    find(storage, balances[k1]) <=
                      115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
              msg.value = 0 ∧ amount >= 0) →
    { old := storage }
      [ uint se1 = receiver; uint se2 = amount; require(msg.sender == minter); balances[se1] += se2; ]
        ((find(old, minter) = msg.sender ∧ find(storage, minter) = find(old, minter)) ∧
            find(storage, balances[receiver]) = find(old, balances[receiver]) + amount ∧
              (∀ uint a; ¬a = receiver → find(storage, balances[a]) = find(old, balances[a]))) }
-/
#guard_msgs in #step spec[Benchmark.Coin.Coin]{ mint }

end Inspect

/-! ## `#taclet`

A rule of the calculus by its constructor, and a solkey taclet by its `.key`
name: `storageFieldWriteCaptureSrc` is one of the two taclets
`storageFieldRead_unfold_rightSndResult` merges.  Terms print in KeY's long
forms (`consr(sp, fld)`, `pp.sol.key`), and a fresh name beside the schema
variable it copies is primed (`sp'`). -/

/--
info: Solidity.Core.Taclet.storageFieldWriteSave : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {x : Name}
  {sp : Core.SPath C Γ (Ty.struct x)} {fld : Name} {x_1 : PrimTy} {se : Core.Simple C Γ x_1},
  dl{ ⟨[ sp.fld = se; ]⟩ ⇝ { storage := save(storage, consr(sp, fld), se) } ⟨[ ]⟩ }
solkey: storageFieldWriteSave (simplify_prog)
printed: storageFieldWriteSave
sound: Solidity.Core.Taclet.toStep (the premise is Stmt.step's; Core.Stmt.Sound)
-/
#guard_msgs in #taclet storageFieldWriteSave

/--
info: solkey: storageFieldWriteCaptureSrc (simplify_prog), transcribed by

Solidity.Core.Taclet.storageFieldRead_unfold_rightSndResult : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx}
  {x : RefTy} {loc : Core.Loc C Γ (Ty.ref x)} {x_1 : Name} {sp : Core.SPath C Γ (Ty.struct x_1)} {fld : Name}
  {hm : (Ty.ref x).mapFree = true}, dl{ ⟨[ loc = sp.fld; ]⟩ ⇝ ⟨[ T storage sp' = sp.fld; loc = sp'; ]⟩ }
solkey (merged): storageFieldRead_unfold_rightSndResult (simplify_prog), storageFieldWriteCaptureSrc (simplify_prog)
printed (merged): storageFieldRead_unfold_rightSndResult, storageFieldWriteCaptureSrc
sound: Solidity.Core.Taclet.toStep (the premise is Stmt.step's; Core.Stmt.Sound)
-/
#guard_msgs in #taclet "storageFieldWriteCaptureSrc"

/-! A rule solkey does not have, and a solkey taclet no rule claims.  The
call it fires on has an argument that is not simple, so it is neither `fbs`
nor `ic` (calls whose arguments are all simple, `functionBodyExpand`'s and
`internalCallExpand`'s). -/

/--
info: Solidity.Core.LeanTaclet.functionCallArgCapture : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {f : Name}
  {ps : Core.Ctx} {args : Core.Args C Γ ps} {rs Γ' : Core.Ctx} {ret : Core.CallRet Γ rs Γ'} {Γf : Core.Ctx}
  {body : Core.Prog C (rs ++ ps) Γf} {p : PrimTy} {v : Core.Val C Γ p} {as' : Core.Args C (Core.LTy.val p :: Γ) ps},
  dl[Core.LeanTaclet C k]{ ⟨[ ‹Surface.Stmt.call f args hsep ret body›; ]⟩ ⇝
    ⟨[ T se = v; ‹Surface.Stmt.call f as' ⋯ ret body›; ]⟩ }
solkey: none (a rule solkey does not have)
printed: none (theory only Lean has)
sound: Solidity.Core.LeanTaclet.toStep (the premise is Stmt.step's; Core.Stmt.Sound)
-/
#guard_msgs in #taclet functionCallArgCapture

/--
info: solkey: ifTrue (concrete_solidity)
no Lean rule claims it (`RuleShapes.unclaimedTaclets` says why)
-/
#guard_msgs in #taclet ifTrue

/-! Every rule prints as a rule line (`#check_rule_text`, `Tools/Taclet.lean`). -/

/--
info: all 159 rules of `Solidity.Core.Taclet` print as rule lines
---
info: all 9 rules of `Solidity.Core.LeanTaclet` print as rule lines
---
info: all 3 rules of `Solidity.Core.CallbackTaclet` print as rule lines
-/
#guard_msgs in #check_rule_text

/-! A send's labelled goals (`Premise.cases`), and its callback rule; each is
sound as its premise is the one `Stmt.step` builds (`toStep`). -/

/--
info: Solidity.Core.Taclet.sendNoCallbackBox : ∀ {C : Contract} {k : Nat} {Γ : Core.Ctx}
  {pv : Core.Idx Γ (Core.LTy.val PrimTy.bool)} {sadr se : Core.Simple C Γ PrimTy.uint},
  dl{ [ pv = sadr .send(se); ] ⇝
    "send succeeded":
        { net := if(sadr = self) then net else storeSt(net, at(sadr), selectSt(net, at(sadr)) - se) ‖ pv := true } ⟨[
        ]⟩ ;
      "send failed": { pv := false } ⟨[ ]⟩ }
solkey: sendNoCallbackBox (simplify_prog)
printed: none (a solkey taclet not printed)
sound: Solidity.Core.Taclet.toStep (the premise is Stmt.step's; Core.Stmt.Sound)
-/
#guard_msgs in #taclet sendNoCallbackBox

/--
info: Solidity.Core.CallbackTaclet.sendWithCallbackBox : ∀ {C : Contract} {k : Nat} {Γ : Core.Ctx}
  {pv : Core.Idx Γ (Core.LTy.val PrimTy.bool)} {sadr se : Core.Simple C Γ PrimTy.uint},
  dl[Core.CallbackTaclet C k]{ [ pv = sadr .send(se); ] ⇝
    "send succeeded":
        { net := if(sadr = self) then net else storeSt(net, at(sadr), selectSt(net, at(sadr)) - se) ‖ pv := true } ⟨[
        ]⟩ ;
      "send failed": { pv := false } ⟨[ ]⟩ }
solkey: sendWithCallbackBox (simplify_prog)
printed: none (a solkey taclet not printed)
sound: Solidity.Core.CallbackTaclet.toStep (the premise is Stmt.step's; Core.Stmt.Sound, Core.ProvesC.sound_of)
-/
#guard_msgs in #taclet sendWithCallbackBox

/-! ## `#difftest`

Every function of the contract, called `runs` times from random storages,
in the interpreter and on the machine; they agree, the reverts included, a
payment the world refuses among them (`pay`).  `#difftest C.f` tests one
function, on the same runs as `#difftest C`. -/

/--
info: addOne: 50 runs agree (0 revert)
double: 50 runs agree (16 revert)
addTwo: 50 runs agree (4 revert)
credit: 50 runs agree (8 revert)
larger: 50 runs agree (0 revert)
bump: 50 runs agree (2 revert)
-/
#guard_msgs in #difftest CallsExample (runs := 50) (seed := 1)

/-- info: credit: 50 runs agree (8 revert) -/
#guard_msgs in #difftest CallsExample.credit (runs := 50) (seed := 1)

/-- A contract whose functions reach every kind of storage the compiler lays
out: an `int`, a `bool`, a dynamic and a fixed-size array, structs, a
mapping of structs, a struct holding a mapping; and `push`, `pop`, `delete`,
a copy, `transfer`, `require`.  `viaMemory` declares a memory local, which
the compiler does not take: `#difftest` skips it. -/
def Mixed : Contract := contract!{
  uint total; int signed; bool flag;
  uint[] values; Person alice; Person[] people;
  mapping(uint => Person) folks; mapping(uint => uint) balances;
  uint[3] fixedValues; Wallet wallet; Toggle toggle;
  function put(uint k, uint v) { balances[k] = v; total = total + v; }
  function neg(int x) returns (int) { signed = signed - x; return -x; }
  function grow(uint v) { values.push(v); }
  function shrink() { values.pop(); }
  function ageAt(uint i) returns (uint) { return people[i].age; }
  function setFolk(uint k) { folks[k].age = k * 2; delete alice; }
  function fix(uint i, uint v) { fixedValues[i] = v; }
  function flip() { flag = !flag; toggle.on = flag; toggle.n++; }
  function stash(uint k, uint v) { wallet.stash[k] += v; delete wallet; }
  function pay(uint a, uint v) { a.transfer(v); }
  function guard(uint v) { require(v <= total); total -= v; }
  function copy() { alice = people[0]; }
  function viaMemory() { Person memory p; }
}

/--
info: ok
returns 3
total = 0
signed = 3
flag = false
values = []
alice = {account: {balance: 0, token: {value: 0}}, age: 0}
people = []
folks = {_: {account: {balance: 0, token: {value: 0}}, age: 0}}
balances = {_: 0}
fixedValues = [0, 0, 0]
wallet = {owner: 0, stash: {_: 0}}
toggle = {on: false, n: 0}
-/
#guard_msgs in #run Mixed.neg(-3)

/--
info: put: 50 runs agree (8 revert)
neg: 50 runs agree (3 revert)
grow: 50 runs agree (0 revert)
shrink: 50 runs agree (3 revert)
ageAt: 50 runs agree (39 revert)
setFolk: 50 runs agree (11 revert)
fix: 50 runs agree (37 revert)
flip: 50 runs agree (1 revert)
stash: 50 runs agree (3 revert)
pay: 50 runs agree (14 revert)
guard: 50 runs agree (26 revert)
copy: 50 runs agree (13 revert)
skipped: viaMemory (outside the compiled fragment)
-/
#guard_msgs in #difftest Mixed (runs := 50) (seed := 3)

/-- A failed `assert` panics in the interpreter and reverts on the machine:
the two agree, and the count of reverts includes the panics. -/
def Asserting : Contract := contract!{
  uint count;
  function check(uint x) { assert(x < 1000); count = x; }
  function zero(uint x) { assert(x != 0); count = x; }
}

/--
info: check: 50 runs agree (14 revert)
zero: 50 runs agree (8 revert)
-/
#guard_msgs in #difftest Asserting (runs := 50) (seed := 1)

/-! ## A block run from a state: `Surface.Prog.runT`

The order an `++` inside an expression is captured in is solc's, as
solkey's `TestSuite.sol` pins it: a binary operator's right operand first
(`i++ + i` is `1 + 1`), an assignment's right-hand side before its target
(`a[++i] = ++i` writes `1` at `2`), an index's base before the index
(`matrix[k][k++]` indexes `matrix[0]`).  Run typed from `TestSuite`'s store
(`Surface.Prog.runT`; `Semantics.lean`'s pin of today's run until W4
`modal`). -/

/-- info: (true, true, true) -/
#guard_msgs in
#eval
  ((Surface.Prog.runT Semantics.State.testSuiteStore (sol[TestSuite]{ uint i = 1; uint x = i++ + i;
      assert(x == 2); assert(i == 2); })).isOk,
  (Surface.Prog.runT Semantics.State.testSuiteStore (sol[TestSuite]{ uint i = 0; values.push(100);
      values.push(100); values.push(100); values[++i] = ++i; assert(values[2] == 1); })).isOk,
  (Surface.Prog.runT Semantics.State.testSuiteStore (sol[TestSuite]{ matrix.push(); matrix.push();
      matrix[0].push(0); matrix[1].push(0); uint k = 0; matrix[k][k++] = 77; assert(k == 1);
      assert(matrix[0][0] == 77); assert(matrix[1][0] == 0); })).isOk)

end Solidity.Examples.Tools
