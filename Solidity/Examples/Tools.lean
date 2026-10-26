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
start state is given whole, with `from`: a typed state (`State C []`), here
`State.init` with its storage written out. -/

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
#run CallsExample.bump() from ((State.init CallsExample).withStorage
  (.cons (.prim ⟨0, rfl⟩) (.cons (.prim ⟨41, rfl⟩) (.cons (.map .nil (.prim ⟨0, rfl⟩)) .nil))))

/-! ## `#wp` and `#step` -/

section Inspect

local instance : InContract := ⟨StandardExample⟩

/-! The formulas read the scoped calculus (`open scoped
Solidity.Scoped`, `Tools/Inspect.lean`): a parameter is bound by
`∀`, and `#step` names the rule `Stmt.step` fires. -/

open scoped Scoped

/-! What symbolic execution leaves is a formula of updates; reduced, it
reads the initial state alone: the write returns (`alice.age` is a location
of the typed storage) and the read gives `42`.  `(d; a)` is `a` where `d`
returns. -/

/--
info: symbolic execution leaves:
    dl{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } x = 42 }
update-free:
    true = true → ∀ uint x; true = true → 42 = 42
-/
#guard_msgs in #wp dl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 }

/-! Imported obligations are declared without executable code. The inspector
reads their declaration values, as symbolic execution does. -/
noncomputable def declaredObligation : Fml StandardExample [] :=
  dl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 }

/--
info: symbolic execution leaves:
    dl{ { storage := save(storage, alice.age, 42) } { x := find(storage, alice.age) } x = 42 }
update-free:
    true = true → ∀ uint x; true = true → 42 = 42
-/
#guard_msgs in #wp declaredObligation

/--
info:   ~[storageFieldWriteSave]~>
    dl{ { storage := save(storage, alice.age, 42) } [ uint x = alice.age; ] x = 42 }
-/
#guard_msgs in #step declaredObligation


/-! Memory is pushed in as terms of the typed heap: a copy from storage is
the pair `copy` (the root it allocates) and `copySt` (the memory after
it), a `new T[](n)` the copy of `newArr(n)`, a write `write(m, a, v)` and
a copy of memory into storage `copyMem(m, r)`; the reduction reads each
as solkey's memory rules do. -/

/--
info: symbolic execution leaves:
    dl{
  { carol := freshId(copySt(memory, find(storage, alice))) ‖ memory := copySt(memory, find(storage, alice)) }
    { x := read(memory, carol.age) } x = find(storage, alice.age) }
update-free:
    (copy(memory, select(storage, alice)); if(true = true) then true else err) = (copy(memory, select(storage, alice)); if(true = true) then true else err) → ∀ uint x; ((if(true = true) then find(storage, alice.age) else err); true) = ((if(true = true) then find(storage, alice.age) else err); true) → (if(true = true) then find(storage, alice.age) else err) = find(storage, alice.age)
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
    ∀ uint i; ∀ uint n; (copy(memory, newArr(n)); true) = (copy(memory, newArr(n)); true) → (if(i < n = true) then true else err) = (if(i < n = true) then true else err) → (copyMem(write(copySt(memory, newArr(n)), copy(memory, newArr(n))[i], 7), copy(memory, newArr(n))); true) = (copyMem(write(copySt(memory, newArr(n)), copy(memory, newArr(n))[i], 7), copy(memory, newArr(n))); true) → (copyMem(write(copySt(memory, newArr(n)), copy(memory, newArr(n))[i], 7), copy(memory, newArr(n))), copyMem(write(copySt(memory, newArr(n)), copy(memory, newArr(n))[i], 7), copy(memory, newArr(n))), (if(i < (if(true = true) then size(write(copySt(memory, newArr(n)), copy(memory, newArr(n))[i], 7), copy(memory, newArr(n))) else 0)) then true else err); if(if(i < (if(true = true) then size(write(copySt(memory, newArr(n)), copy(memory, newArr(n))[i], 7), copy(memory, newArr(n))) else 0)) then (if(true = true) then (i < size(write(copySt(memory, newArr(n)), copy(memory, newArr(n))[i], 7), copy(memory, newArr(n)))) else false) else has(storage, values[i])) then (if(i < (if(true = true) then size(write(copySt(memory, newArr(n)), copy(memory, newArr(n))[i], 7), copy(memory, newArr(n))) else 0)) then (if(if(true = true) then (i < size(write(copySt(memory, newArr(n)), copy(memory, newArr(n))[i], 7), copy(memory, newArr(n)))) else false = true) then read(write(copySt(memory, newArr(n)), copy(memory, newArr(n))[i], 7), copy(memory, newArr(n))[i]) else 0) else if(i < find(storage, values.length)) then 0 else find(storage, values[i])) else err) = 7
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
info: Solidity.Taclet.storageFieldWriteSave : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {x : Name}
  {sp : SPath C Γ (Ty.struct x)} {fld : Name} {x_1 : PrimTy} {se : Simple C Γ x_1},
  dl{ ⟨[ sp.fld = se; ]⟩ ⇝ { storage := save(storage, consr(sp, fld), se) } ⟨[ ]⟩ }
solkey: storageFieldWriteSave (simplify_prog)
printed: storageFieldWriteSave
sound: Solidity.Taclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet storageFieldWriteSave

/--
info: solkey: storageFieldWriteCaptureSrc (simplify_prog), transcribed by

Solidity.Taclet.storageFieldRead_unfold_rightSndResult : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {x : RefTy}
  {loc : Loc C Γ (Ty.ref x)} {x_1 : Name} {sp : SPath C Γ (Ty.struct x_1)} {fld : Name}
  {hm : (Ty.ref x).mapFree = true}, dl{ ⟨[ loc = sp.fld; ]⟩ ⇝ ⟨[ T storage sp' = sp.fld; loc = sp'; ]⟩ }
solkey (merged): storageFieldRead_unfold_rightSndResult (simplify_prog), storageFieldWriteCaptureSrc (simplify_prog)
printed (merged): storageFieldRead_unfold_rightSndResult, storageFieldWriteCaptureSrc
sound: Solidity.Taclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet "storageFieldWriteCaptureSrc"

/-! A rule solkey does not have, and a solkey taclet no rule claims.  The
call it fires on has an argument that is not simple, so it is neither `fbs`
nor `ic` (calls whose arguments are all simple, `functionBodyExpand`'s and
`internalCallExpand`'s). -/

/--
info: Solidity.LeanTaclet.functionCallArgCapture : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {f : Name} {ps : Ctx}
  {args : Args C Γ ps} {rs Γ' : Ctx} {ret : CallRet Γ rs Γ'} {Γf : Ctx} {body : Prog C (rs ++ ps) Γf} {p : PrimTy}
  {v : Val C Γ p} {as' : Args C (LTy.val p :: Γ) ps},
  dl[LeanTaclet C k]{ ⟨[ ‹Stmt.call f args ret body›; ]⟩ ⇝ ⟨[ T se = v; ‹Stmt.call f as' ret body›; ]⟩ }
solkey: none (a rule solkey does not have)
printed: none (theory only Lean has)
sound: Solidity.LeanTaclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet functionCallArgCapture

/-! `ifElseJoin`'s update is what `Upd.ifJoin?` computes of the branches,
the side condition the printer hides (`{ u }`): `{ x := (se ? x + 1 : x) }`
for `if (se) { x = x + 1; }` (`Examples/Tactics/Join.lean`). -/

/--
info: Solidity.LeanTaclet.ifElseJoin : ∀ {C : Contract} {k : Nat} {Γ x : Ctx} {thenStm : Prog C Γ x} {x_1 : Ctx}
  {elseStm : Prog C Γ x_1} {m : Modality} {se : Simple C Γ PrimTy.bool} {u : Upd C Γ Γ},
  dl[LeanTaclet C k]{ ⟨[ if (se) thenStm else elseStm; ]⟩ ⇝ { u } ⟨[ ]⟩ }
solkey: none (a rule solkey does not have)
printed: none (theory only Lean has)
sound: Solidity.LeanTaclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet ifElseJoin

/--
info: solkey: ifTrue (concrete_solidity)
no Lean rule claims it (`RuleShapes.unclaimedTaclets` says why)
-/
#guard_msgs in #taclet ifTrue

/-! Every rule prints as a rule line (`#check_rule_text`, `Tools/Taclet.lean`). -/

/--
info: all 181 rules of `Solidity.Taclet` print as rule lines
---
info: all 27 rules of `Solidity.LeanTaclet` print as rule lines
---
info: all 4 rules of `Solidity.CallbackTaclet` print as rule lines
-/
#guard_msgs in #check_rule_text

/-! A send's labelled goals (`Premise.cases`), and its callback rule; each is
sound as its premise is the one `Stmt.step` builds (`toStep`). -/

/--
info: Solidity.Taclet.sendNoCallbackBox : ∀ {C : Contract} {k : Nat} {Γ : Ctx} {pv : Idx Γ (LTy.val PrimTy.bool)}
  {sadr se : Simple C Γ PrimTy.uint} {full : Bool},
  dl{ [ pv = sadr .send(se); ] ⇝
    "send succeeded": { pay(sadr,se) ‖ pv := true } ⟨[ ]⟩ ; "send failed": { pv := false } ⟨[ ]⟩ }
solkey: sendNoCallbackBox (simplify_prog)
printed: none (a solkey taclet not printed)
sound: Solidity.Taclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet sendNoCallbackBox

/--
info: Solidity.CallbackTaclet.sendWithCallbackBox : ∀ {C : Contract} {k : Nat} {Γ : Ctx} {pv : Idx Γ (LTy.val PrimTy.bool)}
  {sadr se : Simple C Γ PrimTy.uint} {full : Bool},
  dl[CallbackTaclet C k]{ [ pv = sadr .send(se); ] ⇝
    "send succeeded": { pay(sadr,se) ‖ pv := true } ⟨[ ]⟩ ; "send failed": { pv := false } ⟨[ ]⟩ }
solkey: sendWithCallbackBox (simplify_prog)
printed: none (a solkey taclet not printed)
sound: Solidity.CallbackTaclet.toStep (the premise is Stmt.step's; Stmt.Sound, ProvesC.sound_of)
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

/-! ## A block run from a state: `Prog.runT`

The order an `++` inside an expression is captured in is solc's, as
solkey's `TestSuite.sol` pins it: a binary operator's right operand first
(`i++ + i` is `1 + 1`), an assignment's right-hand side before its target
(`a[++i] = ++i` writes `1` at `2`), an index's base before the index
(`matrix[k][k++]` indexes `matrix[0]`).  Run typed from `TestSuite`'s store
(`Prog.runT`, from the typed `State.testSuiteStore`). -/

/-- info: (true, true, true) -/
#guard_msgs in
#eval
  ((Prog.runT State.testSuiteStore (sol[TestSuite]{ uint i = 1; uint x = i++ + i;
      assert(x == 2); assert(i == 2); })).isOk,
  (Prog.runT State.testSuiteStore (sol[TestSuite]{ uint i = 0; values.push(100);
      values.push(100); values.push(100); values[++i] = ++i; assert(values[2] == 1); })).isOk,
  (Prog.runT State.testSuiteStore (sol[TestSuite]{ matrix.push(); matrix.push();
      matrix[0].push(0); matrix[1].push(0); uint k = 0; matrix[k][k++] = 77; assert(k == 1);
      assert(matrix[0][0] == 77); assert(matrix[1][0] == 0); })).isOk)

/-! `x = 10` through an alias, typed from `StandardExample`'s store: the
write lands in `alice`, printed from the typed storage (`fmtRoot`). -/

/-- info: Except.ok (some "{account: {balance: 0, token: {value: 0}}, age: 10}") -/
#guard_msgs in
#eval (Prog.runT State.exampleStore (sol[StandardExample]{
    Person storage p = alice; p.age = 10; uint x = alice.age; assert(x == 10); })).map fun τ =>
  Tools.fmtRoot τ.storage "alice"


end Solidity.Examples.Tools
