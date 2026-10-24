import Solidity.Syntax.Quote
import Solidity.Syntax.Inlined
import Solidity.Syntax.Elab

/-!
# Elaborating a block, as a term

The elaborator's entry points (`Syntax/Elab.lean`): `elabProgS`,
`elabProgAtS` (and its `go`, which `solc_import` runs per function) and
`ctorProgS` elaborate a block from the locals in scope where it starts into
the scoped syntax (`Prog C Γ Γ'`, `Syntax/Scoped.lean`), each local typed at
its position as it is read, so a block that elaborates is in scope;
`sol[C]{ … }` and `sol{ … }` splice it as a term.  The branches of an `if`
and of a `try`, a loop's body and a call's body are scopes, as in solc, so a
local a branch declares cannot be read after it, and a later branch may
declare the same name at another type.  The block is spliced quoted and
hash-consed (`Prog.quoteShared`), so the kernel checks every local's scope
and type: a block that reads a local out of its scope is an elaboration
error, not a term.
-/

namespace Solidity

section Elab

variable [FreshNames] (C : Contract)

/-- Elaborate a block against `C`, from no locals.  A capture is numbered
past every fresh variable the block writes. -/
def elabProgS (ss : List RawStmt) : Except String (Blk C []) := do
  let k := RawStmt.maxIdxs ss + 1
  let ss ← freshenBlocks (C.vars.map (·.1)) [] ss
  let P ← ((elabStmtsP C ss).run { funs := C.funs }).run' ([], k)
  SProg.chain [] [] P

/-- The statements `ss`, the `i`th first, from the state `st`, each appended
to `acc`, the block so far, which leaves the context named `ns`. -/
def elabProgAtS.goWt {Γ₀ : Ctx} (i : Nat) (ss : List RawStmt) (st : ECtx × Nat)
    (ns : List Var) (acc : Blk C Γ₀) (mutableFreshNames : List String := []) :
    Except (Nat × String) (Blk C Γ₀) :=
  match ss with
  | [] => pure acc
  | s :: ss =>
    match ((elabStmtP C s).run { funs := C.funs, mutableFreshNames }).run st with
    | .error e => .error (i, e)
    | .ok (P, st) =>
      match SProg.chain ns acc.1 P with
      | .error e => .error (i, e)
      | .ok b =>
        match Blk.append acc b with
        | .error e => .error (i, e)
        | .ok acc' => elabProgAtS.goWt (i + 1) ss st (b.2.outNames ns) acc' mutableFreshNames

/-- `elabProgS`, from the state `st`, an error naming the statement of the
block it arose in (its position, from `i`): the same block, statement by
statement, each typed from the locals the ones before it leave. -/
def elabProgAtS.go (i : Nat) (ss : List RawStmt) (st : ECtx × Nat) (source : Bool := false) :
    Except (Nat × String) (Blk C (ECtx.toNCtx st.1).ctx) := do
  -- a block's locals renamed apart (`freshenBlocks`)
  let ss ← (freshenBlocks (C.vars.map (·.1)) (st.1.map (·.1)) ss).mapError (i, ·)
  let names := if source then
    C.vars.map (·.1) ++ st.1.map (·.1) ++ RawStmt.namesList ss ++ RawStmt.declsList ss else []
  let st := if source then
    (st.1, names.foldl (fun k x => max k ((Var.ofName x).idx + 1)) st.2) else st
  elabProgAtS.goWt C i ss st (ECtx.toNCtx st.1).names ⟨_, .nil⟩ names

/-- `elabProgS`, an error naming the statement of the block it arose in. -/
def elabProgAtS (ss : List RawStmt) : Except (Nat × String) (Blk C []) :=
  elabProgAtS.go C 0 ss ([], RawStmt.maxIdxs ss + 1)

/-- A deployment's program, `constructor(args);`, elaborated (`elabCtor`):
nothing for a contract that declares no constructor and no initializer. -/
def ctorProgS (args : List RawExpr) : Except String (Blk C []) :=
  if C.ctor.isNone && C.inits.isEmpty && args.isEmpty then .ok ⟨[], .nil⟩
  else elabProgS C [.call (.name "constructor") args]

end Elab

/-! ## `sol[C]{ … }` -/

/-- `sol[C]{ s₁; s₂; … }`: the statements, elaborated against the named
contract `C`. -/
syntax (name := solBracket) "sol[" term "]{" (sol_stmt solSemi)* "}" : term

/-- `sol{ … }`: `sol[C]{ … }` for the file's `InContract` contract. -/
syntax "sol{" (sol_stmt solSemi)* "}" : term

open Lean Elab Term Meta in
/-- Run `f C` at compile time for the contract the term `c` names, and splice
the term it computes, of type `Except ε Lean.Expr` (`ε` the Lean type `errTy`);
an error is reported by `onErr`.  `c` is unfolded through instances only, so
it may be `InContract.contract` but must end at a named contract. -/
def elabAgainstWith {ε : Type} (errTy : Lean.Expr) (onErr : ε → TermElabM Lean.Expr)
    (c : Lean.Term) (f : Lean.Term → TermElabM Lean.Term) : TermElabM Lean.Expr := do
  let C ← withTransparency .instances <| whnf (← elabTermAndSynthesize c (mkConst ``Contract))
  let some n := C.constName? | throwError "not a named contract: {C}"
  let t ← f (← `(Lean.mkConst $(quote n)))
  let ty := mkApp2 (mkConst ``Except [0, 0]) errTy (mkConst ``Lean.Expr)
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  match ← unsafe evalExpr (Except ε Lean.Expr) ty e with
  | .ok r => pure r
  | .error err => onErr err

open Lean Elab Term Meta in
/-- `elabAgainstWith`, an error reported at the source. -/
def elabAgainst (c : Lean.Term) (f : Lean.Term → TermElabM Lean.Term) : TermElabM Lean.Expr :=
  elabAgainstWith (ε := String) (mkConst ``String)
    (fun msg => throwError "Solidity elaboration failed: {msg}") c f

open Lean Elab Term Meta in
@[term_elab solBracket]
def elabSolBracket : TermElab := fun stx _ => do
  match stx with
  | `(sol[ $c ]{ $[$ss:sol_stmt;]* }) =>
    let raw ← `(sol_raw!{ $[$ss;]* })
    -- an error is reported at the statement it arose in
    let errTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``String)
    let ref ← getRef
    let stmts : Array Syntax := ss.map TSyntax.raw
    elabAgainstWith (ε := Nat × String) errTy (fun ((i, msg) : Nat × String) =>
        throwErrorAt (stmts[i]?.getD ref) "Solidity elaboration failed: {msg}") c
      fun q => `((elabProgAtS $c $raw).map fun (b : Blk $c []) => (Prog.quoteShared $q b.2).1)
  | _ => throwUnsupportedSyntax

macro_rules
  | `(sol{ $[$ss;]* }) => `(sol[InContract.contract]{ $[$ss;]* })

/-! ## Examples -/

section Examples

local instance : InContract := ⟨StandardExample⟩

/-- A block over `StandardExample`: a local, an alias, writes through both,
a mapping entry, a branch on a comparison, a delete, a struct copy into a
mapping, a guard. -/
def tour := sol{
  uint x = alice.age + 1;
  Person storage p = alice;
  p.age = x;
  balances[x] = 10;
  if (x > 3) { alice.age = 0; } else { revert(); };
  delete bob.account;
  folks[1] = bob;
  require(flags[x] || x == 2);
}

/--
info: uint x = alice.age + 1;
Person storage p = alice;
p.age = x;
balances[x] = 10;
if (x > 3) { alice.age = 0; } else { revert(); }
delete bob.account;
folks[1] = bob;
require(flags[x] || (x == 2));
-/
#guard_msgs in #eval IO.println (Prog.show [] tour)

/-- A compound target at a non-simple index captures the index first. -/
example : Prog.toStr [] (sol{ values[total + 1] += 2; }) =
    "uint ie1 = total + 1; values[ie1] += 2;" := rfl

/-- The captures are numbered past the fresh variables the block writes. -/
example : Prog.toStr [] (sol{ uint ie4 = 1; values[total + 1] += 2; }) =
    "uint ie4 = 1; uint ie5 = total + 1; values[ie5] += 2;" := rfl

/-- `lsv = sp.push()` and `T storage lsv = sp.push()`. -/
example : Prog.toStr [] (sol{ Person storage p = people.push(); p = persons.push(); }) =
    "Person storage p = people.push(); p = persons.push();" := rfl

/-- error: Solidity elaboration failed: age is already declared, or names a state variable -/
#guard_msgs in #check sol{ uint age = 1; }

/-- error: Solidity elaboration failed: a storage reference where a uint is expected -/
#guard_msgs in #check sol{ uint y = alice; }

/-- error: Solidity elaboration failed: `delete` on a storage pointer -/
#guard_msgs in #check sol{ Person storage q = alice; delete q; }

/-- error: Solidity elaboration failed: struct Person has no member balance -/
#guard_msgs in #check sol{ alice.balance = 1; }

/-- error: Solidity elaboration failed: a storage copy of a type that holds a mapping -/
#guard_msgs in #check sol{ wallet = wallet; }

/-- `.length` is a value: of a storage array and of a memory one. -/
example : Prog.toStr [] (sol{ uint n = values.length; uint[] memory xs = new uint[](n);
    n = xs.length; }) =
    "uint n = values.length; uint[] memory xs = new uint[](n); n = xs.length;" := rfl

/-- A decrement is spelled `−−` (two U+2212): `--` opens a Lean comment. -/
example : Prog.toStr [] (sol{ total−−; −−total; uint y = 0; y = total−−; }) =
    "total−−; −−total; uint y = 0; y = total−−;" := rfl

/-- `++` inside an expression is captured before its statement, into a fresh
local. -/
example : Prog.toStr [] (sol{ uint i = 0; values[i++] = 1; }) =
    "uint i = 0; uint se1; se1 = i++; values[se1] = 1;" := rfl

/-- A conditional of references binds a fresh alias, declared before the branches. -/
example : Prog.toStr [] (sol{ bool c = true; Person storage p = c ? alice : bob; }) =
    "bool c = true; Person storage sp1; if (c) { sp1 = alice; } else { sp1 = bob; } \
    Person storage p = sp1;" := rfl

/-- A memory one declares its `mv1` before the branches, bound to a branch
that indexes nothing (a read that cannot revert on a set local; an unset
one, which only a hidden binder holds, reverts there where solc reads the
other branch), and rebinds it in each: the branches are scopes. -/
example : Prog.toStr [] (sol{ bool c = true; Person memory mx = alice; Person memory my = bob;
    Person memory m = c ? mx : my; }) =
    "bool c = true; Person memory mx = alice; Person memory my = bob; \
    Person memory mv1 = mx; if (c) { mv1 = mx; } else { mv1 = my; } \
    Person memory m = mv1;" := rfl

/-- Both indexing, it is bound to a fresh default object first. -/
example : Prog.toStr [] (sol{ bool c = true; Person[] memory xs = new Person[](2);
    Person memory m = c ? xs[0] : xs[1]; }) =
    "bool c = true; Person[] memory xs = new Person[](2); Person memory mv1; \
    if (c) { mv1 = xs[0]; } else { mv1 = xs[1]; } Person memory m = mv1;" := rfl

-- The scope is the type's: a local nothing declares, one read at another
-- type than declared, one a branch declares read after it.
/-- error: Solidity elaboration failed: unknown name x -/
#guard_msgs in #check sol{ bool b; x = 1; }

/-- error: Solidity elaboration failed: a number where a bool is expected -/
#guard_msgs in #check sol{ bool b; b = 1; }

/-- error: Solidity elaboration failed: a bool where a uint is expected -/
#guard_msgs in #check sol{ bool b; uint y = b; }

/-- error: Solidity elaboration failed: unknown name y -/
#guard_msgs in #check sol{ bool c; if (c) { uint y; } else { } y = 1; }

/-- So a later branch may declare the same name at another type. -/
example : Prog.toStr [] (sol{ uint t = 0; if (t > 0) { bool y = true; } else { }
    if (t > 1) { uint y = 1; } else { } }) =
    "uint t = 0; if (t > 0) { bool y = true; } else { } if (t > 1) { uint y = 1; } else { }" := rfl

/-- An increment under `&&` is evaluated only when the left operand does not
decide: the right operand runs in a branch (solkey's `logicalAndShortCircuitRhs`). -/
example : Prog.toStr [] (sol{ bool c = true; uint i = 0; c = c && i++ > 0; } :
    Prog StandardExample [] _) =
    "bool c = true; uint i = 0; bool se1 = c; if (se1) { uint se2; se2 = i++; se1 = se2 > 0; } else { } c = se1;" := by
  decide

/-- A negative literal takes the type it stands at. -/
example : (sol{ int e = -5; } : Prog StandardExample [] _) =
    .cons (.declLocal .int (.user "e") (some (.simple (.lit (-5) rfl)))) .nil := rfl

/-- info: int e = -5; -/
#guard_msgs in #eval IO.println (Prog.show [] (sol{ int e = -5; } : Prog StandardExample [] _))

/-- A constant expression is folded as solc folds it: an operand out of
range whose result is in range is accepted (`BinOp.foldLit?`). -/
example : (sol{ uint x = 115792089237316195423570985008687907853269984665640564039457584007913129639936 - 1;
    int y = 57896044618658097711785492504343953926634992332820282019728792003956564819968 - 1; } :
    Prog StandardExample [] _) =
    .cons (.declLocal .uint (.user "x") (some (.simple (.lit 115792089237316195423570985008687907853269984665640564039457584007913129639935 rfl))))
     (.cons (.declLocal .int (.user "y") (some (.simple (.lit 57896044618658097711785492504343953926634992332820282019728792003956564819967 rfl)))) .nil) := rfl

-- One whose result is out of range is refused.
/-- error: Solidity elaboration failed: the literal 115792089237316195423570985008687907853269984665640564039457584007913129639937 is out of the range of uint -/
#guard_msgs in #check sol{ uint x = 115792089237316195423570985008687907853269984665640564039457584007913129639936 + 1; }

/-- `delete` in memory, and a fresh array written to a location. -/
example : Prog.toStr [] (sol[TestSuite]{ Person memory m; delete m.age; delete m;
    basketA.items = new uint[](2); }) =
    "Person memory m; delete m.age; delete m; basketA.items = new uint[](2);" := rfl

/-- A call is its body inlined, every local of the callee fresh. -/
example : Prog.toStr [] (sol[CallsExample]{ uint y = addTwo(3); credit(y, 2); bump(); }) =
    "uint y; y = addTwo(3); credit(y, 2); bump();" := rfl

/-! What the calls run: `addTwo` calls `addOne` twice, `larger` returns from
both branches of its last `if`. -/

/--
info: uint y; uint se1 = 3; uint se2; uint se3 = se1; uint se4; se4 = se3 + 1; se2 = se4; uint se5 = se2; uint se6; se6 = se5 + 1; se2 = se6; y = se2; uint z; uint se7 = y; uint se8 = 7; uint se9; if (se7 > se8) { se9 = se7; } else { se9 = se8; } z = se9;
-/
#guard_msgs in
#eval IO.println (Prog.inlinedStr [] (sol[CallsExample]{ uint y = addTwo(3); uint z = larger(y, 7); }))

/-- error: Solidity elaboration failed: addOne is not a function declared before this one -/
#guard_msgs in #check sol[StandardExample]{ uint y = addOne(1); }

/-- error: Solidity elaboration failed: addOne takes 1 arguments, not 2 -/
#guard_msgs in #check sol[CallsExample]{ uint y = addOne(1, 2); }

/-! ### Friendlier spellings -/

/-- `else if`: the `if`s nested. -/
example : Prog.toStr [] (sol{ if (total > 2) { total = 1; } else if (total > 1) { total = 2; }
    else if (total > 0) { total = 3; } else { total = 4; } }) =
    "if (total > 2) { total = 1; } else { if (total > 1) { total = 2; } else { \
    if (total > 0) { total = 3; } else { total = 4; } } }" := rfl

/-- A statement ending in a block needs no `;`; one with it reads the same. -/
example : (sol{ if (total > 0) { total = 0; } unchecked { total += 1; } total = 1; } :
    Prog StandardExample [] _) = sol{ if (total > 0) { total = 0; }; unchecked { total += 1; }; total = 1; } :=
  rfl

/-- `address payable` is an `address`, a `uint`. -/
example : Prog.toStr [] (sol{ address payable a = owner; }) = "uint a = owner;" := rfl

/-- error: Solidity elaboration failed: unknown type Foo -/
#guard_msgs in #check sol{ Foo x; }

-- A struct that repeats a member name is refused, as solc refuses its
-- declaration ("Identifier already declared", `refusedStructs`, decision 16).
/-- error: Solidity elaboration failed: struct BadDup: identifier already declared: member a -/
#guard_msgs in #check sol{ BadDup memory x; }

/-- A `uint8` is a `uint` whose arithmetic is checked at 8 bits (`narrowPost`);
`Examples/Tactics/Checked.lean` has the rest. -/
example : Prog.toStr [] (sol{ uint8 x = 250; x += 10; }) =
    "uint x = 250; x += 10; require(x <= 255);" := rfl

/-- error: Solidity elaboration failed: unknown type uint7: the integer types are `uint8` … `uint256` and `int8` … `int256`, in steps of 8 -/
#guard_msgs in #check sol{ uint7 x = 1; }

/-- error: Solidity elaboration failed: total is indexed, but it is a uint, not a mapping or an array -/
#guard_msgs in #check sol{ total[1] = 2; }

/-- error: Solidity elaboration failed: alice: an operand of reference type Person -/
#guard_msgs in #check sol{ total = alice + 1; }

/-- error: Solidity elaboration failed: alice: a storage reference to a Person where a Person[] is expected -/
#guard_msgs in #check sol{ Person[] storage ps = alice; }

/-! ### Declared

A block declared for the kernel to check (`Prog.define`): the calls of
`CallsExample`, which `Semantics/Run.lean` runs. -/

open Lean Elab Command in
run_cmd liftCoreM do
  match elabProgS CallsExample (sol_raw!{ uint y = addTwo(3); uint z = larger(y, 7); }) with
  | .error e => throwError "callsCore: {e}"
  | .ok ⟨_, P⟩ =>
    if let some e ← Prog.define `Solidity.callsCore ``CallsExample P then
      throwError "callsCore: {e}"

example : (sol[CallsExample]{ uint y = addTwo(3); uint z = larger(y, 7); } :
    Prog CallsExample [] _) = callsCore := rfl

/--
info: uint y;
y = addTwo(3);
uint z;
z = larger(y, 7);
-/
#guard_msgs in
#eval IO.println (Prog.show [] (sol[CallsExample]{ uint y = addTwo(3); uint z = larger(y, 7); }))

end Examples

end Solidity
