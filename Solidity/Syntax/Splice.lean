import Solidity.Syntax.Resolve

/-!
# Elaborating a block, checked, as a term

The elaborator's entry points: `elabProg`, `elabProgAt` (and its `go`, which
`solc_import` runs per function) and `ctorProg` run the elaborator
(`Syntax.lean`) and then the locals check, `resolve` (`Syntax/Resolve.lean`),
from the locals in scope where the block starts; `sol[C]{ … }` and
`sol{ … }` splice the checked block as a term (`Prog.quote`).  The other
entry points run the same check: a specification's call (`specPieces`), a
constructor's obligation (`Problem.ctor`) and each statement of a `dl!{ … }`
modality (`Calculus/Notation.lean`).

`resolve` reads the branches of an `if` and of a `try`, a loop's body and a
call's body as scopes, as solc does, so a local a branch declares cannot be
read after it, and a later branch may declare the same name at another type.
-/

namespace Solidity

section Elab

variable [FreshNames] (C : Contract)

/-- Elaborate a block against `C`, from no locals.  A capture is numbered
past every fresh variable the block writes. -/
def elabProg (ss : List RawStmt) : Except String (Prog C) := do
  let k := RawStmt.maxIdxs ss + 1
  let ss ← freshenBlocks (C.vars.map (·.1)) [] ss
  let P ← ((elabStmts C ss).run { funs := C.funs }).run' ([], k)
  let _ ← Core.Prog.resolveCheck [] P
  pure P

/-- `elabProg`, an error naming the statement of the block it arose in (its
position): the same block, statement by statement, each checked
(`resolve`) from the locals the ones before it leave. -/
def elabProgAt (ss : List RawStmt) : Except (Nat × String) (Prog C) :=
  go 0 ss ([], RawStmt.maxIdxs ss + 1)
where
  go (i : Nat) (ss : List RawStmt) (st : ECtx × Nat) : Except (Nat × String) (Prog C) := do
    -- a block's locals renamed apart (`freshenBlocks`)
    let ss ← (freshenBlocks (C.vars.map (·.1)) (st.1.map (·.1)) ss).mapError (i, ·)
    goWt i ss st (ECtx.toNCtx st.1)
  goWt (i : Nat) : List RawStmt → ECtx × Nat → Core.NCtx → Except (Nat × String) (Prog C)
    | [], _, _ => pure []
    | s :: ss, st, Γ =>
      match ((elabStmt C s).run { funs := C.funs }).run st with
      | .error e => .error (i, e)
      | .ok (P, st) =>
        match Core.Prog.resolveCheck Γ P with
        | .error e => .error (i, e)
        | .ok Γ => do pure (P ++ (← goWt (i + 1) ss st Γ))

/-- A deployment's program, `constructor(args);`, elaborated (`elabCtor`):
nothing for a contract that declares no constructor and no initializer. -/
def ctorProg (args : List RawExpr) : Except String (Prog C) :=
  if C.ctor.isNone && C.inits.isEmpty && args.isEmpty then .ok []
  else elabProg C [.call (.name "constructor") args]


end Elab

/-! ## `sol[C]{ … }` -/

/-- `sol[C]{ s₁; s₂; … }`: the statements, elaborated against the named
contract `C`. -/
syntax "sol[" term "]{" (sol_stmt solSemi)* "}" : term

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
elab_rules : term
  | `(sol[ $c ]{ $[$ss:sol_stmt;]* }) => do
    let raw ← `(sol_raw!{ $[$ss;]* })
    -- an error is reported at the statement it arose in
    let errTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``String)
    let ref ← getRef
    let stmts : Array Syntax := ss.map TSyntax.raw
    elabAgainstWith (ε := Nat × String) errTy (fun ((i, msg) : Nat × String) =>
        throwErrorAt (stmts[i]?.getD ref) "Solidity elaboration failed: {msg}") c
      fun q => `((elabProgAt $c $raw).map (Prog.quote $q))

macro_rules
  | `(sol{ $[$ss;]* }) => `(sol[InContract.contract]{ $[$ss;]* })

/-! ## Examples -/

section Examples

local instance : InContract := ⟨StandardExample⟩

/-- A block over `StandardExample`: a local, an alias, writes through both,
a mapping entry, a branch on a comparison, a delete, a struct copy into a
mapping, a guard. -/
def tour : Prog StandardExample := sol{
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
#guard_msgs in #eval IO.println (Prog.show tour)

/-- A compound target at a non-simple index captures the index first. -/
example : Prog.toStr (sol{ values[total + 1] += 2; }) =
    "uint ie1 = total + 1; values[ie1] += 2;" := rfl

/-- The captures are numbered past the fresh variables the block writes. -/
example : Prog.toStr (sol{ uint ie4 = 1; values[total + 1] += 2; }) =
    "uint ie4 = 1; uint ie5 = total + 1; values[ie5] += 2;" := rfl

/-- `lsv = sp.push()` and `T storage lsv = sp.push()`. -/
example : Prog.toStr (sol{ Person storage p = people.push(); p = persons.push(); }) =
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
example : Prog.toStr (sol{ uint n = values.length; uint[] memory xs = new uint[](n);
    n = xs.length; }) =
    "uint n = values.length; uint[] memory xs = new uint[](n); n = xs.length;" := rfl

/-- A decrement is spelled `−−` (two U+2212): `--` opens a Lean comment. -/
example : Prog.toStr (sol{ total−−; −−total; uint y = 0; y = total−−; }) =
    "total−−; −−total; uint y = 0; y = total−−;" := rfl

/-- `++` inside an expression is captured before its statement, into a fresh
local. -/
example : Prog.toStr (sol{ uint i = 0; values[i++] = 1; }) =
    "uint i = 0; uint se1; se1 = i++; values[se1] = 1;" := rfl

/-- A conditional of references binds a fresh alias, declared before the branches. -/
example : Prog.toStr (sol{ bool c = true; Person storage p = c ? alice : bob; }) =
    "bool c = true; Person storage sp1; if (c) { sp1 = alice; } else { sp1 = bob; } \
    Person storage p = sp1;" := rfl

/-- A memory one declares its `mv1` before the branches, bound to a branch
that indexes nothing, and rebinds it in each: the branches are scopes. -/
example : Prog.toStr (sol{ bool c = true; Person memory mx = alice; Person memory my = bob;
    Person memory m = c ? mx : my; }) =
    "bool c = true; Person memory mx = alice; Person memory my = bob; \
    Person memory mv1 = mx; if (c) { mv1 = mx; } else { mv1 = my; } \
    Person memory m = mv1;" := rfl

/-- Both indexing, it is bound to a fresh default object first. -/
example : Prog.toStr (sol{ bool c = true; Person[] memory xs = new Person[](2);
    Person memory m = c ? xs[0] : xs[1]; }) =
    "bool c = true; Person[] memory xs = new Person[](2); Person memory mv1; \
    if (c) { mv1 = xs[0]; } else { mv1 = xs[1]; } Person memory m = mv1;" := rfl

/-- The error of a check, if any. -/
private def checkErr (P : Prog StandardExample) : String :=
  match Core.Prog.resolveCheck [] P with
  | .error e => e
  | .ok _ => ""

-- The locals check names the statement it rejects and the local: `x`, which
-- nothing declares, and `b`, declared a `bool`, read as a `uint`.
#guard checkErr [.declLocal .bool (.user "b") none, .assignLocal (.user "x") (.simple (.lit (p := .uint) 1 rfl))] =
  "the locals check (`resolve`) rejects `x = 1;`: x is not declared"
#guard checkErr [.declLocal .bool (.user "b") none, .assignLocal (.user "b") (.simple (.lit (p := .uint) 1 rfl))] =
  "the locals check (`resolve`) rejects `b = 1;`: b is declared as bool, used as uint"

-- A branch is a scope: what it declares is not seen after it.
#guard checkErr [.declLocal .bool (.user "c") none,
  .ite (.simple (.local (.user "c"))) [.declLocal .uint (.user "y") none] [],
  .assignLocal (.user "y") (.simple (.lit (p := .uint) 1 rfl))] =
  "the locals check (`resolve`) rejects `y = 1;`: y is not declared"

/-- So a later branch may declare the same name at another type. -/
example : Prog.toStr (sol{ uint t = 0; if (t > 0) { bool y = true; } else { }
    if (t > 1) { uint y = 1; } else { } }) =
    "uint t = 0; if (t > 0) { bool y = true; } else { } if (t > 1) { uint y = 1; } else { }" := rfl

-- An increment under `&&` is evaluated only when the left operand does not
-- decide, so it cannot be captured before the statement.
/-- error: Solidity elaboration failed: `++` or `−−` under a short-circuit operator -/
#guard_msgs in #check sol{ bool c = true; uint i = 0; c = c && i++ > 0; }

/-- A negative literal takes the type it stands at. -/
example : (sol{ int e = -5; } : Prog StandardExample) =
    [.declLocal .int (.user "e") (some (.simple (.lit (-5) rfl)))] := rfl

/-- info: int e = -5; -/
#guard_msgs in #eval IO.println (Prog.show (sol{ int e = -5; } : Prog StandardExample))

/-- A constant expression is folded as solc folds it: an operand out of
range whose result is in range is accepted (`BinOp.foldLit?`). -/
example : (sol{ uint x = 115792089237316195423570985008687907853269984665640564039457584007913129639936 - 1;
    int y = 57896044618658097711785492504343953926634992332820282019728792003956564819968 - 1; } :
    Prog StandardExample) =
    [.declLocal .uint (.user "x") (some (.simple (.lit 115792089237316195423570985008687907853269984665640564039457584007913129639935 rfl))),
     .declLocal .int (.user "y") (some (.simple (.lit 57896044618658097711785492504343953926634992332820282019728792003956564819967 rfl)))] := rfl

-- One whose result is out of range is refused.
/-- error: Solidity elaboration failed: the literal 115792089237316195423570985008687907853269984665640564039457584007913129639936 is out of the range of uint -/
#guard_msgs in #check (sol{ uint x = 115792089237316195423570985008687907853269984665640564039457584007913129639936 + 1; } : Prog StandardExample)

/-- `delete` in memory, and a fresh array written to a location. -/
example : Prog.toStr (sol[TestSuite]{ Person memory m; delete m.age; delete m;
    basketA.items = new uint[](2); }) =
    "Person memory m; delete m.age; delete m; basketA.items = new uint[](2);" := rfl

/-- A call is its body inlined, every local of the callee fresh. -/
example : Prog.toStr (C := CallsExample) (sol[CallsExample]{ uint y = addTwo(3); credit(y, 2); bump(); }) =
    "uint y; y = addTwo(3); credit(y, 2); bump();" := rfl

/-- Each call of a block replaced by its inlined body, for display. -/
partial def Prog.inlined {C : Contract} : Prog C → Prog C
  | [] => []
  | .call _ args _ ret body :: P => Stmt.expandBody args ret (Prog.inlined body) ++ Prog.inlined P
  | s :: P => s :: Prog.inlined P

/-! What the calls run: `addTwo` calls `addOne` twice, `larger` returns from
both branches of its last `if`. -/

/--
info: uint y; uint se1 = 3; uint se2; uint se3 = se1; uint se4; se4 = se3 + 1; se2 = se4; uint se5 = se2; uint se6; se6 = se5 + 1; se2 = se6; y = se2; uint z; uint se7 = y; uint se8 = 7; uint se9; if (se7 > se8) { se9 = se7; } else { se9 = se8; } z = se9;
-/
#guard_msgs in
#eval IO.println (Prog.toStr (Prog.inlined (sol[CallsExample]{ uint y = addTwo(3); uint z = larger(y, 7); })))

/-- error: Solidity elaboration failed: addOne is not a function declared before this one -/
#guard_msgs in #check sol[StandardExample]{ uint y = addOne(1); }

/-- error: Solidity elaboration failed: addOne takes 1 arguments, not 2 -/
#guard_msgs in #check sol[CallsExample]{ uint y = addOne(1, 2); }

/-! ### Friendlier spellings -/

/-- `else if`: the `if`s nested. -/
example : Prog.toStr (sol{ if (total > 2) { total = 1; } else if (total > 1) { total = 2; }
    else if (total > 0) { total = 3; } else { total = 4; } }) =
    "if (total > 2) { total = 1; } else { if (total > 1) { total = 2; } else { \
    if (total > 0) { total = 3; } else { total = 4; } } }" := rfl

/-- A statement ending in a block needs no `;`; one with it reads the same. -/
example : (sol{ if (total > 0) { total = 0; } unchecked { total += 1; } total = 1; } :
    Prog StandardExample) = sol{ if (total > 0) { total = 0; }; unchecked { total += 1; }; total = 1; } :=
  rfl

/-- `address payable` is an `address`, a `uint`. -/
example : Prog.toStr (sol{ address payable a = owner; }) = "uint a = owner;" := rfl

/-- error: Solidity elaboration failed: unknown type Foo -/
#guard_msgs in #check sol{ Foo x; }

/-- A `uint8` is a `uint` whose arithmetic is checked at 8 bits (`narrowPost`);
`Examples/Tactics/Checked.lean` has the rest. -/
example : Prog.toStr (sol{ uint8 x = 250; x += 10; }) =
    "uint x = 250; x += 10; require(x <= 255);" := rfl

/-- error: Solidity elaboration failed: unknown type uint7: the integer types are `uint8` … `uint256` and `int8` … `int256`, in steps of 8 -/
#guard_msgs in #check sol{ uint7 x = 1; }

/-- error: Solidity elaboration failed: total is indexed, but it is a uint, not a mapping or an array -/
#guard_msgs in #check sol{ total[1] = 2; }

/-- error: Solidity elaboration failed: alice: an operand of reference type Person -/
#guard_msgs in #check sol{ total = alice + 1; }

/-- error: Solidity elaboration failed: alice: a storage reference to a Person where a Person[] is expected -/
#guard_msgs in #check sol{ Person[] storage ps = alice; }



end Examples

end Solidity
