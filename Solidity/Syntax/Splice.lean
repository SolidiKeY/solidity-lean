import Solidity.Syntax.Quote

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
declare the same name at another type.

`elabProg`, `elabProgAt` and `ctorProg` are the same block erased to the
statement as written (`Surface.Prog C`, `Prog.erase`), for the readers not
yet moved to the scoped syntax: `sol[C]{ … }` splices it where a
`Surface.Prog C` (or nothing) is expected, the scoped block
(`Prog.quoteShared`) anywhere else.
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
def elabProgAtS.goWt {Γ₀ : Ctx} (i : Nat) : List RawStmt → ECtx × Nat → List Var → Blk C Γ₀ →
    Except (Nat × String) (Blk C Γ₀)
  | [], _, _, acc => pure acc
  | s :: ss, st, ns, acc =>
    match ((elabStmtP C s).run { funs := C.funs }).run st with
    | .error e => .error (i, e)
    | .ok (P, st) =>
      match SProg.chain ns acc.1 P with
      | .error e => .error (i, e)
      | .ok b =>
        match Blk.append acc b with
        | .error e => .error (i, e)
        | .ok acc' => elabProgAtS.goWt (i + 1) ss st (b.2.outNames ns) acc'

/-- `elabProgS`, from the state `st`, an error naming the statement of the
block it arose in (its position, from `i`): the same block, statement by
statement, each typed from the locals the ones before it leave. -/
def elabProgAtS.go (i : Nat) (ss : List RawStmt) (st : ECtx × Nat) :
    Except (Nat × String) (Blk C (ECtx.toNCtx st.1).ctx) := do
  -- a block's locals renamed apart (`freshenBlocks`)
  let ss ← (freshenBlocks (C.vars.map (·.1)) (st.1.map (·.1)) ss).mapError (i, ·)
  elabProgAtS.goWt C i ss st (ECtx.toNCtx st.1).names ⟨_, .nil⟩

/-- `elabProgS`, an error naming the statement of the block it arose in. -/
def elabProgAtS (ss : List RawStmt) : Except (Nat × String) (Blk C []) :=
  elabProgAtS.go C 0 ss ([], RawStmt.maxIdxs ss + 1)

/-- A deployment's program, `constructor(args);`, elaborated (`elabCtor`):
nothing for a contract that declares no constructor and no initializer. -/
def ctorProgS (args : List RawExpr) : Except String (Blk C []) :=
  if C.ctor.isNone && C.inits.isEmpty && args.isEmpty then .ok ⟨[], .nil⟩
  else elabProgS C [.call (.name "constructor") args]

/-- `elabProgS`, as written. -/
def elabProg (ss : List RawStmt) : Except String (Surface.Prog C) :=
  (elabProgS C ss).map (·.2.erase [])

/-- `elabProgAtS.go`, as written. -/
def elabProgAt.go (i : Nat) (ss : List RawStmt) (st : ECtx × Nat) :
    Except (Nat × String) (Surface.Prog C) :=
  (elabProgAtS.go C i ss st).map (·.2.erase (ECtx.toNCtx st.1).names)

/-- `elabProgAtS`, as written. -/
def elabProgAt (ss : List RawStmt) : Except (Nat × String) (Surface.Prog C) :=
  (elabProgAtS C ss).map (·.2.erase [])

/-- `ctorProgS`, as written. -/
def ctorProg (args : List RawExpr) : Except String (Surface.Prog C) :=
  (ctorProgS C args).map (·.2.erase [])

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
/-- Whether a block is spliced as written: where a `Surface.Prog C` (a list)
or nothing is expected. -/
def asWritten (ety? : Option Lean.Expr) : TermElabM Bool := do
  let some ety := ety? | return true
  let ety ← whnfR (← instantiateMVars ety)
  return ety.isMVar || ety.isAppOf ``List

open Lean Elab Term Meta in
@[term_elab solBracket]
def elabSolBracket : TermElab := fun stx ety? => do
  match stx with
  | `(sol[ $c ]{ $[$ss:sol_stmt;]* }) =>
    let raw ← `(sol_raw!{ $[$ss;]* })
    -- an error is reported at the statement it arose in
    let errTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``String)
    let ref ← getRef
    let stmts : Array Syntax := ss.map TSyntax.raw
    let written ← asWritten ety?
    elabAgainstWith (ε := Nat × String) errTy (fun ((i, msg) : Nat × String) =>
        throwErrorAt (stmts[i]?.getD ref) "Solidity elaboration failed: {msg}") c
      fun q => if written then `((elabProgAt $c $raw).map (Surface.Prog.quote $q))
        else `((elabProgAtS $c $raw).map fun b => (Prog.quoteShared $q b.2).1)
  | _ => throwUnsupportedSyntax

macro_rules
  | `(sol{ $[$ss;]* }) => `(sol[InContract.contract]{ $[$ss;]* })

/-! ## Examples -/

section Examples

local instance : InContract := ⟨StandardExample⟩

/-- A block over `StandardExample`: a local, an alias, writes through both,
a mapping entry, a branch on a comparison, a delete, a struct copy into a
mapping, a guard. -/
def tour : Surface.Prog StandardExample := sol{
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
#guard_msgs in #eval IO.println (Surface.Prog.show tour)

/-- A compound target at a non-simple index captures the index first. -/
example : Surface.Prog.toStr (sol{ values[total + 1] += 2; }) =
    "uint ie1 = total + 1; values[ie1] += 2;" := rfl

/-- The captures are numbered past the fresh variables the block writes. -/
example : Surface.Prog.toStr (sol{ uint ie4 = 1; values[total + 1] += 2; }) =
    "uint ie4 = 1; uint ie5 = total + 1; values[ie5] += 2;" := rfl

/-- `lsv = sp.push()` and `T storage lsv = sp.push()`. -/
example : Surface.Prog.toStr (sol{ Person storage p = people.push(); p = persons.push(); }) =
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
example : Surface.Prog.toStr (sol{ uint n = values.length; uint[] memory xs = new uint[](n);
    n = xs.length; }) =
    "uint n = values.length; uint[] memory xs = new uint[](n); n = xs.length;" := rfl

/-- A decrement is spelled `−−` (two U+2212): `--` opens a Lean comment. -/
example : Surface.Prog.toStr (sol{ total−−; −−total; uint y = 0; y = total−−; }) =
    "total−−; −−total; uint y = 0; y = total−−;" := rfl

/-- `++` inside an expression is captured before its statement, into a fresh
local. -/
example : Surface.Prog.toStr (sol{ uint i = 0; values[i++] = 1; }) =
    "uint i = 0; uint se1; se1 = i++; values[se1] = 1;" := rfl

/-- A conditional of references binds a fresh alias, declared before the branches. -/
example : Surface.Prog.toStr (sol{ bool c = true; Person storage p = c ? alice : bob; }) =
    "bool c = true; Person storage sp1; if (c) { sp1 = alice; } else { sp1 = bob; } \
    Person storage p = sp1;" := rfl

/-- A memory one declares its `mv1` before the branches, bound to a branch
that indexes nothing, and rebinds it in each: the branches are scopes. -/
example : Surface.Prog.toStr (sol{ bool c = true; Person memory mx = alice; Person memory my = bob;
    Person memory m = c ? mx : my; }) =
    "bool c = true; Person memory mx = alice; Person memory my = bob; \
    Person memory mv1 = mx; if (c) { mv1 = mx; } else { mv1 = my; } \
    Person memory m = mv1;" := rfl

/-- Both indexing, it is bound to a fresh default object first. -/
example : Surface.Prog.toStr (sol{ bool c = true; Person[] memory xs = new Person[](2);
    Person memory m = c ? xs[0] : xs[1]; }) =
    "bool c = true; Person[] memory xs = new Person[](2); Person memory mv1; \
    if (c) { mv1 = xs[0]; } else { mv1 = xs[1]; } Person memory m = mv1;" := rfl

/-- The error of a check, if any. -/
private def checkErr (P : Surface.Prog StandardExample) : String :=
  match Prog.resolveCheck [] P with
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
example : Surface.Prog.toStr (sol{ uint t = 0; if (t > 0) { bool y = true; } else { }
    if (t > 1) { uint y = 1; } else { } }) =
    "uint t = 0; if (t > 0) { bool y = true; } else { } if (t > 1) { uint y = 1; } else { }" := rfl

-- An increment under `&&` is evaluated only when the left operand does not
-- decide, so it cannot be captured before the statement.
/-- error: Solidity elaboration failed: `++` or `−−` under a short-circuit operator -/
#guard_msgs in #check sol{ bool c = true; uint i = 0; c = c && i++ > 0; }

/-- A negative literal takes the type it stands at. -/
example : (sol{ int e = -5; } : Surface.Prog StandardExample) =
    [.declLocal .int (.user "e") (some (.simple (.lit (-5) rfl)))] := rfl

/-- info: int e = -5; -/
#guard_msgs in #eval IO.println (Surface.Prog.show (sol{ int e = -5; } : Surface.Prog StandardExample))

/-- A constant expression is folded as solc folds it: an operand out of
range whose result is in range is accepted (`BinOp.foldLit?`). -/
example : (sol{ uint x = 115792089237316195423570985008687907853269984665640564039457584007913129639936 - 1;
    int y = 57896044618658097711785492504343953926634992332820282019728792003956564819968 - 1; } :
    Surface.Prog StandardExample) =
    [.declLocal .uint (.user "x") (some (.simple (.lit 115792089237316195423570985008687907853269984665640564039457584007913129639935 rfl))),
     .declLocal .int (.user "y") (some (.simple (.lit 57896044618658097711785492504343953926634992332820282019728792003956564819967 rfl)))] := rfl

-- One whose result is out of range is refused.
/-- error: Solidity elaboration failed: the literal 115792089237316195423570985008687907853269984665640564039457584007913129639936 is out of the range of uint -/
#guard_msgs in #check (sol{ uint x = 115792089237316195423570985008687907853269984665640564039457584007913129639936 + 1; } : Surface.Prog StandardExample)

/-- `delete` in memory, and a fresh array written to a location. -/
example : Surface.Prog.toStr (sol[TestSuite]{ Person memory m; delete m.age; delete m;
    basketA.items = new uint[](2); }) =
    "Person memory m; delete m.age; delete m; basketA.items = new uint[](2);" := rfl

/-- A call is its body inlined, every local of the callee fresh. -/
example : Surface.Prog.toStr (C := CallsExample) (sol[CallsExample]{ uint y = addTwo(3); credit(y, 2); bump(); }) =
    "uint y; y = addTwo(3); credit(y, 2); bump();" := rfl

/-- Each call of a block replaced by its inlined body, for display. -/
partial def Surface.Prog.inlined {C : Contract} : Surface.Prog C → Surface.Prog C
  | [] => []
  | .call _ args _ ret body :: P => Surface.Stmt.expandBody args ret (Surface.Prog.inlined body) ++ Surface.Prog.inlined P
  | s :: P => s :: Surface.Prog.inlined P

/-! What the calls run: `addTwo` calls `addOne` twice, `larger` returns from
both branches of its last `if`. -/

/--
info: uint y; uint se1 = 3; uint se2; uint se3 = se1; uint se4; se4 = se3 + 1; se2 = se4; uint se5 = se2; uint se6; se6 = se5 + 1; se2 = se6; y = se2; uint z; uint se7 = y; uint se8 = 7; uint se9; if (se7 > se8) { se9 = se7; } else { se9 = se8; } z = se9;
-/
#guard_msgs in
#eval IO.println (Surface.Prog.toStr (Surface.Prog.inlined (sol[CallsExample]{ uint y = addTwo(3); uint z = larger(y, 7); })))

/-- error: Solidity elaboration failed: addOne is not a function declared before this one -/
#guard_msgs in #check sol[StandardExample]{ uint y = addOne(1); }

/-- error: Solidity elaboration failed: addOne takes 1 arguments, not 2 -/
#guard_msgs in #check sol[CallsExample]{ uint y = addOne(1, 2); }

/-! ### Friendlier spellings -/

/-- `else if`: the `if`s nested. -/
example : Surface.Prog.toStr (sol{ if (total > 2) { total = 1; } else if (total > 1) { total = 2; }
    else if (total > 0) { total = 3; } else { total = 4; } }) =
    "if (total > 2) { total = 1; } else { if (total > 1) { total = 2; } else { \
    if (total > 0) { total = 3; } else { total = 4; } } }" := rfl

/-- A statement ending in a block needs no `;`; one with it reads the same. -/
example : (sol{ if (total > 0) { total = 0; } unchecked { total += 1; } total = 1; } :
    Surface.Prog StandardExample) = sol{ if (total > 0) { total = 0; }; unchecked { total += 1; }; total = 1; } :=
  rfl

/-- `address payable` is an `address`, a `uint`. -/
example : Surface.Prog.toStr (sol{ address payable a = owner; }) = "uint a = owner;" := rfl

/-- error: Solidity elaboration failed: unknown type Foo -/
#guard_msgs in #check sol{ Foo x; }

-- A struct that repeats a member name is refused, as solc refuses its
-- declaration ("Identifier already declared", `refusedStructs`, decision 16).
/-- error: Solidity elaboration failed: struct BadDup: identifier already declared: member a -/
#guard_msgs in #check sol{ BadDup memory x; }

/-- A `uint8` is a `uint` whose arithmetic is checked at 8 bits (`narrowPost`);
`Examples/Tactics/Checked.lean` has the rest. -/
example : Surface.Prog.toStr (sol{ uint8 x = 250; x += 10; }) =
    "uint x = 250; x += 10; require(x <= 255);" := rfl

/-- error: Solidity elaboration failed: unknown type uint7: the integer types are `uint8` … `uint256` and `int8` … `int256`, in steps of 8 -/
#guard_msgs in #check sol{ uint7 x = 1; }

/-- error: Solidity elaboration failed: total is indexed, but it is a uint, not a mapping or an array -/
#guard_msgs in #check sol{ total[1] = 2; }

/-- error: Solidity elaboration failed: alice: an operand of reference type Person -/
#guard_msgs in #check sol{ total = alice + 1; }

/-- error: Solidity elaboration failed: alice: a storage reference to a Person where a Person[] is expected -/
#guard_msgs in #check sol{ Person[] storage ps = alice; }




/-! ### Scoped

`sol{ … }` at a scoped type is the block typed in place (`elabProgS`), the
one `resolve` makes of the block as written: `tour` and a block of calls,
declared from their erasure resolved (`Prog.defineCore`), are the kernel's
and the same terms, and each erases back to the block as written. -/

section Pins

private def callsBlock : Solidity.Surface.Prog CallsExample :=
  sol[CallsExample]{ uint y = addTwo(3); uint z = larger(y, 7); }

open Lean Elab Command in
run_cmd liftCoreM do
  for (n, cn, err) in [(`Solidity.tourCore, ``StandardExample,
        ← Prog.defineCore `Solidity.tourCore ``StandardExample [] tour),
      (`Solidity.callsCore, ``CallsExample,
        ← Prog.defineCore `Solidity.callsCore ``CallsExample [] callsBlock)] do
    if let some e := err then throwError "{n} ({cn}): {e}"

example : Prog.erase [] tourCore = tour := rfl
example : Prog.erase [] callsCore = callsBlock := rfl

example : (sol{
  uint x = alice.age + 1;
  Person storage p = alice;
  p.age = x;
  balances[x] = 10;
  if (x > 3) { alice.age = 0; } else { revert(); };
  delete bob.account;
  folks[1] = bob;
  require(flags[x] || x == 2);
} : Prog StandardExample [] _) = tourCore := rfl

example : (sol[CallsExample]{ uint y = addTwo(3); uint z = larger(y, 7); } :
    Prog CallsExample [] _) = callsCore := rfl

/--
info: uint y;
y = addTwo(3);
uint z;
z = larger(y, 7);
-/
#guard_msgs in
#eval IO.println (Prog.show [] (sol[CallsExample]{ uint y = addTwo(3); uint z = larger(y, 7); } :
  Prog CallsExample [] _))

end Pins

end Examples

end Solidity
