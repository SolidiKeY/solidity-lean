import Solidity.Update
import Solidity.Tools.Show

/-!
# What the `Tools/` commands share

Two things every command of `Tools/` needs, written once:

* **random states**: `Gen`, Lean core's `StdGen` threaded through
  `StateM`, and `GenSpec.sval`, a canonical storage value of a type
  (`Typing/Reachability.lean`: every struct member in order, a mapping's keys
  unique and its default `defaultForTy V`, no shadow).  A `GenSpec` says how
  words and keys are drawn and how long a mapping or an array gets:
  `#difftest` draws words anywhere in range, `#counterexample` from pools of
  interesting values;
* **the command front end**: what an identifier `C` or `C.f` names
  (`resolveTarget`), a closed formula of a named contract (`elabFormula`),
  a term of type `Except String (List String)` elaborated and run
  (`evalLines`), and a report of a head line and indented lines
  (`logReport`).
-/

namespace Solidity.Tools

open Semantics

/-! ## Random values -/

/-- A generator: Lean core's `StdGen`, threaded. -/
abbrev Gen := StateM StdGen

/-- A number below `n` (`0` for `n = 0`, drawing nothing). -/
def randBelow (n : Nat) : Gen Nat := do
  if n = 0 then return 0
  let (i, g) := randNat (← get) 0 (n - 1)
  set g
  pure i

/-- An element of `xs`, `d` if there is none. -/
def pickD {α : Type} (d : α) (xs : List α) : Gen α := do
  pure (xs.getD (← randBelow xs.length) d)

instance : Inhabited SVal := ⟨.prim (.int 0)⟩

/-- How a random storage value is drawn: its words (`prim`), a mapping's
keys (`none`: a mapping of that key type stays empty), and the bounds on a
mapping's entries and a dynamic array's length (drawn below them). -/
structure GenSpec where
  prim : PrimTy → Gen Value
  key : PrimTy → Option (Gen Int)
  entries : Nat
  length : Nat

/-- **A canonical storage value of type `T`**: every struct member in
order, a mapping's keys unique (a key drawn twice is drawn once; its value
is drawn only the first time) over the default `defaultForTy V`, an array
without recycled slots. -/
partial def GenSpec.sval (g : GenSpec) : Ty → Gen SVal
  | .prim p => do pure (.prim (← g.prim p))
  | .ref (.mapping (.prim K) V) => do
    let some key := g.key K | pure (.map [] (defaultForTy V))
    let n ← randBelow g.entries
    let mut es : List (Int × SVal) := []
    for _ in [0:n] do
      let k ← key
      if (es.find? (·.1 == k)).isNone then es := es ++ [(k, ← g.sval V)]
    pure (.map es (defaultForTy V))
  | .ref (.mapping _ V) => pure (.map [] (defaultForTy V))
  | .ref (.struct s) => do
    pure (.struct (← (structDef s).mapM fun (f, T) => do pure (f, ← g.sval T)))
  | .ref (.array E) => do
    let n ← randBelow g.length
    pure (.array (← (List.range n).mapM fun _ => g.sval E) [] false)
  | .ref (.fixed E n) => do
    pure (.array (← (List.range n).mapM fun _ => g.sval E) [] true)

/-- A storage: every root of the contract, drawn at its type, in order. -/
def GenSpec.storage (g : GenSpec) (C : Contract) : Gen (List (Name × SVal)) :=
  C.vars.mapM fun (r, T) => do pure (r, ← g.sval T)

/-- Whether `f` has an obligation: a clause of its own or an invariant of
the contract, and no `skip`. -/
def hasObligation (C : Contract) (d : FunDecl) : Bool :=
  !d.spec.skip && (!d.spec.requires.isEmpty || !d.spec.ensures.isEmpty ||
    d.spec.assignable.isSome || !C.inv.isEmpty)

/-! ## The command front end -/

open Lean Elab Term Meta

/-- What a command's identifier names: a contract, or a function of one.
`c` is the contract's constant, `C` its value. -/
inductive Target where
  | contract (c : Lean.Name) (C : Contract)
  | function (c : Lean.Name) (C : Contract) (f : String)

/-- The constant of type `Contract` an identifier names, if it names one. -/
def contractConst? (id : Lean.Name) : TermElabM (Option Lean.Name) := do
  let some c ← (try some <$> realizeGlobalConstNoOverload (mkIdent id) catch _ => pure none)
    | return none
  return if (← getConstInfo c).type == Lean.mkConst ``Contract then some c else none

/-- **What `id` names**, for the command `cmd`: the contract `C`, or its
function `C.f`; `none` if it names neither.  A `C.f` whose `f` is not a
function of `C` is an error, unless `C.f` is a declaration of its own. -/
def resolveTarget? (cmd : String) (id : Lean.Name) : TermElabM (Option Target) := do
  if let some c ← contractConst? id then
    return some (.contract c (← unsafe evalConst Contract c))
  let .str pre f := id | return none
  let some c ← contractConst? pre | return none
  let C ← unsafe evalConst Contract c
  if (lookupBy f C.funs).isSome then return some (.function c C f)
  if (← try some <$> realizeGlobalConstNoOverload (mkIdent id) catch _ => pure none).isSome then
    return none
  let fs := C.funs.map (·.1)
  let has := if fs.isEmpty then "none" else ", ".intercalate fs
  throwError "{cmd}: {f} is not a function of {pre}; it has {has}"

/-- What `id` names, which must be a contract or a function of one. -/
def resolveTarget (cmd : String) (id : Lean.Name) : TermElabM Target := do
  let some t ← resolveTarget? cmd id
    | throwError "{cmd}: {id} is not a contract `C` or a function `C.f`"
  pure t

/-- What `id` names, which must be a function of a contract. -/
def resolveFunction (cmd : String) (id : Lean.Name) :
    TermElabM (Lean.Name × Contract × String) := do
  match ← resolveTarget cmd id with
  | .function c C f => pure (c, C, f)
  | .contract .. => throwError "{cmd}: expected a function `{id}.f`, not the contract {id}"

/-- **Elaborate a closed formula of a named contract**: the formula, the
contract, and the contract's name quoted (`Lean.mkConst n []`). -/
def elabFormula (cmd : String) (t : Lean.Term) :
    TermElabM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let φ ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  let ty ← whnf (← inferType φ)
  unless ty.isAppOfArity ``Fml 1 do throwError "{cmd}: not a formula{indentExpr φ}"
  let C := ty.appArg!
  let some n := (← whnfR C).constName? | throwError "{cmd}: not a named contract: {C}"
  if φ.hasFVar || φ.hasMVar then throwError "{cmd}: the formula is not closed{indentExpr φ}"
  let c := mkApp2 (mkConst ``Lean.mkConst) (toExpr n)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Lean.Level))
  return (φ, C, c)

/-- **Run a report**: elaborate `t : Except String (List String)`, evaluate
it, and return its lines, or fail with its message. -/
def evalLines (cmd : String) (t : Lean.Term) : TermElabM (List String) := do
  let ty ← mkAppM ``Except #[mkConst ``String, ← mkAppM ``List #[mkConst ``String]]
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  match ← unsafe evalExpr (Except String (List String)) ty e with
  | .ok lines => pure lines
  | .error msg => throwError "{cmd}: {msg}"

/-- A report: its head line, then one indented line each. -/
def reportMsg (head : MessageData) (lines : List MessageData) : MessageData :=
  head ++ MessageData.joinSep (lines.map (m!"\n  " ++ ·)) m!""

/-- Log a report: its head line, then one indented line each. -/
def logReport (head : MessageData) (lines : List MessageData) : CoreM Unit :=
  logInfo (reportMsg head lines)

end Solidity.Tools
