import Solidity.Syntax
import Solidity.Tools.Show

/-!
# What the `Tools/` commands share

Two things every command of `Tools/` needs, written once:

* **random states**: `Gen`, Lean core's `StdGen` threaded through
  `StateM`, and `TGen.sval`, a canonical typed storage value of a type
  (`Typing/Reachability.lean`: every struct member in order, a mapping's keys
  unique over the type's default, no shadow).  A `TGen` says how words and
  keys are drawn and how long a mapping or an array gets: `#difftest` draws
  words anywhere in range, `#counterexample` from small pools;
* **the command front end**: what an identifier `C` or `C.f` names
  (`resolveTarget`), a term of type `Except String (List String)` elaborated and run
  (`evalLines`), and a report of a head line and indented lines
  (`logReport`).
-/

namespace Solidity.Tools

open Semantics (structDef lookupBy)

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

/-- `n` at the type `p`, its default out of range: a word a generator
draws in range. -/
def _root_.Solidity.PrimTy.ofIntD (p : PrimTy) (n : Int) : p.Denote :=
  (PrimTy.ofInt? p n).getD (PrimTy.dflt p)

/-- How a random typed storage value is drawn: its words (`prim`), a
mapping's keys (`none`: a mapping of that key type stays empty), and the
bounds on a mapping's entries and a dynamic array's length (drawn below
them). -/
structure TGen where
  prim : (p : PrimTy) → Gen p.Denote
  key : PrimTy → Option (Gen Int)
  entries : Nat := 4
  length : Nat := 3

/-- Exactly `n` values, each drawn by `f`, the first first. -/
def TGen.vec {E : Ty} (f : Gen (SVal E)) : (n : Nat) → Gen (SVec E n)
  | 0 => pure .nil
  | n + 1 => do
    let v ← f
    pure (.cons v (← TGen.vec f n))

/-- A struct's members, in order, each drawn at its type by `f`. -/
def TGen.fields (f : (T : Ty) → Gen (SVal T)) :
    (fs : List (Name × Ty)) → Gen (SFields fs)
  | [] => pure .nil
  | (_, T) :: fs => do
    let v ← f T
    pure (.cons v (← TGen.fields f fs))

/-- A mapping's entries, in the order written. -/
def TGen.smap {V : Ty} : List (Int × SVal V) → SMap V
  | [] => .nil
  | (k, v) :: es => .cons k v (TGen.smap es)

/-- An array of the elements `es` over the shadow `sh`, its type's default
past the bound on a length: what a certificate quotes
(`Tools/Counterexample.lean`'s `quoteFold`), the bound checked by the
kernel. -/
def _root_.Solidity.SVal.arrayOf {E : Ty} {n : Nat} (es : SVec E n) (sh : SList E) :
    SVal (.ref (.array E)) :=
  if h : n < 2 ^ 256 then .array es sh h else SVal.dflt _

/-- **A canonical storage value of type `T`**, at most `k` levels deep (the
default below): every struct member in order, a mapping's keys drawn by
`g.key` (a key drawn twice is drawn once, its value only the first time)
over the type's default, an array of fewer than `g.length` elements and no
shadow. -/
def TGen.sval (g : TGen) : Nat → (T : Ty) → Gen (SVal T)
  | 0, T => pure (SVal.dflt T)
  | _ + 1, .prim p => do pure (.prim (← g.prim p))
  | k + 1, .ref (.mapping (.prim K) V) => do
    let some key := g.key K | return .map .nil (SVal.dflt V)
    let n ← randBelow g.entries
    let mut es : List (Int × SVal V) := []
    for _ in [0:n] do
      let x ← key
      if (es.find? (·.1 == x)).isNone then es := es ++ [(x, ← g.sval k V)]
    pure (.map (TGen.smap es) (SVal.dflt V))
  | _ + 1, .ref (.mapping _ V) => pure (.map .nil (SVal.dflt V))
  | k + 1, .ref (.struct s) => do pure (.struct (← TGen.fields (g.sval k) (structDef s)))
  | k + 1, .ref (.array E) => do
    let n ← randBelow g.length
    pure (SVal.arrayOf (← TGen.vec (g.sval k E) n) .nil)
  | k + 1, .ref (.fixed E n) => do pure (.fixed (← TGen.vec (g.sval k E) n))

/-- A storage: every root of the contract, drawn at its type, in order. -/
def TGen.storage (g : TGen) (C : Contract) : Gen (Storage C) :=
  TGen.fields (g.sval 32) C.vars

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
