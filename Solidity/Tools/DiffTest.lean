import Solidity.Evm.Compile
import Solidity.Typing.Storage
import Solidity.Tools.Run

/-!
# `#difftest`: the interpreter against the compiled code, on random states

```
#difftest CallsExample (runs := 50) (seed := 1)
#difftest CallsExample.credit (runs := 200)
```

For each function of the contract (or the one function named), `runs`
times: draw a well-typed storage, arguments and a transaction, call the
function in the interpreter (`Prog.run`) and run its compiled code on the
machine (`Evm.run`, `compileProg`) from the storage laid out as solc lays it
out, and compare.

**What is compared is what `compile_correct` claims** (`Evm/Correctness.lean`),
from a start where its hypotheses hold:

* the call is the program `#run` builds (`callProg`), kept only if it is in
  the compiled fragment, `wtProg (fun _ => none) P = some Γ'`; otherwise the
  function is reported skipped;
* the start machine represents the start state (`Sim C L (fun _ => none) σ m`):
  its storage is the storage encoded (`SVal.encode`, which is `ReprAt` read
  as a function), every other slot `0`, which is how a mapping's absent keys
  represent its default; no locals; the funds, the sender, the value and the
  time are words and the same on both sides; nothing sent.  The storages
  drawn are canonical (`Typing/Reachability.lean`: no shadow, a mapping's
  default `defaultForTy V`, distinct keys), in range, and checked with
  `SVal.hasTy`; an array holds fewer than `4` elements, so `L = 4` and
  `L + pushesP P ≤ 2^64`;
* the two **agree** when both revert, or when both succeed with the machine's
  stack as it was and the machine representing the final state: every slot
  the final storage occupies holds its word (`ReprStore`, for the mapping keys
  either storage mentions: the keys of a mapping entry nobody wrote are `0`
  on both sides by construction); every value local the final context types
  (`Γ'`) holds the local's word in its memory cell (`Sim.vals`: the value
  returned, in `_r`, among them); the ledger is the money that moved
  (`Sim.net`), at every address the ledger holds, the contract's own
  included, the contract at an address drawn among the senders, so some
  payments are to itself.  The
  aliases' cells (`Sim.aliases`) are not compared, and neither are the slots
  the final storage no longer occupies (a popped element), which
  `ReprStore` leaves free.

The machine reverting where the interpreter succeeds agrees only in code
that pays (`paysP`): the world refused a payment, which the draw makes
happen, the contract's account holding less than `100` and the recipient
`3` refusing every payment.  A stuck interpreter or a faulting machine is a
disagreement: on the fragment, `compile_correct` excludes both.

The generator is `GenSpec.sval` (`Tools/Common.lean`) over Lean core's
`StdGen`.  Run `i` of the `j`-th function draws from a seed of its own,
`runSeed seed j i`, whatever other function is tested, so a mismatch prints
the command that replays it: `#difftest C.f (runs := i + 1) (seed := s)`,
whose last run is the one that failed.
-/

namespace Solidity.Tools

open Semantics Evm

/-! ## The layout, as a function -/

/-- The mapping keys a value holds anywhere, as words. -/
partial def SVal.mapKeys : SVal → List Nat
  | .prim _ => []
  | .struct fs => fs.flatMap (SVal.mapKeys ·.2)
  | .array es sh _ => (es ++ sh).flatMap SVal.mapKeys
  | .map es d =>
    (es.filterMap fun (k, _) => if 0 ≤ k ∧ k < (W : Int) then some k.toNat else none) ++
      (es.flatMap (SVal.mapKeys ·.2)) ++ SVal.mapKeys d

/-- The slots the value `v` of type `T` occupies from slot `s`, with their
words: `ReprAt` constructor by constructor.  A `uint` its number, a `bool`
`bword b`, an `int` its two's complement word; a struct its members from
`s.add (offset n f)`; a dynamic array its length at `s` and element `i` from
`.data s (i · size E)`; a fixed-size one element `i` from `s.add (i · size E)`;
a `uint`-keyed mapping entry `k` from `.hash k s 0`, for the keys `keys` and
its own (an entry of another key type takes no slot the fragment reads, as
`ReprAt.mapOther` says).  An error is a value no machine storage represents:
out of range, of another type, or a struct short of a member. -/
partial def SVal.encode (keys : List Nat) : Ty → Slot → SVal → Except String (List (Slot × Nat))
  | .prim .uint, s, .prim (.int n) =>
    if 0 ≤ n ∧ n < (W : Int) then pure [(s, n.toNat)] else throw s!"uint {n} out of range"
  | .prim .bool, s, .prim (.bool b) => pure [(s, bword b)]
  | .prim .int, s, .prim (.int n) =>
    if -(H : Int) ≤ n ∧ n < (H : Int) then pure [(s, toWord n)] else throw s!"int {n} out of range"
  | .ref (.struct n), s, .struct fs =>
    (structDef n).flatMapM fun (f, T) => do
      let some v := lookupBy f fs | throw s!"{n} without its member {f}"
      SVal.encode keys T (s.add (offset n f)) v
  | .ref (.array E), s, .array es _ false => do
    let elems ← (List.range es.length).zip es |>.flatMapM fun (i, v) =>
      SVal.encode keys E (.data s (i * size E)) v
    pure ((s, es.length) :: elems)
  | .ref (.fixed E n), s, .array es _ true => do
    unless es.length = n do throw s!"a {n}-element array with {es.length}"
    (List.range es.length).zip es |>.flatMapM fun (i, v) =>
      SVal.encode keys E (s.add (i * size E)) v
  | .ref (.mapping (.prim .uint) V), s, .map es d =>
    let own := es.filterMap fun (k, _) => if 0 ≤ k ∧ k < (W : Int) then some k.toNat else none
    (own ++ keys).eraseDups.flatMapM fun k =>
      SVal.encode keys V (.hash k s 0) ((lookupBy (k : Int) es).getD d)
  | .ref (.mapping _ _), _, _ => pure []
  | T, _, v => throw s!"{SVal.fmt T v} is no {Ty.toStr T}"

/-- The whole storage laid out: every root of the contract at `rootSlot`. -/
def encodeStorage (C : Contract) (keys : List Nat) (st : List (Name × SVal)) :
    Except String (List (Slot × Nat)) :=
  C.vars.flatMapM fun (r, T) => do
    let some v := lookupBy r st | throw s!"no root {r}"
    SVal.encode keys T (rootSlot C r) v

/-- A machine storage holding the words listed, `0` elsewhere. -/
def storeOf (ws : List (Slot × Nat)) : Slot → Nat := fun s => (lookupBy s ws).getD 0

/-- The word a value local's cell holds: `ReprV` read as a function. -/
def wordOf : PrimTy → Value → Option Word
  | .uint, .int n => if 0 ≤ n ∧ n < (W : Int) then some (.val n.toNat) else none
  | .bool, .bool b => some (.val (bword b))
  | .int, .int n => if -(H : Int) ≤ n ∧ n < (H : Int) then some (.val (toWord n)) else none
  | _, _ => none

/-! ## Random well-typed values -/

/-- A `uint`: mostly small, so that guards go both ways, sometimes at the
edges of the word (`0`, `2^256 - 1`, `2^255`), sometimes anywhere. -/
def genUint : Gen Nat := do
  let c ← randBelow 10
  if c < 7 then randBelow 8
  else if c < 9 then pure [0, W - 1, W - 2, H][← randBelow 4]!
  else randBelow W

/-- An `int` in `[-2^255, 2^255)`: mostly small, sometimes at the edges. -/
def genInt : Gen Int := do
  let c ← randBelow 10
  if c < 7 then pure (((← randBelow 11 : Nat) : Int) - 5)
  else if c < 9 then pure [-(H : Int), (H : Int) - 1, -1, 0][← randBelow 4]!
  else pure (((← randBelow W : Nat) : Int) - H)

/-- A `bool`. -/
def genBool : Gen Bool := do pure ((← randBelow 2) == 1)

/-- How `#difftest` draws a storage: words by `genUint`, `genInt`,
`genBool`; up to `3` entries of a `uint`-keyed mapping (none for another key
type, which takes no slot the compiled code reads), a few small keys, so
that two entries or two reads can meet, and the largest word; arrays of
fewer than `4` elements. -/
def diffGen : GenSpec where
  prim
    | .uint => do pure (.int (← genUint))
    | .int => do pure (.int (← genInt))
    | .bool => do pure (.bool (← genBool))
  key
    | .uint => some do
      if (← randBelow 8) < 7 then pure ((← randBelow 4 : Nat) : Int) else pure (W - 1 : Nat)
    | _ => none
  entries := 4
  length := 4

/-- An argument as a literal: `5`, `-5`, `true`.  An `int` argument is kept
off `-2^255`, which no literal spells (`-x` of `2^255` is out of range). -/
def genArg : Ty → Gen (Option (RawExpr × Value))
  | .prim .uint => do let n ← genUint; pure (some (.num n, .int n))
  | .prim .bool => do let b ← genBool; pure (some (.bool b, .bool b))
  | .prim .int => do
    let n ← genInt
    let n := if n = -(H : Int) then n + 1 else n
    pure (some (if n < 0 then .unop .neg (.num n.natAbs) else .num n.toNat, .int n))
  | _ => pure none

/-! ## One run -/

/-- What a run starts from. -/
structure Start where
  storage : List (Name × SVal)
  args : List Value
  sender : Nat
  value : Nat
  time : Nat
  /-- The contract's account. -/
  balance : Nat
  /-- The contract's address. -/
  self : Nat

/-- The interpreter's start state. -/
def Start.state (s : Start) : State where
  storage := s.storage
  selfBalance := s.balance
  tx := { msgSender := s.sender, msgValue := s.value, timestamp := s.time, selfAddress := s.self }

/-- The start of a run, drawn: the storage, the arguments and the
transaction; `none` if a parameter has no value type. -/
def genStart (C : Contract) (d : FunDecl) : Gen (Option (Start × List RawExpr)) := do
  let st ← diffGen.storage C
  let args ← d.params.mapM fun (_, T) => genArg T
  let sender ← randBelow 4
  let value ← randBelow 3
  let time ← randBelow 100
  let balance ← randBelow 100
  let self ← randBelow 4
  pure <| (args.mapM id).map fun args =>
    ({ storage := st, args := args.map (·.2), sender, value, time, balance, self }, args.map (·.1))

/-- A run's outcome, for the report. -/
def fmtRes : Res State → String
  | .ok _ => "ok"
  | .error h => fmtHalt h

/-- A machine run's outcome, for the report. -/
def fmtOut : Out → String
  | .ok _ 0 => "ok"
  | .ok _ k => s!"ok with {k} instructions still to skip"
  | .revert => "revert"
  | .fault => "fault"

/-- Where the final machine fails to represent the final state, one line
each; empty when it does. -/
def differences [FreshNames] (C : Contract) (Γ' : TyCtx) (keys : List Nat) (σ' : State)
    (m' : Machine) : List String :=
  let store := match encodeStorage C keys σ'.storage with
    | .error e => [s!"storage: the interpreter's final storage is not representable: {e}"]
    | .ok ws => ws.filterMap fun (s, w) =>
      if m'.store s == w then none else some s!"slot {s}: interpreter {w}, machine {m'.store s}"
  let vals := σ'.env.filterMap fun (x, b) => match Γ' x, b with
    | some (.val p), .val v =>
      if wordOf p v == some (m'.mem x) then none
      else some s!"local {x}: interpreter {Value.fmt v}, machine {m'.mem x}"
    | _, _ => none
  let net := σ'.net.filterMap fun (a, n) =>
    if 0 ≤ a ∧ a < (W : Int) ∧ n != (m'.bal₀ a.toNat : Int) - m'.bal a.toNat then
      some s!"net {a}: interpreter {n}, account {m'.bal₀ a.toNat} → {m'.bal a.toNat}"
    else none
  let stack := if m'.stack.isEmpty then [] else [s!"stack left: {m'.stack}"]
  store ++ vals ++ net ++ stack

/-- One run of `P` from `s`: whether both reverted when the two agree, else
the lines of the mismatch. -/
def runOnce [FreshNames] (C : Contract) (P : Prog C) (Γ' : TyCtx) (s : Start) :
    Except (List String) Bool :=
  let σ := s.state
  let keys0 := s.storage.flatMap (SVal.mapKeys ·.2)
  match encodeStorage C keys0 s.storage with
  | .error e => throw [s!"the start storage is not representable: {e}"]
  | .ok ws =>
    let m : Machine :=
      { Machine.init (fun a => if a = s.self then s.balance else 0) s.self with
        accepts := fun a _ => a != 3
        store := storeOf ws
        caller := s.sender
        callvalue := s.value
        timestamp := s.time }
    let res := Prog.run σ P
    let out := Evm.run (compileProg P) m
    match res, out with
    | .error .revert, .revert => pure true
    | .ok _, .revert => if paysP P then pure true
      else throw ["interpreter ok, machine revert, and no payment to refuse"]
    | .ok σ', .ok m' 0 =>
      let keys := (keys0 ++ σ'.storage.flatMap (SVal.mapKeys ·.2)).eraseDups
      match differences C Γ' keys σ' m' with
      | [] => pure false
      | ds => throw (s!"both ok, and they differ:" :: ds)
    | _, _ => throw [s!"interpreter {fmtRes res}, machine {fmtOut out}"]

/-! ## The test -/

/-- The seed of run `i` of the `j`-th function, from the test's seed. -/
def runSeed (seed j i : Nat) : Nat := seed * 1000003 + j * 10007 + i

/-- `runs` runs of function `f`, the `j`-th of the contract `name`: its
report line, or the mismatch's lines, the first the command that replays
it. -/
def testFun [FreshNames] (C : Contract) (name : String) (runs seed j : Nat) (f : Name)
    (d : FunDecl) : List String := Id.run do
  let mut agreed := 0
  let mut reverted := 0
  for i in List.range runs do
    let some (s, args) := (genStart C d).run' (mkStdGen (runSeed seed j i))
      | return [s!"skipped: {f} (a parameter of reference type)"]
    let P ← match callProg C f args with
      | .ok P => pure P
      | .error e => return [s!"skipped: {f} ({e})"]
    let some Γ' := wtProg (fun _ => none) P
      | return [s!"skipped: {f} (outside the compiled fragment)"]
    unless pushesP P + 4 ≤ Lmax do return [s!"skipped: {f} (too many pushes)"]
    match runOnce C P Γ' s with
    | .ok rev =>
      agreed := agreed + 1
      if rev then reverted := reverted + 1
    | .error ds =>
      let args := (d.params.zip s.args).map fun ((x, _), v) => s!"{x} = {Value.fmt v}"
      return [s!"{f}: MISMATCH at run {i}, replayed by",
        s!"  #difftest {name}.{f} (runs := {i + 1}) (seed := {seed})",
        "  " ++ ", ".intercalate (args ++ fmtTx s.state),
        "  before: " ++ fmtStorageLine C s.storage] ++
        ds.map ("  " ++ ·)
  let agree := if agreed = 1 then "run agrees" else "runs agree"
  return [s!"{f}: {agreed} {agree} ({reverted} revert)"]

/-- The report of `#difftest`: one line per function (the function `only`,
if given), or a mismatch.  `name` is the contract as the command names
it. -/
def diffTest [FreshNames] (C : Contract) (name : String) (only : Option String)
    (runs seed : Nat) : Except String (List String) :=
  pure <| (C.funs.zip (List.range C.funs.length)).flatMap fun ((f, d), j) =>
    if only.all (· == f) then testFun C name runs seed j f d else []

/-- `#difftest C (runs := n) (seed := s)`: compare the interpreter with the
compiled code on `n` random calls of each function of `C` (default `50`
runs, seed `0`); `#difftest C.f …`: of the function `f` alone. -/
syntax (name := difftestCmd) "#difftest " ident ("(" &"runs" " := " num ")")?
  ("(" &"seed" " := " num ")")? : command

open Lean Elab Command Term Meta in
@[command_elab difftestCmd] def elabDiffTest : CommandElab
  | `(#difftest $id:ident $[( runs := $n?)]? $[( seed := $s?)]?) => liftTermElabM do
    let n := (n?.map (·.getNat)).getD 50
    let s := (s?.map (·.getNat)).getD 0
    let (c, name, only) ← match ← resolveTarget "#difftest" id.getId with
      | .contract c _ => pure (c, id.getId, (none : Option String))
      | .function c _ f => pure (c, id.getId.getPrefix, some f)
    let only ← match only with
      | some f => `(some $(quote f))
      | none => `(none)
    let t ← `(diffTest $(mkCIdent c) $(quote name.toString) $only $(quote n) $(quote s))
    logInfo (String.intercalate "\n" (← evalLines "#difftest" t))
  | _ => throwUnsupportedSyntax

end Solidity.Tools
