import Solidity.Evm.Compile
import Solidity.Semantics.Run
import Solidity.Tools.Run

/-!
# `#difftest`: the typed run against the compiled code, on random states

```
#difftest CallsExample (runs := 50) (seed := 1)
#difftest CallsExample.credit (runs := 200)
```

For each function of the contract (or the one function named), `runs`
times: draw a well-typed storage, arguments and a transaction, call the
function in the typed run (`Prog.run`, `Semantics/Run.lean`)
and run its compiled code on the machine (`Evm.run`, `Evm.compileProg`)
from the storage laid out as solc lays it out, and compare.

**What is compared is what `compile_correct` claims** (`Evm/Correct.lean`),
from a start where its hypotheses hold:

* the call is the program `#run` builds (`callProg`, elaborated scoped),
  and kept only if it is in the compiled
  fragment, `inFragP (Frag.init []) Q = some F'`; otherwise the function is
  reported skipped;
* the start machine represents the start state (`Sim C L b F σ m`): its
  storage is the typed storage encoded (`encodeFold`, which is `ReprAt`
  read as a function), every other slot `0`, which is how a mapping's absent
  keys represent its default; no locals; the funds, the sender, the value
  and the time are words and the same on both sides; nothing sent.  The
  storages drawn are typed (`TGen.sval`, `Tools/Common.lean`) and canonical
  (`Typing/Reachability.lean`: no shadow, a mapping's default the type's,
  distinct keys); an array holds fewer than `4` elements, so `L = 4` and
  `L + Prog.pushes Q ≤ 2^64`;
* the two **agree** when both revert, or when both succeed with the machine's
  stack as it was and the machine representing the final state: every slot
  the final storage occupies holds its word (`ReprStore`, for the mapping keys
  either storage mentions: the keys of a mapping entry nobody wrote are `0`
  on both sides by construction); every value local of the final context
  holds the local's word in the memory cell of its level (`Sim.vals`: the
  value returned, in `_r`, among them); the ledger is the money that moved
  (`Sim.net`), at every address the ledger holds but the contract's own,
  whose entry is `0` (`Sim.netSelf`), the contract at an address drawn
  among the senders, so some payments are to itself.  The aliases' cells
  (`Sim.aliases`) are not compared, and neither are the slots the final
  storage no longer occupies (a popped element), which `ReprStore` leaves
  free.

The machine reverting where the typed run succeeds agrees only in code that
pays (`Prog.pays`): the world refused a payment, which the draw makes
happen, the contract's account holding less than `100` and the recipient
`3` refusing every payment.  A diverging typed run or a faulting machine is
a disagreement: on the fragment, `compile_correct` excludes both.

The generator is `TGen.sval` (`Tools/Common.lean`) over Lean core's
`StdGen`.  Run `i` of the `j`-th function draws from a seed of its own,
`runSeed seed j i`, whatever other function is tested, so a mismatch prints
the command that replays it: `#difftest C.f (runs := i + 1) (seed := s)`,
whose last run is the one that failed.
-/

namespace Solidity.Tools

open Evm
open Semantics (lookupBy)

/-! ## The layout, as a function -/

/-- The mapping keys a value holds anywhere, as words: a mapping's own keys
in range, then its values', then its default's; an array's shadow
included. -/
def mapKeysFold : Fold where
  V _ := List Nat
  F _ := List Nat
  L _ := List Nat
  W _ _ := List Nat
  M _ _ := List Nat × List Nat
  prim _ := []
  struct _ r := r
  array _ _ _ w l := w ++ l
  fixed _ w := w
  map _ _ m d := m.1 ++ m.2 ++ d
  fnil := []
  fcons _ _ v r := v ++ r
  lnil := []
  lcons _ _ v r := v ++ r
  wnil := []
  wcons _ _ v r := v ++ r
  mnil := ([], [])
  mcons k _ _ v r :=
    let k := PrimTy.key k
    ((if 0 ≤ k ∧ k < (W : Int) then [k.toNat] else []) ++ r.1, v ++ r.2)

/-- The mapping keys a storage holds anywhere, as words. -/
def storageKeys {C : Contract} (st : Storage C) : List Nat := SFields.fold mapKeysFold st

/-- **The slots a value occupies from a slot, with their words**: `ReprAt`
(`Evm/Repr.lean`) constructor by constructor, read as a function.  A `uint`
its number, a `bool` `bword b`, an `int` its two's complement word; a
struct its members from `s.add (offset n f)` (a struct's fields are given
the slot of each member); a dynamic array its length at `s` and element `i`
from `.data s (i · size E)`; a fixed-size one element `i` from
`s.add (i · size E)`; a `uint`-keyed mapping entry `k` from `.hash k s 0`,
for the keys `keys` and its own (a mapping of another key type takes no slot
the fragment reads: `ReprAt.map`'s `K = uint` premise).  Total: a typed
value is in range and of its shape. -/
def encodeFold (keys : List Nat) : Fold where
  V _ := Slot → List (Slot × Nat)
  F _ := (Name → Slot) → List (Slot × Nat)
  L _ := Unit
  W _ _ := (Nat → Slot) → Nat → List (Slot × Nat)
  M _ _ := List (Int × (Slot → List (Slot × Nat)))
  prim {p} v s := match p, v with
    | .uint, n => [(s, n.1.toNat)]
    | .bool, b => [(s, bword b)]
    | .int, n => [(s, toWord n.1)]
  struct {n} _ r s := r fun f => s.add (offset n f)
  array {E n} _ _ _ w _ s := (s, n) :: w (fun i => .data s (i * size E)) 0
  fixed {E _} _ w s := w (fun i => s.add (i * size E)) 0
  map {K _} _ _ m d s :=
    if K == .uint then
      let own := m.filterMap fun (k, _) => if 0 ≤ k ∧ k < (W : Int) then some k.toNat else none
      (own ++ keys).eraseDups.flatMap fun (k : Nat) => ((lookupBy (k : Int) m).getD d) (.hash (wmod k) s 0)
    else []
  fnil _ := []
  fcons {f _ _} _ _ v r slot := v (slot f) ++ r slot
  lnil := ()
  lcons _ _ _ _ := ()
  wnil _ _ := []
  wcons _ _ v r slot i := v (slot i) ++ r slot (i + 1)
  mnil := []
  mcons k _ _ v r := (PrimTy.key k, v) :: r

/-- The whole storage laid out: every root of the contract at `rootSlot`. -/
def encodeStorage (C : Contract) (keys : List Nat) (st : Storage C) : List (Slot × Nat) :=
  SFields.fold (encodeFold keys) st (rootSlot C)

/-- A machine storage holding the words listed, `0` elsewhere. -/
def storeOf (ws : List (Slot × Nat)) : WordStore :=
  WordStore.ofFn fun s => (lookupBy s ws).getD 0

/-- The word a value local's cell holds: `ReprV` read as a function. -/
def wordOf : (p : PrimTy) → p.Denote → Word
  | .uint, n => .val (wmod n.1.toNat)
  | .bool, b => .val (bword b)
  | .int, n => .val (sword n.1)

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

/-- A value of the type `p`: `genUint`, `genInt`, `genBool`. -/
def genVal : (p : PrimTy) → Gen p.Denote
  | .uint => do pure ((PrimTy.ofInt? .uint (← genUint)).getD (PrimTy.dflt .uint))
  | .int => do pure ((PrimTy.ofInt? .int (← genInt)).getD (PrimTy.dflt .int))
  | .bool => do pure (show Bool from ← genBool)

/-- How `#difftest` draws a storage: words by `genVal`;
up to `3` entries of a `uint`-keyed mapping (none for another key type,
which takes no slot the compiled code reads), a few small keys, so that two
entries or two reads can meet, and the largest word; arrays of fewer than
`4` elements. -/
def diffGen : TGen where
  prim p := genVal p
  key
    | .uint => some do
      if (← randBelow 8) < 7 then pure (PrimTy.ofIntD .uint (← randBelow 4 : Nat))
      else pure (PrimTy.ofIntD .uint (W - 1 : Nat))
    | _ => none
  entries := 4
  length := 4

/-- An argument as a literal: `5`, `-5`, `true`.  An `int` argument is kept
off `-2^255`, which no literal spells (`-x` of `2^255` is out of range). -/
def genArg : Ty → Gen (Option (RawExpr × Semantics.CallValue))
  | .prim .uint => do
    let n ← genVal .uint
    pure (some (.num n.1.toNat, .uint n))
  | .prim .bool => do let b ← genBool; pure (some (.bool b, .bool b))
  | .prim .int => do
    let n ← genVal .int
    let n := if n.1 = -(H : Int) then (PrimTy.ofInt? .int (n.1 + 1)).getD n else n
    pure (some (if n.1 < 0 then .unop .neg (.num n.1.natAbs) else .num n.1.toNat, .int n))
  | _ => pure none

/-! ## One run -/

/-- What a run starts from. -/
structure Start (C : Contract) where
  storage : Storage C
  args : List Semantics.CallValue
  sender : Nat
  value : Nat
  time : Nat
  /-- The contract's account. -/
  balance : Nat
  /-- The contract's address. -/
  self : Nat

/-- The typed state a run starts in: the storage, no memory, no locals,
the funds and the transaction's words (all drawn in range). -/
def Start.state {C : Contract} (s : Start C) : State C [] :=
  { State.init C with
    storage := s.storage
    selfBalance := PrimTy.ofIntD .uint s.balance
    tx := { msgSender := PrimTy.ofIntD .uint s.sender, msgValue := PrimTy.ofIntD .uint s.value,
            timestamp := PrimTy.ofIntD .uint s.time, selfAddress := PrimTy.ofIntD .uint s.self } }

/-- The start of a run, drawn: the storage, the arguments and the
transaction; `none` if a parameter has no value type. -/
def genStart (C : Contract) (d : FunDecl) : Gen (Option (Start C × List RawExpr)) := do
  let st ← diffGen.storage C
  let args ← d.params.mapM fun (_, T) => genArg T
  let sender ← randBelow 4
  let value ← randBelow 3
  let time ← randBelow 100
  let balance ← randBelow 100
  let self ← randBelow 4
  pure <| (args.mapM id).map fun args =>
    ({ storage := st, args := args.map (·.2), sender, value, time, balance, self }, args.map (·.1))

/-- A machine run's outcome, for the report. -/
def fmtOut : Evm.Out → String
  | .ok _ 0 => "ok"
  | .ok _ k => s!"ok with {k} instructions still to skip"
  | .revert => "revert"
  | .fault => "fault"

/-- Where the final machine fails to represent the final typed state, one
line each; empty when it does.  `names` are the final context's names. -/
def differences {Γ : Ctx} (C : Contract) (names : List Var) (keys : List Nat)
    (σ' : State C Γ) (m' : Machine) : List String :=
  let store := (encodeStorage C keys σ'.storage).filterMap fun (s, w) =>
    if m'.store s == w then none else some s!"slot {s}: typed run {w}, machine {m'.store s}"
  let vals := (names.zip (localCells Γ σ'.env)).filterMap fun (x, l, c) => match c with
    | some ⟨p, v⟩ =>
      if wordOf p v == m'.memAt l then none
      else some s!"local {x}: typed run {PrimTy.fmt v}, machine {m'.memAt l}"
    | none => none
  let net := σ'.net.filterMap fun (address, n) =>
    let a := address.1
    if a = m'.self.1 then
      (if n != 0 then some s!"net {a}: typed run {n} at the contract itself, expected 0" else none)
    else if 0 ≤ a ∧ a < (W : Int) ∧ n != (m'.bal₀ (wmod a.toNat) : Int) - m'.bal (wmod a.toNat) then
      some s!"net {a}: typed run {n}, account {m'.bal₀ (wmod a.toNat)} → {m'.bal (wmod a.toNat)}"
    else none
  let stack := if m'.stack.isEmpty then [] else [s!"stack left: {m'.stack}"]
  store ++ vals ++ net ++ stack

/-- One run of `Q` from `s`: whether both reverted when the two agree, else
the lines of the mismatch.  The machine has no panic: a failed `assert`
reverts there (`compile_correct`'s panic case). -/
def runOnce (C : Contract) {Γ' : Ctx} (Q : Prog C [] Γ') (s : Start C) :
    Except (List String) Bool :=
  let keys0 := storageKeys s.storage
  let σ := s.state
  let m : Machine :=
    { Machine.init (fun a => if a.1 = s.self then s.balance else 0) (wmod s.self) with
      accepts := fun a _ => a.1 != 3
      store := storeOf (encodeStorage C keys0 s.storage)
      caller := wmod s.sender
      callvalue := wmod s.value
      timestamp := wmod s.time }
  let res := Prog.run σ Q
  let out := Evm.run (Evm.compileProg 0 Q) m
  match res, out with
  | .error .revert, .revert => pure true
  | .error .panic, .revert => pure true
  | .ok _, .revert => if Evm.Prog.pays Q then pure true
    else throw ["typed run ok, machine revert, and no payment to refuse"]
  | .ok o, .ok m' 0 =>
    let keys := (keys0 ++ storageKeys o.st.storage).eraseDups
    match differences C (Q.outNames []) keys o.st m' with
    | [] => pure false
    | ds => throw (s!"both ok, and they differ:" :: ds)
  | _, _ => throw [s!"typed run {fmtTRes res}, machine {fmtOut out}"]

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
    let ⟨_, Q⟩ ← match callProg C f args with
      | .ok r => pure r
      | .error e => return [s!"skipped: {f} ({e})"]
    unless (Evm.inFragP (Evm.Frag.init []) Q).isSome do
      return [s!"skipped: {f} (outside the compiled fragment)"]
    unless Evm.Prog.pushes Q + 4 ≤ Lmax do return [s!"skipped: {f} (too many pushes)"]
    match runOnce C Q s with
    | .ok rev =>
      agreed := agreed + 1
      if rev then reverted := reverted + 1
    | .error ds =>
      let args := (d.params.zip s.args).map fun ((x, _), v) => s!"{x} = {CallValue.fmt v}"
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

/-- `#difftest C (runs := n) (seed := s)`: compare the typed run with the
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
