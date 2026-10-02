import Solidity.FreshNames
import Solidity.Calculus.Chains
import Solidity.Examples.Chains.Storage

/-!
# Printed names for the rules' fresh variables

`#derivation` spells a rule's fresh variables `se1`, `sp1`; the examples name
each after what it holds, and per example.  Each example here is a namespace
with its own table (`FreshNames.lean`), and every line in it — `dl!{ … }`,
`sol{ … }`, `#derivation`, `sol_chain`'s errors — reads and prints the
printed names:

* `Headline` — `alice.account.balance = 10;`, whose table is
  `Chains.Storage.BalanceWrite.names` (the value `pv`, the alias `acc`; the
  chain itself is `BalanceWrite.chain`): a line is the term its default
  spelling gives, a capture is numbered past `pv`, an error prints `pv`;
* `Capture` — a `sol{ … }` capture numbered past a table name.

A table changes spellings only: each line is the term its default spelling
gives (`headlineLast`, `captured`), so the chains of `Examples/Chains/` check
as they do in the default spelling.
-/

namespace Solidity.Examples.ExampleNames

local instance : InContract := ⟨StandardExample⟩

/-- The headline's last line, in the default spelling. -/
def headlineLast : Fml StandardExample :=
  dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
        alice.account.balance == 10 }

/-- A capture in a formula, numbered past the parameter `se1`. -/
def capturedDl : Fml StandardExample := dl!{ ⟨ values[total + 1] += 2; ⟩ se1 == 0 }

/-- A capture in a block, numbered past the local `ie1`. -/
def captured : Prog StandardExample := sol{ uint ie1 = 1; values[total + 1] += 2; }

-- with no rows, a table is the default spelling
example : (FreshNames.ofTable []).name "sp" 2 = "sp2" := rfl

-- what a table that does not read back breaks, row by row
/--
info: ["se2 is itself a fresh variable's spelling", "alice is a state variable or an enum of the contract",
  "sp9x is not a fresh variable's spelling", "pv names two variables", "se3 has two names",
  "storage is a word the readers resolve first", "k2 is a word the readers resolve first", "my var is not a name",
  "selfBalance is a word the readers resolve first", "net is a word the readers resolve first",
  "ie6 is given the empty name", "Account is a struct type or a function of the contract"]
-/
#guard_msgs in
#eval FreshNames.clashes StandardExample
  [("se2", "se1"), ("alice", "sp1"), ("x", "sp9x"), ("pv", "se2"), ("pv", "se4"), ("y", "se3"),
   ("z", "se3"), ("storage", "ie1"), ("k2", "ie2"), ("my var", "ie3"), ("selfBalance", "ie4"),
   ("net", "ie5"), ("", "ie6"), ("Account", "mv1")]

namespace Headline

local instance : FreshNames := .ofTable Chains.Storage.BalanceWrite.names

-- `acc` reads as `sp1`, and `se1` prints as `pv`
#guard Var.ofName "acc" == .fresh "sp" 1 && toString (Var.fresh "se" 1) == "pv"

-- the same term as the default spelling's, which still reads
example : dl!{ { pv := 10 } { acc := alice.account } { storage := save(storage, acc.balance, pv) }
    alice.account.balance == 10 } = headlineLast := rfl
example : dl!{ { se1 := 10 } true } = dl!{ { pv := 10 } true } := rfl

-- a capture is numbered past `pv`
example : dl!{ ⟨ values[total + 1] += 2; ⟩ pv == 0 } = capturedDl := rfl

-- an error prints the table's names too
/--
error: sol_chain: the derivation of
  dl{ ⟨ alice.account.balance = 10; ⟩ find(storage, alice.account.balance) = 10 }
does not reach
  dl{
    ⟨ uint pv = 11; Account storage acc = alice.account; acc.balance = pv; ⟩ find(storage, alice.account.balance) = 10 }
Its lines:
    dl{ ⟨ alice.account.balance = 10; ⟩ find(storage, alice.account.balance) = 10 }
  ~[storageFieldWrite_unfold_leftFst]~>
    dl{
  ⟨ uint pv = 10; Account storage acc = alice.account; acc.balance = pv; ⟩ find(storage, alice.account.balance) = 10 }
-/
#guard_msgs in
example : dl!{ ⟨ alice.account.balance = 10; ⟩ alice.account.balance == 10 }
    ~> dl!{ ⟨ uint pv = 11; Account storage acc = alice.account; acc.balance = pv; ⟩
            alice.account.balance == 10 } := by
  sol_chain

end Headline

namespace Capture

/-- The index a compound assignment captures, `ie1`, is `idx`. -/
def names : FreshTable := [("idx", "ie1")]

local instance : FreshNames := .ofTable names

#guard (FreshNames.clashes StandardExample names).isEmpty

example : Prog.toStr (sol{ values[total + 1] += 2; }) = "uint idx = total + 1; values[idx] += 2;" :=
  rfl

-- a program local spelled like a row is that fresh variable (the hazard of
-- `FreshNames.lean`'s docstring); its capture is numbered past it, not
-- re-declared
example : sol{ uint idx = 1; values[total + 1] += 2; } = captured := rfl
example : Prog.toStr (sol{ uint idx = 1; values[total + 1] += 2; }) =
    "uint idx = 1; uint ie2 = total + 1; values[ie2] += 2;" := rfl

end Capture

end Solidity.Examples.ExampleNames
