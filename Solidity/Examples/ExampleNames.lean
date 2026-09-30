import Solidity.FreshNames
import Solidity.Calculus.Chains

/-!
# Printed names for the rules' fresh variables

`#derivation` spells a rule's fresh variables `se1`, `sp1`; the examples name
each after what it holds, and per example.  Each example here is a namespace
with its own table (`FreshNames.lean`), and every line in it — `dl!{ … }`,
`sol{ … }`, `#derivation`, `sol_chain`'s errors — reads and prints the
printed names:

* `Headline` — `alice.account.balance = 10;`: the value `pv`, the alias
  `acc`.  Its chains are the headline's of
  `Examples/Chains.lean`, which reads this table; here are its tests: a
  line is the term its default spelling gives, a capture is numbered past
  `pv`, an error prints `pv`;
* `Token` — `alice.account.token.value = 5;`: `aliceTok`, then `aliceAcc`,
  the alias the second unfolding declares;
* `Memory` — `carol.account.balance = 10;`: `acc` again, now a memory
  reference;
* `Matrix` — `matrix[i++][i++] = 77;`: `idx1`, `sp`, `idx2`, captured by the
  elaborator in solc's order;
* `Snapshot` — `m[i++] = i;`: the value `a` captured before the index `b`
  runs;
* `Capture` — a `sol{ … }` capture numbered past a table name.

A table changes spellings only: each line is the term its default spelling
gives (`headlineLast`, `captured`), so the chains check as they do in
the default spelling.  The printed `int pv` is `uint pv` here (the
type of the place written), and its last lines, with the updates applied,
are not drawn.
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

/-- `alice.account.balance = 10;`: the value `pv`, the alias `acc`. -/
def names : FreshTable := [("pv", "se1"), ("acc", "sp1")]

local instance : FreshNames := .ofTable names

#guard (FreshNames.clashes StandardExample names).isEmpty

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

namespace Token

/-- `alice.account.token.value = 5;`: `aliceAcc` is the second alias, `sp2`. -/
def names : FreshTable := [("pv", "se1"), ("aliceTok", "sp1"), ("aliceAcc", "sp2")]

local instance : FreshNames := .ofTable names

#guard (FreshNames.clashes StandardExample names).isEmpty

/--
info:     dl{ ⟨ alice.account.token.value = 5; ⟩ find(storage, alice.account.token.value) = 5 }
  ~[storageFieldWrite_unfold_leftFst]~>
    dl{
  ⟨ uint pv = 5; Token storage aliceTok = alice.account.token; aliceTok.value = pv; ⟩
    find(storage, alice.account.token.value) = 5 }
  ~[localValueDeclInitDrop]~>
    dl{
  ⟨ pv = 5; Token storage aliceTok = alice.account.token; aliceTok.value = pv; ⟩
    find(storage, alice.account.token.value) = 5 }
  ~[localValueAssign]~>
    dl{
  { pv := 5 }
    ⟨ Token storage aliceTok = alice.account.token; aliceTok.value = pv; ⟩
      find(storage, alice.account.token.value) = 5 }
  ~[storageLocalDeclInitDrop]~>
    dl{
  { pv := 5 } ⟨ aliceTok = alice.account.token; aliceTok.value = pv; ⟩ find(storage, alice.account.token.value) = 5 }
  ~[storageFieldRead_unfold_rightFst]~>
    dl{
  { pv := 5 }
    ⟨ Account storage aliceAcc = alice.account; aliceTok = aliceAcc.token; aliceTok.value = pv; ⟩
      find(storage, alice.account.token.value) = 5 }
  ~[storageLocalDeclInitDrop]~>
    dl{
  { pv := 5 }
    ⟨ aliceAcc = alice.account; aliceTok = aliceAcc.token; aliceTok.value = pv; ⟩
      find(storage, alice.account.token.value) = 5 }
  ~[storageFieldReadBindLocalRoot]~>
    dl{
  { pv := 5 }
    { aliceAcc := alice.account }
      ⟨ aliceTok = aliceAcc.token; aliceTok.value = pv; ⟩ find(storage, alice.account.token.value) = 5 }
  ~[storageFieldReadBindLocalRoot]~>
    dl{
  { pv := 5 }
    { aliceAcc := alice.account }
      { aliceTok := aliceAcc.token } ⟨ aliceTok.value = pv; ⟩ find(storage, alice.account.token.value) = 5 }
  ~[storageFieldWriteSave]~>
    dl{
  { pv := 5 }
    { aliceAcc := alice.account }
      { aliceTok := aliceAcc.token }
        { storage := save(storage, aliceTok.value, pv) } ⟨ ⟩ find(storage, alice.account.token.value) = 5 }
  ~[emptyModality]~>
    dl{
  { pv := 5 }
    { aliceAcc := alice.account }
      { aliceTok := aliceAcc.token }
        { storage := save(storage, aliceTok.value, pv) } find(storage, alice.account.token.value) = 5 }
-/
#guard_msgs in
#derivation dl!{ ⟨ alice.account.token.value = 5; ⟩ alice.account.token.value == 5 }

/-- The printed chain.  The line `storageFieldRead_unfold_rightFst` reaches is
left `_`: `dl!{ … }` does not read it back in any spelling (`sp1 =
sp2.token` is refused as well), since it types an alias bound by an
assignment only from a state variable's path (`aliceTok =
alice.account.token`), not from another alias's (`aliceTok =
aliceAcc.token`); `Calculus/Notation.lean` lists the gap.  The
`#derivation` above shows the line. -/
def token : dl!{ ⟨ alice.account.token.value = 5; ⟩ alice.account.token.value == 5 }
    ~*> dl!{ { pv := 5 } { aliceAcc := alice.account } { aliceTok := aliceAcc.token }
              { storage := save(storage, aliceTok.value, pv) } alice.account.token.value == 5 } :=
  calc dl!{ ⟨ alice.account.token.value = 5; ⟩ alice.account.token.value == 5 }
    _ ~[storageFieldWrite_unfold_leftFst]~>
        dl!{ ⟨ uint pv = 5; Token storage aliceTok = alice.account.token; aliceTok.value = pv; ⟩
            alice.account.token.value == 5 } := rfl
    _ ~*> dl!{ { pv := 5 } ⟨ aliceTok = alice.account.token; aliceTok.value = pv; ⟩
            alice.account.token.value == 5 } := by sol_chain
    _ ~[storageFieldRead_unfold_rightFst]~> _ := rfl
    _ ~*> dl!{ { pv := 5 } { aliceAcc := alice.account } { aliceTok := aliceAcc.token }
              ⟨ aliceTok.value = pv; ⟩ alice.account.token.value == 5 } := by sol_chain
    _ ~*> dl!{ { pv := 5 } { aliceAcc := alice.account } { aliceTok := aliceAcc.token }
              { storage := save(storage, aliceTok.value, pv) } alice.account.token.value == 5 } := by
      sol_chain

end Token

namespace Memory

/-- `carol.account.balance = 10;`: `acc` is a memory reference here, `mv1`. -/
def names : FreshTable := [("acc", "mv1")]

local instance : FreshNames := .ofTable names

#guard (FreshNames.clashes StandardExample names).isEmpty

/--
info:     dl{ ⟨ Person memory carol; carol.account.balance = 10; ⟩ true }
  ~[memoryReferenceDeclFreshAlloc]~>
    dl{ { carol := freshId(addM(memory)) ‖ memory := addM(memory) } ⟨ carol.account.balance = 10; ⟩ true }
  ~[memoryFieldWrite_unfold_leftFst]~>
    dl{
  { carol := freshId(addM(memory)) ‖ memory := addM(memory) }
    ⟨ Account memory acc = carol.account; acc.balance = 10; ⟩ true }
  ~[memoryLocalDeclInitDrop]~>
    dl{ { carol := freshId(addM(memory)) ‖ memory := addM(memory) } ⟨ acc = carol.account; acc.balance = 10; ⟩ true }
  ~[memoryFieldReadAliasRoot]~>
    dl{
  { carol := freshId(addM(memory)) ‖ memory := addM(memory) }
    { acc := read(memory, carol.account) } ⟨ acc.balance = 10; ⟩ true }
  ~[memoryFieldWriteStore]~>
    dl{
  { carol := freshId(addM(memory)) ‖ memory := addM(memory) }
    { acc := read(memory, carol.account) } { memory := write(memory, acc.balance, 10) } ⟨ ⟩ true }
  ~[emptyModality]~>
    dl{
  { carol := freshId(addM(memory)) ‖ memory := addM(memory) }
    { acc := read(memory, carol.account) } { memory := write(memory, acc.balance, 10) } true }
-/
#guard_msgs in
#derivation dl!{ ⟨ Person memory carol; carol.account.balance = 10; ⟩ true }

end Memory

namespace Matrix

/-- `matrix[i++][i++] = 77;`: the receiver's index `idx1`, the row `sp`, the
index `idx2`. -/
def names : FreshTable := [("idx1", "se1"), ("sp", "sp2"), ("idx2", "se3")]

local instance : FreshNames := .ofTable names

#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `matrix[i++][i++] = 77;`, Lean's derivation of
it in the printed names, down to the in-bounds write.  The lines are not the
printed ones: the elaborator captures both increments before the write (the first
step, an equality), where the printed rules capture them as they unfold it;
the printed `pv` is not declared, since `77` is already a value. -/
def matrix : dl!{ ⟨ matrix[i++][i++] = 77; ⟩ matrix[0][1] == 77 }
    ~*> dl!{ { idx1 := 0 } { i := i + 1 ‖ idx1 := i } { sp := matrix[idx1] } { idx2 := 0 }
              { i := i + 1 ‖ idx2 := i } { storage := save(storage, sp[idx2], 77) }
              matrix[0][1] == 77 } :=
  calc dl!{ ⟨ matrix[i++][i++] = 77; ⟩ matrix[0][1] == 77 }
    _ = dl!{ ⟨ uint idx1; idx1 = i++; uint[] storage sp = matrix[idx1]; uint idx2; idx2 = i++;
            sp[idx2] = 77; ⟩ matrix[0][1] == 77 } := rfl
    _ ~*> dl!{ { idx1 := 0 } { i := i + 1 ‖ idx1 := i } { sp := matrix[idx1] } { idx2 := 0 }
              { i := i + 1 ‖ idx2 := i } ⟨ sp[idx2] = 77; ⟩ matrix[0][1] == 77 } := by sol_chain
    _ ~[storageIndexWriteArraySave]~>
        dl!{ { idx1 := 0 } { i := i + 1 ‖ idx1 := i } { sp := matrix[idx1] } { idx2 := 0 }
              { i := i + 1 ‖ idx2 := i } { storage := save(storage, sp[idx2], 77) } ⟨⟩
              matrix[0][1] == 77 } := rfl
    _ ~[emptyModality]~>
        dl!{ { idx1 := 0 } { i := i + 1 ‖ idx1 := i } { sp := matrix[idx1] } { idx2 := 0 }
              { i := i + 1 ‖ idx2 := i } { storage := save(storage, sp[idx2], 77) }
              matrix[0][1] == 77 } := rfl

end Matrix

namespace Snapshot

/-- `m[i++] = i;`: the value `a`, then the index `b`. -/
def names : FreshTable := [("a", "se1"), ("b", "se2")]

local instance : FreshNames := .ofTable names

#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `m[i++] = i;`, as `balances[i++] = i;`:
the elaborator snapshots the value `a` before the index `b` runs `i++`, so
the write stores the old `i`.  Lean declares `b` and then assigns it, where
the printed chain initialises it. -/
def snapshot : dl!{ ⟨ balances[i++] = i; ⟩ balances[0] == 0 }
    ~*> dl!{ { a := i } { b := 0 } { i := i + 1 ‖ b := i } { storage := save(storage, balances[b], a) }
              balances[0] == 0 } :=
  calc dl!{ ⟨ balances[i++] = i; ⟩ balances[0] == 0 }
    _ = dl!{ ⟨ uint a = i; uint b; b = i++; balances[b] = a; ⟩ balances[0] == 0 } := rfl
    _ ~*> dl!{ { a := i } { b := 0 } { i := i + 1 ‖ b := i } ⟨ balances[b] = a; ⟩
            balances[0] == 0 } := by sol_chain
    _ ~[storageIndexWriteMappingSave]~>
        dl!{ { a := i } { b := 0 } { i := i + 1 ‖ b := i } { storage := save(storage, balances[b], a) }
            ⟨⟩ balances[0] == 0 } := rfl
    _ ~[emptyModality]~>
        dl!{ { a := i } { b := 0 } { i := i + 1 ‖ b := i } { storage := save(storage, balances[b], a) }
            balances[0] == 0 } := rfl

end Snapshot

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
