import Solidity.Calculus.Chains
import Solidity.Calculus.LastLine
import Solidity.Calculus.ChainGen
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# Memory array examples as chains

The calculus's worked memory-array examples, in order, each one chain term over any modality `m` and
postcondition `φ` (`Examples/Chains/Storage.lean` says how to read one, `Chains/Memory.lean` the memory
conventions), in the printed names (`FreshNames` tables: `idx`, `pv`, `acc`, `mv`).

* The first line puts the arrays the program indexes in front of it, as the update their declarations
  leave, with three elements: `{ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }`.
  The printed `uint[]` is empty when fresh, so every index into it would revert, and the update notation
  has no `new uint[](n)`.  The index `i`, a value `val`, the element a program reads and the storage a
  call reads get a concrete value there too.
* An index read or write takes no bounds branch here: an index out of range halts the read (or reverts
  the write) by itself, where the printed trace splits on `0 ≤ i < ℓ`; its `⊤`/`⊥` branches are not
  drawn.
* A nonsimple index is captured by the elaborator (`uint idx; idx = ++i;`), so the printed first `⇝` is
  the program as written; the receiver of `carolValues[++i] = …` is not re-aliased (the printed `mv1`),
  since no operand here rebinds a local.
* `Account` has no `tokens` or `values` here: `TokenBucket`'s `tokens` and `Basket`'s `items`
  (`TestSuite`) stand for `carol.account.tokens` and `carol.account.values`, one selector shorter, and
  `tk` for `tok` (a state variable there).  Those members are dynamic arrays, empty in a fresh object.
* Past the program the stack merges (`~[sequentialToParallel]~>`), an index folds (`~[add_literals]~>`)
  and each read is resolved by a law, one link each, every capture kept to the last line, which
  `#last_line` checks.  Where no law applies, the declaration says what is missing.
-/

namespace Solidity.Examples.Chains.MemoryArrays

local instance : InContract := ⟨StandardExample⟩

section
variable (m : Modality) (φ : Post StandardExample)

/-! ## Example: Index Read and Write on a Memory Array -/

namespace IndexRead

/-- `v = carolValues[i];` with `i` 2, from a memory where `carolValues[2]` is 10: read out of the heap at
the index (the paper's `⇝`, the rule and its empty program); past the merge the read is the write's value
(`readOnWrite`). -/
theorem chain :
    dl![m]{
      { i := 2 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
        { memory := write(memory, carolValues[2], 10) } ⟨[ v = carolValues[i]; ]⟩ φ }
    ~*> dl![m]{
        { i := 2 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
          { memory := write(memory, carolValues[2], 10) } { v := read(memory, carolValues[i]) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ carolValues := freshId(addM(memory, uint[3])) ‖
            memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], 10) ‖
            v :=
              read(write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], 10), freshId(addM(memory, uint[3]))[2]) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { i := 2 ‖ carolValues := freshId(addM(memory, uint[3])) ‖
            memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], 10) ‖ v := 10 }
          φ } := by
  sol_chain
#last_line chain

end IndexRead

namespace IndexWrite

/-- `carolValues[i] = 100;` with `i` 2: written into the heap at the index (the paper's `⇝`). -/
theorem chain :
    dl![m]{
      { i := 2 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
        ⟨[ carolValues[i] = 100; ]⟩ φ }
    ~*> dl![m]{
        { i := 2 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
          { memory := write(memory, carolValues[i], 100) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ carolValues := freshId(addM(memory, uint[3])) ‖
            memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], 100) }
          φ } := by
  sol_chain
#last_line chain

end IndexWrite

/-! ## Example: A Fixed-Size Memory Array -/

namespace FixedArray

/-- `uint[3] memory x; x[1] = 5;` — the declaration tags the fresh root with the shape of `uint[3]`
(`addM(memory, uint[3])`), which holds the length (the paper's `⇝`); the write is an element write.  The
printed program's `assert`s are not drawn: each splits the line into its three goals, and the update
notation prints a comparison's result (`se1 := 3 == 3`) only as a `‹…›` escape
(`Calculus/RuleSyntax.lean`). -/
theorem chain :
    dl![m]{ ⟨[ uint[3] memory x; x[1] = 5; ]⟩ φ }
    ~[memoryReferenceDeclFreshAlloc]~> dl![m]{
        { x := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) } ⟨[ x[1] = 5; ]⟩ φ }
    ~*> dl![m]{
        { x := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) } { memory := write(memory, x[1], 5) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { x := freshId(addM(memory, uint[3])) ‖ memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[1], 5) }
          φ } := by
  sol_chain
#last_line chain

end FixedArray

/-! ## Example: Additional Memory Array Cases -/

namespace IndexReadCaptured

/-- `idx`, the captured index. -/
def names : FreshTable := [("idx", "se1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `v = carolValues[++i];` with `i` 1, from a memory where `carolValues[2]` is 10: the index captured,
then read at (the paper's `⇝*`); the merge resolves the index to `1 + 1`, which folds to `2` in `i`, `idx`
and the read (`add_literals`, inside a memory term too), and the read of the write resolves to `10`
(`readOnWrite`). -/
theorem chain :
    dl![m]{
      { i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
        { memory := write(memory, carolValues[2], 10) } ⟨[ v = carolValues[++i]; ]⟩ φ }
    ~*> dl![m]{
        { i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
          { memory := write(memory, carolValues[2], 10) }
            { idx := 0 } { i := i + 1 ‖ idx := i + 1 } { v := read(memory, carolValues[idx]) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖
            memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], 10) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖
            v :=
              read(write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], 10),
                freshId(addM(memory, uint[3]))[1 + 1]) }
          φ }
    ~[add_literals]~> dl![m]{
        { i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖
            memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], 10) ‖ idx := 0 ‖ i := 2 ‖ idx := 2 ‖
            v :=
              read(write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], 10), freshId(addM(memory, uint[3]))[2]) }
          φ }
    ~[readOnWrite]~> dl![m]{
        { i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖
            memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], 10) ‖ idx := 0 ‖ i := 2 ‖ idx := 2 ‖
            v := 10 }
          φ } := by
  sol_chain
#last_line chain

end IndexReadCaptured

namespace IndexWriteCaptured

/-- `pv`, the snapshot of the right-hand side, and `idx`, the captured index. -/
def names : FreshTable := [("pv", "se1"), ("idx", "se2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `carolValues[++i] = val;` with `i` 1 and `val` 7: the right-hand side is snapshot before the index
runs, then the element written by the captured index (the paper's `⇝*`); the merge resolves the index to
`1 + 1` and the value to `7`, and the index folds to `2` in `i`, `idx` and the write. -/
theorem chain :
    dl![m]{
      { i := 1 ‖ val := 7 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
        ⟨[ carolValues[++i] = val; ]⟩ φ }
    ~*> dl![m]{
        { i := 1 ‖ val := 7 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
          { pv := val } { idx := 0 } { i := i + 1 ‖ idx := i + 1 } { memory := write(memory, carolValues[idx], pv) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 1 ‖ val := 7 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ pv := 7 ‖ idx := 0 ‖ i := 1 + 1 ‖ idx := 1 + 1 ‖
            memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[1 + 1], 7) }
          φ }
    ~[add_literals]~> dl![m]{
        { i := 1 ‖ val := 7 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ pv := 7 ‖ idx := 0 ‖ i := 2 ‖ idx := 2 ‖
            memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], 7) }
          φ } := by
  sol_chain
#last_line chain

end IndexWriteCaptured

namespace ElementFromField

/-- `acc`, the alias of `david.account`. -/
def names : FreshTable := [("acc", "mv1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `carolTokens[i] = david.account.token;` with `i` 2: the source's receiver is bound (`acc`, where the
printed trace binds the source as `tok`), then the element is written with the identity the member holds
(the paper's `⇝*`).  The last line keeps the reads of `david`'s members: no law reads a member of a fresh
object to its identity. -/
theorem chain :
    dl![m]{
      { i := 2 ‖ carolTokens := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) }
        { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          ⟨[ carolTokens[i] = david.account.token; ]⟩ φ }
    ~[memoryFieldRead_unfold_rightFst]~> dl![m]{
        { i := 2 ‖ carolTokens := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) }
          { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ Account memory acc = david.account; carolTokens[i] = acc.token; ]⟩ φ }
    ~*> dl![m]{
        { i := 2 ‖ carolTokens := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) }
          { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            { acc := read(memory, david.account) } { memory := write(memory, carolTokens[i], read(memory, acc.token)) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ carolTokens := freshId(addM(memory, Token[3])) ‖ david := freshId(addM(addM(memory, Token[3]), Person)) ‖
            acc := read(addM(addM(memory, Token[3]), Person), freshId(addM(addM(memory, Token[3]), Person)).account) ‖
            memory :=
              write(addM(addM(memory, Token[3]), Person), freshId(addM(memory, Token[3]))[2],
                read(addM(addM(memory, Token[3]), Person),
                  read(addM(addM(memory, Token[3]), Person), freshId(addM(addM(memory, Token[3]), Person)).account).token)) }
          φ } := by
  sol_chain
#last_line chain

end ElementFromField

namespace FieldFromElement

/-- `mv`, the alias of `carol.account`. -/
def names : FreshTable := [("mv", "mv1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `carol.account.token = davidTokens[i];` with `i` 2: the target's receiver is bound (`mv`), then the
member is written with the element's identity (the paper's `⇝*`; the printed `tok` is not declared).  Past
the merge the read of `carol.account` passes the later allocation of `davidTokens`
(`readAddDifferentIdentity`); the element of the fresh `davidTokens` is an identity, which no law reads. -/
theorem chain :
    dl![m]{
      { i := 2 ‖ carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
        { davidTokens := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) }
          ⟨[ carol.account.token = davidTokens[i]; ]⟩ φ }
    ~[memoryFieldWrite_unfold_leftFst]~> dl![m]{
        { i := 2 ‖ carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { davidTokens := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) }
            ⟨[ Account memory mv = carol.account; mv.token = davidTokens[i]; ]⟩ φ }
    ~*> dl![m]{
        { i := 2 ‖ carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
          { davidTokens := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) }
            { mv := read(memory, carol.account) } { memory := write(memory, mv.token, read(memory, davidTokens[i])) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ carol := freshId(addM(memory, Person)) ‖ davidTokens := freshId(addM(addM(memory, Person), Token[3])) ‖
            mv := read(addM(addM(memory, Person), Token[3]), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(addM(memory, Person), Token[3]),
                read(addM(addM(memory, Person), Token[3]), freshId(addM(memory, Person)).account).token,
                read(addM(addM(memory, Person), Token[3]), freshId(addM(addM(memory, Person), Token[3]))[2])) }
          φ }
    ~[readAddDifferentIdentity]~> dl![m]{
        { i := 2 ‖ carol := freshId(addM(memory, Person)) ‖ davidTokens := freshId(addM(addM(memory, Person), Token[3])) ‖
            mv := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
            memory :=
              write(addM(addM(memory, Person), Token[3]),
                read(addM(memory, Person), freshId(addM(memory, Person)).account).token,
                read(addM(addM(memory, Person), Token[3]), freshId(addM(addM(memory, Person), Token[3]))[2])) }
          φ } := by
  sol_chain
#last_line chain

end FieldFromElement

namespace ElementAlias

/-- `idx`, the captured index. -/
def names : FreshTable := [("idx", "se1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `Token memory tok = carolTokens[++i];` with `i` 1: the index captured and bound, the declaration
dropped (the paper's first `⇝`, which here comes after the capture), and `tok` bound to the element's
identity; the merge resolves the index to `1 + 1`, which folds to `2` in `i`, `idx` and the read.  The read
of the element stays: it is an identity of the fresh `carolTokens`, which no law reads. -/
theorem chain :
    dl![m]{
      { i := 1 ‖ carolTokens := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) }
        ⟨[ Token memory tok = carolTokens[++i]; ]⟩ φ }
    ~*> dl![m]{
        { i := 1 ‖ carolTokens := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) }
          { idx := 0 } { i := i + 1 ‖ idx := i + 1 } ⟨[ Token memory tok = carolTokens[idx]; ]⟩ φ }
    ~[memoryLocalDeclInitDrop]~> dl![m]{
        { i := 1 ‖ carolTokens := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) }
          { idx := 0 } { i := i + 1 ‖ idx := i + 1 } ⟨[ tok = carolTokens[idx]; ]⟩ φ }
    ~*> dl![m]{
        { i := 1 ‖ carolTokens := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) }
          { idx := 0 } { i := i + 1 ‖ idx := i + 1 } { tok := read(memory, carolTokens[idx]) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 1 ‖ carolTokens := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) ‖ idx := 0 ‖ i := 1 + 1 ‖
            idx := 1 + 1 ‖ tok := read(addM(memory, Token[3]), freshId(addM(memory, Token[3]))[1 + 1]) }
          φ }
    ~[add_literals]~> dl![m]{
        { i := 1 ‖ carolTokens := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) ‖ idx := 0 ‖ i := 2 ‖
            idx := 2 ‖ tok := read(addM(memory, Token[3]), freshId(addM(memory, Token[3]))[2]) }
          φ } := by
  sol_chain
#last_line chain

end ElementAlias

end

namespace CallValue

/-- `makeValue()` reads a state variable. -/
def Calls : Contract := contract!{
  uint seed; uint[] values;
  function makeValue() returns (uint) { return seed; }
}

local instance : InContract := ⟨Calls⟩

/-- `pv`, the call's value, and `idx`, the captured index. -/
def names : FreshTable := [("pv", "se1"), ("idx", "se3")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Calls names).isEmpty

section
variable (m : Modality) (φ : Post Calls)

/-- `carolValues[++i] = makeValue();` with `i` 1, from a storage where `seed` is 7: the call is captured
before the index (solc's order; the paper prints only that capture, which is the program as written
here), inlined (`makeValue`'s result `se2`, the printed `makeValue()`), the index captured and the
element written.  The receiver is not re-aliased, as the printed first line does with `mv1`.  Past the
merge `seed` is read in the starting storage (`findOnSave`, in the write too) and the index folds.  The
starting storage is an update of its
own: `sequentialToParallel` merges an update that writes memory only where its other elements bind
locals (`Upd.merge`). -/
theorem incrementIndex :
    dl![m]{
      { storage := save(storage, seed, 7) }
        { i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
          ⟨[ carolValues[++i] = makeValue(); ]⟩ φ }
    ~[valueDeclSkip]~> dl![m]{
        { storage := save(storage, seed, 7) }
          { i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
            { pv := 0 } ⟨[ pv = makeValue(); uint idx; idx = ++i; carolValues[idx] = pv; ]⟩ φ }
    ~[functionBodyExpand]~> dl![m]{
        { storage := save(storage, seed, 7) }
          { i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
            { pv := 0 } ⟨[ uint se2; se2 = seed; pv = se2; uint idx; idx = ++i; carolValues[idx] = pv; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, seed, 7) }
          { i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
            { pv := 0 } { se2 := 0 } { se2 := find(storage, seed) } { pv := se2 } { idx := 0 }
              ⟨[ idx = ++i; carolValues[idx] = pv; ]⟩ φ }
    ~[localAssignIncrement]~> dl![m]{
        { storage := save(storage, seed, 7) }
          { i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
            { pv := 0 } { se2 := 0 } { se2 := find(storage, seed) } { pv := se2 } { idx := 0 }
              { i := i + 1 ‖ idx := i + 1 } ⟨[ carolValues[idx] = pv; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, seed, 7) }
          { i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
            { pv := 0 } { se2 := 0 } { se2 := find(storage, seed) } { pv := se2 } { idx := 0 }
              { i := i + 1 ‖ idx := i + 1 } { memory := write(memory, carolValues[idx], pv) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { storage := save(storage, seed, 7) ‖ i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ pv := 0 ‖ se2 := 0 ‖
            se2 := find(save(storage, seed, 7), seed) ‖ pv := find(save(storage, seed, 7), seed) ‖ idx := 0 ‖
            i := 1 + 1 ‖ idx := 1 + 1 ‖
            memory :=
              write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[1 + 1], find(save(storage, seed, 7), seed)) }
          φ }
    ~[findOnSave]~> dl![m]{
        { storage := save(storage, seed, 7) ‖ i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ pv := 0 ‖ se2 := 0 ‖
            se2 := 7 ‖ pv := 7 ‖ idx := 0 ‖ i := 1 + 1 ‖ idx := 1 + 1 ‖
            memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[1 + 1], 7) }
          φ }
    ~[add_literals]~> dl![m]{
        { storage := save(storage, seed, 7) ‖ i := 1 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ pv := 0 ‖ se2 := 0 ‖
            se2 := 7 ‖ pv := 7 ‖ idx := 0 ‖ i := 2 ‖ idx := 2 ‖
            memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], 7) }
          φ } := by
  sol_chain
#last_line incrementIndex

/-- `carolValues[i] = makeValue();` with `i` 2, from a storage where `seed` is 7: the call captured,
inlined, and written (the paper's `⇝*`); past the merge `seed` is read in the starting storage
(`findOnSave`), in the captures and in the write. -/
theorem simpleIndex :
    dl![m]{
      { storage := save(storage, seed, 7) }
        { i := 2 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
          ⟨[ carolValues[i] = makeValue(); ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, seed, 7) }
          { i := 2 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
            { pv := 0 } { se2 := 0 } { se2 := find(storage, seed) } { pv := se2 }
              { memory := write(memory, carolValues[i], pv) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { storage := save(storage, seed, 7) ‖ i := 2 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ pv := 0 ‖ se2 := 0 ‖
            se2 := find(save(storage, seed, 7), seed) ‖ pv := find(save(storage, seed, 7), seed) ‖
            memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], find(save(storage, seed, 7), seed)) }
          φ }
    ~[findOnSave]~> dl![m]{
        { storage := save(storage, seed, 7) ‖ i := 2 ‖ carolValues := freshId(addM(memory, uint[3])) ‖ pv := 0 ‖ se2 := 0 ‖
            se2 := 7 ‖ pv := 7 ‖ memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[2], 7) }
          φ } := by
  sol_chain
#last_line simpleIndex

end

end CallValue

namespace ElementOfField

local instance : InContract := ⟨TestSuite⟩

/-- `pv` the right-hand side, `mv` the receiver, `idx` the index. -/
def names : FreshTable := [("pv", "se1"), ("mv", "mv1"), ("idx", "ie1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes TestSuite names).isEmpty

section
variable (m : Modality) (φ : Post TestSuite)

/-- `b.items[i] = val;` with `i` 2 and `val` 7, for the printed `carol.account.values[i] = val;`
(`Basket memory b` for `carol.account`): the right-hand side, the receiver and the index are each bound
(the paper's `⇝`), and the element is written (its `⇝*`); the merge resolves the receiver to `mv`'s read.
That read stays: no law reads a member of a fresh object to its identity. -/
theorem valueWrite :
    dl![m]{
      { i := 2 ‖ val := 7 ‖ b := freshId(addM(memory, Basket)) ‖ memory := addM(memory, Basket) }
        ⟨[ b.items[i] = val; ]⟩ φ }
    ~[memoryIndexWriteCaptureAllComplexRecv]~> dl![m]{
        { i := 2 ‖ val := 7 ‖ b := freshId(addM(memory, Basket)) ‖ memory := addM(memory, Basket) }
          ⟨[ uint pv = val; uint[] memory mv = b.items; uint idx = i; mv[idx] = pv; ]⟩ φ }
    ~*> dl![m]{
        { i := 2 ‖ val := 7 ‖ b := freshId(addM(memory, Basket)) ‖ memory := addM(memory, Basket) }
          { pv := val } { mv := read(memory, b.items) } { idx := i } { memory := write(memory, mv[idx], pv) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ val := 7 ‖ b := freshId(addM(memory, Basket)) ‖ pv := 7 ‖
            mv := read(addM(memory, Basket), freshId(addM(memory, Basket)).items) ‖ idx := 2 ‖
            memory := write(addM(memory, Basket), read(addM(memory, Basket), freshId(addM(memory, Basket)).items)[2], 7) }
          φ } := by
  sol_chain
#last_line valueWrite

/-- `Token memory tk = b.tokens[i];` with `i` 2, for the printed `Token memory tok = carol.account.tokens[i];`
(`TokenBucket memory b` for `carol.account`): the declaration dropped, the receiver bound (`mv`), its
declaration dropped, then the element read — the paper's three `⇝` and its `⇝*`.  The reads stay, as in
`valueWrite`. -/
theorem tokenRead :
    dl![m]{
      { i := 2 ‖ b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
        ⟨[ Token memory tk = b.tokens[i]; ]⟩ φ }
    ~[memoryLocalDeclInitDrop]~> dl![m]{
        { i := 2 ‖ b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) } ⟨[ tk = b.tokens[i]; ]⟩ φ }
    ~[memoryIndexRead_unfold_rightFst]~> dl![m]{
        { i := 2 ‖ b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
          ⟨[ Token[] memory mv = b.tokens; tk = mv[i]; ]⟩ φ }
    ~[memoryLocalDeclInitDrop]~> dl![m]{
        { i := 2 ‖ b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
          ⟨[ mv = b.tokens; tk = mv[i]; ]⟩ φ }
    ~*> dl![m]{
        { i := 2 ‖ b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) }
          { mv := read(memory, b.tokens) } { tk := read(memory, mv[i]) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { i := 2 ‖ b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) ‖
            mv := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
            tk :=
              read(addM(memory, TokenBucket), read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[2]) }
          φ } := by
  sol_chain
#last_line tokenRead

end

end ElementOfField

end Solidity.Examples.Chains.MemoryArrays
