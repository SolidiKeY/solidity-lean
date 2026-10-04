import Solidity.Calculus.Chains
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# Memory array examples as chains

The calculus's worked memory-array examples, as `calc`s of formulas
`dl![m]{ … }` for every modality `m` and postcondition `φ` (conventions of
`Chains/Memory.lean`: printed `⇝` is `~[r]~>`, printed `⇝*` is `~*>`; an array the
printed trace does not declare is bound by the update its declaration leaves).

* An index read or write takes no bounds branch here: an index out of range halts
  the read (or reverts the write) by itself, where the printed trace splits on
  `0 ≤ i < ℓ`; its `⊤`/`⊥` branches are not drawn.
* A nonsimple index is captured by the elaborator (`uint idx; idx = ++i;`), and the
  receiver of `carolValues[++i] = …` is not re-aliased (the printed `mv1`), since no
  operand here rebinds a local.
* `Account` has no `tokens` or `values` here: `TokenBucket`'s `tokens` and
  `Basket`'s `items` (`TestSuite`) stand for `carol.account.tokens` and
  `carol.account.values`, one selector shorter, and `tk` for `tok` (a state variable
  there).
* The fixed-size array is the declaration and two statements; the printed reads of
  its length and elements are term laws with no rewrite link yet, so not drawn.
* A line that reads or writes by a captured index (`carolValues[idx]`) is crossed
  unwritten, the next written line being its merge, which resolves the index
  (`carolValues[i + 1]`) as the printed line does.
* Every chain ends merged with the update its declaration leaves
  (`~[sequentialToParallel]~>`), `#last_line` after it; a read of an element of
  a fresh array stays as it is, since no law reads one.
-/

namespace Solidity.Examples.Chains.MemoryArrays

local instance : InContract := ⟨StandardExample⟩

/-! ## Example: Index Read and Write on a Memory Array -/

namespace IndexRead

/-- `v = carolValues[i];` — read out of the heap at the index. -/
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ v = carolValues[i]; ]⟩ φ }
    ~~> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) ‖
          v := read(addM(memory, uint[]), freshId(addM(memory, uint[]))[i]) } φ } :=
  calc dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ v = carolValues[i]; ]⟩ φ }
    _ ~*> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { v := read(memory, carolValues[i]) } φ } := by sol_chain

    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line chain
end IndexRead

namespace IndexWrite

/-- `carolValues[i] = 100;` — written into the heap at the index. -/
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ carolValues[i] = 100; ]⟩ φ }
    ~~> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖
          memory := write(addM(memory, uint[]), freshId(addM(memory, uint[]))[i], 100) } φ } :=
  calc dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ carolValues[i] = 100; ]⟩ φ }
    _ ~*> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { memory := write(memory, carolValues[i], 100) } φ } := by sol_chain

    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line chain
end IndexWrite

/-! ## Example: A Fixed-Size Memory Array -/

namespace FixedArray

/-- `uint[3] memory x; x[1] = 5;` — the declaration tags the fresh root with the
shape of `uint[3]` (`addM(memory, uint[3])`), which holds the length; the write is
an element write. -/
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ ⟨[ uint[3] memory x; x[1] = 5; ]⟩ φ }
    ~~> dl![m]{ { x := freshId(addM(memory, uint[3])) ‖
          memory := write(addM(memory, uint[3]), freshId(addM(memory, uint[3]))[1], 5) } φ } :=
  calc dl![m]{ ⟨[ uint[3] memory x; x[1] = 5; ]⟩ φ }
    _ ~[memoryReferenceDeclFreshAlloc]~>
        dl![m]{ { x := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
                ⟨[ x[1] = 5; ]⟩ φ } := by sol_chain
    _ ~*>
        dl![m]{ { x := freshId(addM(memory, uint[3])) ‖ memory := addM(memory, uint[3]) }
                { memory := write(memory, x[1], 5) } φ } := by sol_chain

    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line chain
end FixedArray

/-! ## Example: Additional Memory Array Cases -/

namespace IndexReadCaptured

/-- `idx`, the captured index. -/
def names : FreshTable := [("idx", "se1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `v = carolValues[++i];` — the index captured, then read at: the read by the
captured index is crossed unwritten, the merge resolves it to `carolValues[i + 1]`,
and the dead `idx := 0` goes. -/
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ v = carolValues[++i]; ]⟩ φ }
    ~~> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) ‖
          i := i + 1 ‖ idx := i + 1 ‖
          v := read(addM(memory, uint[]), freshId(addM(memory, uint[]))[i + 1]) } φ } :=
  calc dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ v = carolValues[++i]; ]⟩ φ }
    _ = dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ uint idx; idx = ++i; v = carolValues[idx]; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
                  ⟨[ v = carolValues[idx]; ]⟩ φ } := by sol_chain
    _ ~[memoryIndexReadHeap]~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { idx := 0 } { i := i + 1 ‖ idx := i + 1 ‖ v := read(memory, carolValues[i + 1]) } φ } := by
      sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { idx := 0 ‖ i := i + 1 ‖ idx := i + 1 ‖ v := read(memory, carolValues[i + 1]) } φ } := by
      sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { i := i + 1 ‖ idx := i + 1 ‖ v := read(memory, carolValues[i + 1]) } φ } := by sol_chain

    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line chain
end IndexReadCaptured

namespace IndexWriteCaptured

/-- `pv`, the snapshot of the right-hand side, and `idx`, the captured index. -/
def names : FreshTable := [("pv", "se1"), ("idx", "se2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `carolValues[++i] = val;` — the right-hand side is snapshot before the index
runs; the receiver, simple, is not re-aliased (no `mv1`).  The write by the captured
index is crossed unwritten; the merge resolves it to `carolValues[i + 1]` and the
value to `val`, and the dead `idx := 0` goes. -/
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ carolValues[++i] = val; ]⟩ φ }
    ~~> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ pv := val ‖ i := i + 1 ‖ idx := i + 1 ‖
          memory := write(addM(memory, uint[]), freshId(addM(memory, uint[]))[i + 1], val) } φ } :=
  calc dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ carolValues[++i] = val; ]⟩ φ }
    _ = dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ uint pv = val; uint idx; idx = ++i; carolValues[idx] = pv; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { pv := val } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
                  ⟨[ carolValues[idx] = pv; ]⟩ φ } := by sol_chain
    _ ~[memoryIndexWriteStore]~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { pv := val } { idx := 0 }
                { i := i + 1 ‖ idx := i + 1 ‖ memory := write(memory, carolValues[i + 1], pv) } φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { pv := val }
                { idx := 0 ‖ i := i + 1 ‖ idx := i + 1 ‖ memory := write(memory, carolValues[i + 1], pv) } φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { pv := val ‖ idx := 0 ‖ i := i + 1 ‖ idx := i + 1 ‖ memory := write(memory, carolValues[i + 1], val) } φ } := by
      sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { pv := val ‖ i := i + 1 ‖ idx := i + 1 ‖ memory := write(memory, carolValues[i + 1], val) } φ } := by
      sol_chain

    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line chain
end IndexWriteCaptured

namespace ElementFromField

/-- `acc`, the alias of `david.account`. -/
def names : FreshTable := [("acc", "mv1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `carolTokens[i] = david.account.token;` — the source's receiver is bound
(`acc`), and the element is written with the identity the member holds (the printed
`tok` is not declared). -/
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) }
            { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            ⟨[ carolTokens[i] = david.account.token; ]⟩ φ }
    ~~> dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖
          david := freshId(addM(addM(memory, Token[]), Person)) ‖
          acc := read(addM(addM(memory, Token[]), Person), freshId(addM(addM(memory, Token[]), Person)).account) ‖
          memory :=
            write(addM(addM(memory, Token[]), Person), freshId(addM(memory, Token[]))[i],
              read(addM(addM(memory, Token[]), Person),
                read(addM(addM(memory, Token[]), Person),
                  freshId(addM(addM(memory, Token[]), Person)).account).token)) } φ } :=
  calc dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) }
               { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               ⟨[ carolTokens[i] = david.account.token; ]⟩ φ }
    _ ~[memoryFieldRead_unfold_rightFst]~>
        dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) }
                { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                ⟨[ Account memory acc = david.account; carolTokens[i] = acc.token; ]⟩ φ } := by
      sol_chain
    _ ~*> dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) }
                  { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { acc := read(memory, david.account) } ⟨[ carolTokens[i] = acc.token; ]⟩ φ } := by
      sol_chain
    _ ~*>
        dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) }
                { david := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { acc := read(memory, david.account) }
                { memory := write(memory, carolTokens[i], read(memory, acc.token)) } φ } := by sol_chain

    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line chain
end ElementFromField

namespace FieldFromElement

/-- `mv`, the alias of `carol.account`. -/
def names : FreshTable := [("mv", "mv1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `carol.account.token = davidTokens[i];` — the target's receiver is bound
(`mv`), and the member is written with the element's identity (the printed `tok`
is not declared). -/
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
            { davidTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) }
            ⟨[ carol.account.token = davidTokens[i]; ]⟩ φ }
    ~~> dl![m]{ { carol := freshId(addM(memory, Person)) ‖
          davidTokens := freshId(addM(addM(memory, Person), Token[])) ‖
          mv := read(addM(memory, Person), freshId(addM(memory, Person)).account) ‖
          memory :=
            write(addM(addM(memory, Person), Token[]),
              read(addM(memory, Person), freshId(addM(memory, Person)).account).token,
              read(addM(addM(memory, Person), Token[]), freshId(addM(addM(memory, Person), Token[]))[i])) } φ } :=
  calc dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
               { davidTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) }
               ⟨[ carol.account.token = davidTokens[i]; ]⟩ φ }
    _ ~[memoryFieldWrite_unfold_leftFst]~>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { davidTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) }
                ⟨[ Account memory mv = carol.account; mv.token = davidTokens[i]; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                  { davidTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) }
                  { mv := read(memory, carol.account) } ⟨[ mv.token = davidTokens[i]; ]⟩ φ } := by
      sol_chain
    _ ~*>
        dl![m]{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
                { davidTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) }
                { mv := read(memory, carol.account) }
                { memory := write(memory, mv.token, read(memory, davidTokens[i])) } φ } := by sol_chain

    _ ~[sequentialToParallel]~> _ := by sol_chain
    _ ~[readAddDifferentIdentity]~> _ := by sol_chain
#last_line chain
end FieldFromElement

namespace ElementAlias

/-- `idx`, the captured index. -/
def names : FreshTable := [("idx", "se1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-- `Token memory tok = carolTokens[++i];` — the index captured, the
declaration dropped, and `tok` bound to the element's identity: the bind by the
captured index is crossed unwritten, the merge resolves it to `carolTokens[i + 1]`,
and the dead `idx := 0` goes. -/
theorem chain (m : Modality) (φ : Post StandardExample) :
    dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } ⟨[ Token memory tok = carolTokens[++i]; ]⟩ φ }
    ~~> dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) ‖
          i := i + 1 ‖ idx := i + 1 ‖
          tok := read(addM(memory, Token[]), freshId(addM(memory, Token[]))[i + 1]) } φ } :=
  calc dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } ⟨[ Token memory tok = carolTokens[++i]; ]⟩ φ }
    _ = dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } ⟨[ uint idx; idx = ++i; Token memory tok = carolTokens[idx]; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
                  ⟨[ Token memory tok = carolTokens[idx]; ]⟩ φ } := by sol_chain
    _ ~[memoryLocalDeclInitDrop]~>
        dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { idx := 0 } { i := i + 1 ‖ idx := i + 1 }
                ⟨[ tok = carolTokens[idx]; ]⟩ φ } := rfl
    _ ~[memoryIndexReadAliasRoot]~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { idx := 0 } { i := i + 1 ‖ idx := i + 1 ‖ tok := read(memory, carolTokens[i + 1]) } φ } := by
      sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { idx := 0 ‖ i := i + 1 ‖ idx := i + 1 ‖ tok := read(memory, carolTokens[i + 1]) } φ } := by
      sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { carolTokens := freshId(addM(memory, Token[])) ‖ memory := addM(memory, Token[]) } { i := i + 1 ‖ idx := i + 1 ‖ tok := read(memory, carolTokens[i + 1]) } φ } := by sol_chain

    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line chain
end ElementAlias

namespace CallValue

/-- `makeValue()` reads a state variable: its value is symbolic. -/
def Calls : Contract := contract!{
  uint seed; uint[] values;
  function makeValue() returns (uint) { return seed; }
}

local instance : InContract := ⟨Calls⟩

/-- `pv`, the call's value, and `idx`, the captured index. -/
def names : FreshTable := [("pv", "se1"), ("idx", "se3")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Calls names).isEmpty

/-- `carolValues[++i] = makeValue();` — the call is captured before the index
(solc's order), inlined (`makeValue`'s result `se2`, the printed `makeValue()`), and
the element written.  The receiver is not re-aliased, as the printed first line does
with `mv1`.  The stack binds `pv` to the callee's local and writes by the captured
index, so it is crossed unwritten; the merge resolves both, and the dead captures go. -/
theorem incrementIndex (m : Modality) (φ : Post Calls) :
    dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ carolValues[++i] = makeValue(); ]⟩ φ }
    ~~> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ se2 := select(storage, seed) ‖
          pv := select(storage, seed) ‖ i := i + 1 ‖ idx := i + 1 ‖
          memory := write(addM(memory, uint[]), freshId(addM(memory, uint[]))[i + 1], select(storage, seed)) } φ } :=
  calc dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ carolValues[++i] = makeValue(); ]⟩ φ }
    _ = dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ uint pv = makeValue(); carolValues[++i] = pv; ]⟩ φ } := rfl
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { pv := 0 ‖ se2 := 0 ‖ se2 := select(storage, seed) ‖ pv := select(storage, seed) ‖ idx := 0 ‖
                  i := i + 1 ‖ idx := i + 1 ‖ memory := write(memory, carolValues[i + 1], select(storage, seed)) } φ } := by
      sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { se2 := select(storage, seed) ‖ pv := select(storage, seed) ‖ i := i + 1 ‖ idx := i + 1 ‖
                  memory := write(memory, carolValues[i + 1], select(storage, seed)) } φ } := by sol_chain
    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line incrementIndex

/-- `carolValues[i] = makeValue();` — the call captured, inlined, and written; the
stack (`pv` bound to the callee's local) crossed unwritten, merged, the dead
captures gone. -/
theorem simpleIndex (m : Modality) (φ : Post Calls) :
    dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ carolValues[i] = makeValue(); ]⟩ φ }
    ~~> dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ se2 := select(storage, seed) ‖
          pv := select(storage, seed) ‖
          memory := write(addM(memory, uint[]), freshId(addM(memory, uint[]))[i], select(storage, seed)) } φ } :=
  calc dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ carolValues[i] = makeValue(); ]⟩ φ }
    _ = dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } ⟨[ uint pv = makeValue(); carolValues[i] = pv; ]⟩ φ } := rfl
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { pv := 0 ‖ se2 := 0 ‖ se2 := select(storage, seed) ‖ pv := select(storage, seed) ‖
                  memory := write(memory, carolValues[i], select(storage, seed)) } φ } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { carolValues := freshId(addM(memory, uint[])) ‖ memory := addM(memory, uint[]) } { se2 := select(storage, seed) ‖ pv := select(storage, seed) ‖
                  memory := write(memory, carolValues[i], select(storage, seed)) } φ } := by sol_chain

    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line simpleIndex
end CallValue

namespace ElementOfField

local instance : InContract := ⟨TestSuite⟩

/-- `pv` the right-hand side, `mv` the receiver, `idx` the index. -/
def names : FreshTable := [("pv", "se1"), ("mv", "mv1"), ("idx", "ie1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes TestSuite names).isEmpty

/-- `b.items[i] = val;`, for the printed `carol.account.values[i] = val;`
(`Basket memory b` for `carol.account`) — the right-hand side, the receiver and the
index are each bound, and the element is written; the write by the captured index
is crossed unwritten, and its merge with the capture resolves it to `mv[i]`. -/
theorem valueWrite (m : Modality) (φ : Post TestSuite) :
    dl![m]{ { b := freshId(addM(memory, Basket)) ‖ memory := addM(memory, Basket) } ⟨[ b.items[i] = val; ]⟩ φ }
    ~~> dl![m]{ { b := freshId(addM(memory, Basket)) ‖ pv := val ‖
          mv := read(addM(memory, Basket), freshId(addM(memory, Basket)).items) ‖ idx := i ‖
          memory :=
            write(addM(memory, Basket), read(addM(memory, Basket), freshId(addM(memory, Basket)).items)[i], val) } φ } :=
  calc dl![m]{ { b := freshId(addM(memory, Basket)) ‖ memory := addM(memory, Basket) } ⟨[ b.items[i] = val; ]⟩ φ }
    _ ~[memoryIndexWriteCaptureAllComplexRecv]~>
        dl![m]{ { b := freshId(addM(memory, Basket)) ‖ memory := addM(memory, Basket) } ⟨[ uint pv = val; uint[] memory mv = b.items; uint idx = i; mv[idx] = pv; ]⟩ φ } := by
      sol_chain
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { b := freshId(addM(memory, Basket)) ‖ memory := addM(memory, Basket) } { pv := val } { mv := read(memory, b.items) }
                { idx := i ‖ memory := write(memory, mv[i], pv) } φ } := by sol_chain
    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line valueWrite

/-- `Token memory tk = b.tokens[i];`, for the printed
`Token memory tok = carol.account.tokens[i];` (`TokenBucket memory b` for
`carol.account`) — the declaration dropped, the receiver bound (`mv`), then the
element read. -/
theorem tokenRead (m : Modality) (φ : Post TestSuite) :
    dl![m]{ { b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) } ⟨[ Token memory tk = b.tokens[i]; ]⟩ φ }
    ~~> dl![m]{ { b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) ‖
          mv := read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens) ‖
          tk := read(addM(memory, TokenBucket),
            read(addM(memory, TokenBucket), freshId(addM(memory, TokenBucket)).tokens)[i]) } φ } :=
  calc dl![m]{ { b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) } ⟨[ Token memory tk = b.tokens[i]; ]⟩ φ }
    _ ~[memoryLocalDeclInitDrop]~> dl![m]{ { b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) } ⟨[ tk = b.tokens[i]; ]⟩ φ } := by sol_chain
    _ ~[memoryIndexRead_unfold_rightFst]~>
        dl![m]{ { b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) } ⟨[ Token[] memory mv = b.tokens; tk = mv[i]; ]⟩ φ } := by sol_chain
    _ ~[memoryLocalDeclInitDrop]~> dl![m]{ { b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) } ⟨[ mv = b.tokens; tk = mv[i]; ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { b := freshId(addM(memory, TokenBucket)) ‖ memory := addM(memory, TokenBucket) } { mv := read(memory, b.tokens) } { tk := read(memory, mv[i]) } φ } := by
      sol_chain

    _ ~[sequentialToParallel]~> _ := by sol_chain
#last_line tokenRead
end ElementOfField

end Solidity.Examples.Chains.MemoryArrays
