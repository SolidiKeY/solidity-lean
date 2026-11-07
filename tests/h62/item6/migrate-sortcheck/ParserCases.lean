import Solidity.SortCheck.Parser

/-! Isolated finite scanner controls. These kernel examples check the named
computations; the guards check concrete rejection behavior. They do not prove
external-parser equivalence or replace SortFaithfulness. -/
namespace SortCheckMigrationCases
open Solidity Solidity.TacletAnnotations Solidity.KeyTacletParser

/-- Comments cannot introduce a read into a small Solidity taclet. -/
example : stripComments "a/* find<[int]>(storage,p) */b// read<[int]>(memory,p)\nc" = "ab\nc" := by
  decide +kernel

private def accepted (r : Except String TacletRead) : Option TacletRead :=
  match r with
  | .ok x => some x
  | .error _ => none

-- Scanner String suffix operations are checked executably, not asserted to
-- kernel-reduce. The annotation inventory below is kernel-reducible.
#guard accepted (abstractRead ⟨"case", [], [], []⟩ ⟨"find", "int", "storage,p"⟩) =
    some ⟨.storage, .value, .fixed .int⟩

/-- The Solidity annotation inventory retains all 131 frozen rows. -/
example : tacletReadAnns.length = 131 := by
  decide +kernel

private def parsed (reads : List ParsedRead) (vcs : List String := [])
    (unknown : List String := []) : ParsedTaclet := ⟨"case", vcs, reads, unknown⟩
private def sint : TacletRead := ⟨.storage, .value, .fixed .int⟩
private def mint : TacletRead := ⟨.memory, .value, .fixed .int⟩
private def findInt : ParsedRead := ⟨"find", "int", "storage,p"⟩
private def readInt : ParsedRead := ⟨"read", "int", "memory,p"⟩
private def ann (reads : List TacletRead) : TacletReadAnn := ⟨"case", reads⟩

#guard (scanReads "/* textual scanner input */ find<[int]>(storage, p)").1 = [findInt]
#guard ((parseKeyFile "\\rules {\ncase {\n// find<[int]>(storage,p)\n}\n}").map (·.reads)) = [[]]
#guard (scanReads "mystery<[int]>(storage,p)").2 = ["mystery<[int"]
#guard scanVarconds "\\hasSort(p) \\hasSort(p) \\hasMemoryFieldSort(p)" = ["hasSort", "hasMemoryFieldSort"]
#guard accepted (abstractRead (parsed []) ⟨"find", "notASort", "storage,p"⟩) = none
#guard accepted (abstractRead (parsed []) ⟨"find", "alpha", "storage,p"⟩) = none
#guard accepted (abstractRead (parsed [] ["hasSort", "hasFieldSort"]) ⟨"find", "alpha", "storage,p"⟩) = none
#guard accepted (abstractRead (parsed [] ["hasMemoryFieldSort"]) ⟨"read", "alphaPrim", "memory,p"⟩) =
  some ⟨.memory, .value, .generic .hasMemoryFieldSort⟩
#guard accepted (abstractRead (parsed []) ⟨"selectSt", "int", "net,at(a)"⟩) = some ⟨.net, .net, .fixed .int⟩
#guard accepted (abstractRead (parsed []) ⟨"find", "int", "storage,consr(p,size)"⟩) = some ⟨.storage, .length, .fixed .int⟩
#guard accepted (abstractRead (parsed []) ⟨"defaultValue", "Identity", ""⟩) = some ⟨.memory, .dflt, .fixed .identity⟩
#guard accepted (abstractRead (parsed []) ⟨"valAt", "", "storage,p"⟩) = some ⟨.storage, .value, .fixed .stValue⟩
#guard conforms [ann [sint, mint]] [parsed [readInt, findInt]] = []
#guard conforms [ann [sint, sint]] [parsed [findInt, readInt]] ≠ []
#guard conforms [ann [sint]] [parsed [findInt, findInt]] ≠ []
#guard conforms [ann [sint]] [] ≠ []
#guard conforms [] [parsed [findInt]] ≠ []
#guard conforms [] [parsed [] [] ["mystery<[int"]] ≠ []
#guard SortVarcond.render .hasMemoryElementSort = "hasMemoryElementSort"
#guard TacletRead.render mint = "memory/value/fixed int"
#guard tacletReadAnns.length = 131
#guard compoundOps.length = 5
#guard incDecOps.length = 4
end SortCheckMigrationCases
