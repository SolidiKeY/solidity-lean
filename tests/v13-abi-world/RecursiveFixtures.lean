import Solidity.Backend.AbiWorld.RecursiveEntry
import tests.«v13-abi-world».NestedByteFixtures

namespace Solidity.Backend.AbiWorld.RecursiveControls
open AbiEntry RecursiveLayout
abbrev U : AbiEntry.Shape := .word (.uint 256)
abbrev Row : AbiEntry.Shape := .tuple [U,.fixed U 2,.bytes]
def w (n : Nat) (h : n < W) : AbiEntry.Val U := .word ⟨n,h,by exact decide_eq_true (show n < 2 ^ 256 from h)⟩
def pair : Seq U 2 := .cons (w 7 (by decide +kernel)) (.cons (w 11 (by decide +kernel)) .nil)
def row (bs : List UInt8) : AbiEntry.Val Row := .tuple (.cons (w 300 (by decide +kernel)) (.cons (.fixed pair) (.cons (.bytes bs) .nil)))
def rows : Seq Row 2 := .cons (row []) (.cons (row ((List.range 33).map UInt8.ofNat)) .nil)
def ps (loc : AbiEntry.Loc) : List Param :=
  [{shape := .array Row,loc},{shape := .fixed (.fixed U 2) 2,loc := .memory},
   {shape := .bytes,loc},{shape := .word .bool,loc := .value}]
def vals (loc : AbiEntry.Loc) : Vals ((ps loc).map Param.shape) :=
  .cons (.array rows) (.cons (.fixed (.cons (.fixed pair) (.cons (.fixed pair) .nil)))
    (.cons (.bytes [0,255]) (.cons (.word UniformWordControls.b1) .nil)))
def sel : List UInt8 := [9,8,7,6]
def post : List UInt8 := List.replicate 32 0 ++ [255,0,42]
def sample (loc : AbiEntry.Loc) : Input := RecursiveEntry.input (ps loc) (vals loc) sel post 128

theorem typed (loc : AbiEntry.Loc) : ∃ es : Entries (ps loc),
    enter (sample loc) 14 (ps loc) 0 0 = .ok (es,RecursiveEntry.spent (ps loc) (vals loc)) ∧
    entry (sample loc) 14 (ps loc) = .ok es ∧
    bodyValues (sample loc) 14 (ps loc) es 0 = .ok (vals loc) ∧
    verdict (sample loc) 14 (ps loc) = .run (vals loc) ∧ 4 + headsOf (ps loc) ≤ lim := by
  apply RecursiveEntry.roundtrip (ps loc) (vals loc) sel post 128 14
  · decide +kernel
  · decide +kernel
  · cases loc <;>
      simp only [RecursiveEntry.input,Input.size,List.length_append,encodeArgs,vals,ps,rows,row,pair,w,
        Val.enc,Vals.parts,Seq.parts,assemble_length,heads,List.foldr_cons,List.foldr_nil,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        Shape.dynamic,Shape.headSize,List.any_cons,List.any_nil,
        Bool.false_or,Bool.or_false,Bool.true_or,ite_true,ite_false,Bool.false_eq_true,
        MixedPacket.word_length,List.length_nil,List.length_map,List.length_range,
        sel,post,List.length_cons,List.length_replicate]
      <;> decide +kernel
  · cases loc <;> decide +kernel
  · cases loc <;> decide +kernel

/-- info: 'Solidity.Backend.AbiWorld.RecursiveEntry.roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RecursiveEntry.roundtrip
/-- info: 'Solidity.Backend.AbiWorld.RecursiveReadback.value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RecursiveReadback.value
/-- info: 'Solidity.Backend.AbiWorld.RecursiveControls.typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typed
end Solidity.Backend.AbiWorld.RecursiveControls
