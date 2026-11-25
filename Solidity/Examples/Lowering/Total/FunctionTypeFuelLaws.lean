import Solidity.Correctness.Lowering.Total.FunctionTypeFuelLaws

/-! Checks of the function-type reader's fuel laws: nested readings, too little
and more fuel on concrete spellings by `#guard` (`fnParts?` does not reduce in
the kernel), and the laws applied to trees under explicit `fnParts?` and leaf
hypotheses. -/
namespace Solidity.Examples.Lowering.Total.FunctionTypeFuelLaws

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.FunctionTypeDecode

def u256 : Source.Elem := .int false 256 (by decide)
def u8 : Source.Elem := .int false 8 (by decide)
def one {α : Type} (c : Part α) : Parts α := .cons c .nil

/-! ## Nested readings, too little fuel and more fuel -/

/-- `function (function (function (uint8)) external) returns (uint)`: three nested
function types over a leaf, depth 4. -/
def deep : Part Unit :=
  .fn false () (one (.fn true () (one (.fn false () (one (.elem u8)) .nil)) .nil))
    (one (.elem u256))
def deepS : String := "function(function(function(uint8))external)returns(uint)"

#guard deep.depth == 4 && deep.spell == deepS
#guard readSig deepS == some deep
-- Too little fuel: one per nesting level, the leaf included.
#guard (List.range 4).all fun n => part n deepS == none
-- From the depth on, and with any more fuel, the same tree.
#guard part 4 deepS == some deep && part 5 deepS == some deep && part 40 deepS == some deep
#guard part (deepS.length + 1) deepS == some deep
-- A leaf reads at fuel 1; a flat signature at fuel 2.
#guard part 0 "uint8" == none && part 1 "uint8" == some (.elem u8)
#guard part 1 "function(uint)" == none && part 2 "function(uint)" == some (.fn false () (one (.elem u256)) .nil)

/-! ## Refusal, at any depth and any fuel -/

-- A nested marker `fnParts?` refuses (`returns` without parentheses).
#guard (fnParts? "function()returnsuint").isNone
#guard (List.range 8).all fun n => part n "function(function()returnsuint,uint)" == none
#guard readSig "function(uint)returns(function()returnsuint)" == none

/-! ## The laws on trees, under explicit hypotheses -/

example {s : String} {p : Part Unit} (h : part 3 s = some p) : part 10 s = some p :=
  part_mono h (by decide)

example {s : String} {p : Part Unit} (h : readSig s = some p) : part (s.length + 5) s = some p :=
  readSig_part h (by omega)

/-- A malformed nested return refuses its parent at every fuel. -/
example {s c d : String} (isFn : fnTy? c = true) (bad : fnParts? c = none)
    (parts : fnParts? s = some ([d], [c], true)) (n : Nat) : part n s = none :=
  part_refused (.ret parts (List.mem_singleton.2 rfl) (.malformed isFn bad)) n

/-- `deep`'s shape at abstract spellings: the hypotheses are its two nested
`fnParts?` splits, the outer one, and its two leaves' readings. -/
theorem deep_splits {s m i a b : String}
    (outer : fnParts? s = some ([m], [b], false)) (mid : fnParts? m = some ([i], [], true))
    (inner : fnParts? i = some ([a], [], false))
    (ha : fnTy? a = false) (la : leaf a = .elem u8) (hb : fnTy? b = false)
    (lb : leaf b = .elem u256) : deep.Splits s :=
  ⟨[m], [b], outer, ⟨m, [], rfl, ⟨[i], [], mid, ⟨i, [], rfl,
    ⟨[a], [], inner, ⟨a, [], rfl, ⟨ha, la⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩,
    ⟨b, [], rfl, ⟨hb, lb⟩, rfl⟩⟩

/-- Under those hypotheses: read exactly from fuel 4 on, nothing below. -/
example {s m i a b : String}
    (outer : fnParts? s = some ([m], [b], false)) (mid : fnParts? m = some ([i], [], true))
    (inner : fnParts? i = some ([a], [], false))
    (ha : fnTy? a = false) (la : leaf a = .elem u8) (hb : fnTy? b = false)
    (lb : leaf b = .elem u256) :
    part 3 s = none ∧ part 4 s = some deep ∧ part 7 s = some deep :=
  have h := deep_splits outer mid inner ha la hb lb
  ⟨part_lt_depth deep h (by decide), part_of_splits deep h (by decide),
    part_of_splits deep h (by decide)⟩

/-- Annotations are erased: a tree annotated with mutabilities reads back as
its erasure, at `readSig`'s fuel, when its own spelling splits as itself. -/
example (ps rs : Parts Ann) (a : Ann)
    (h : (Part.fn true a ps rs).Splits (Part.fn true a ps rs).spell) :
    readSig (Part.fn true a ps rs).spell = some (.fn true () ps.erase rs.erase) :=
  readSig_spell h

-- The bound holds for every tree, including empty leaf spellings.
example : (Part.named "" : Part Unit).depth ≤ (Part.named "" : Part Unit).spell.length + 1 :=
  Part.depth_le_spell _
example : deep.depth ≤ deepS.length + 1 := Part.depth_le_spell deep

end Solidity.Examples.Lowering.Total.FunctionTypeFuelLaws
