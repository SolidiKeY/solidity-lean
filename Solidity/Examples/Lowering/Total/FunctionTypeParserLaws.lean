import Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws
import Solidity.Correctness.Lowering.Total.FunctionTypeDecode

/-! Checks of the function-signature parser laws. Every `fnParts?` equation
here is a kernel proof (`fnParts?_mk`, `fnParts?_fnTyStr`), none a `#guard`. -/
namespace Solidity.Examples.Lowering.Total.FunctionTypeParserLaws

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws
open Solidity.Correctness.Lowering.Total.FunctionTypeDecode (Part Parts part partsWith part_fn)

/-- A concrete spelling, decided through the list form of the parser. -/
theorem reads {s : String} {x : Option (List String × List String × Bool)}
    (h : partsL s.data = x) : fnParts? s = x := (fnParts?_mk s.data).trans h

/-! ## Empty and nonempty lists, both visibilities -/

example : fnParts? "function()" = some ([], [], false) := reads (by decide)
example : fnParts? "function()external" = some ([], [], true) := reads (by decide)
example : fnParts? "function(uint)returns(uint)" = some (["uint"], ["uint"], false) :=
  reads (by decide)
example : fnParts? "function(address,bool)externalreturns(bool,uint8)"
    = some (["address", "bool"], ["bool", "uint8"], true) := reads (by decide)

example (ext : Bool) : fnParts? (fnTyStr [] [] ext) = some ([], [], ext) :=
  fnParts?_fnTyStr ext (by simp) (by simp)
example (ext : Bool) : fnParts? (fnTyStr [] ["uint"] ext) = some ([], ["uint"], ext) :=
  fnParts?_fnTyStr ext (by simp) (by decide)
example (ext : Bool) :
    fnParts? (fnTyStr ["uint", "bytes4"] ["bool"] ext) = some (["uint", "bytes4"], ["bool"], ext) :=
  fnParts?_fnTyStr ext (by decide) (by decide)

/-! ## Nesting -/

/-- `function (function (uint8) returns (bool), bytes4) returns (uint8, uint)`. -/
example : fnParts? "function(function(uint8)returns(bool),bytes4)returns(uint8,uint)"
    = some (["function(uint8)returns(bool)", "bytes4"], ["uint8", "uint"], false) :=
  reads (by decide)

/-- Components that are themselves spellings, three levels here: a covered
signature reads back, and so does its first parameter. -/
example {ps rs qs : List String} (e₁ e₂ e₃ : Bool)
    (hp : ∀ p ∈ ps, Covered p) (hr : ∀ r ∈ rs, Covered r) (hq : ∀ q ∈ qs, Covered q) :
    fnParts? (fnTyStr [fnTyStr [fnTyStr ps rs e₁] qs e₂, "uint"] [fnTyStr qs ps e₃] e₁)
      = some ([fnTyStr [fnTyStr ps rs e₁] qs e₂, "uint"], [fnTyStr qs ps e₃], e₁)
    ∧ fnParts? (fnTyStr [fnTyStr ps rs e₁] qs e₂) = some ([fnTyStr ps rs e₁], qs, e₂) :=
  have inner : Covered (fnTyStr ps rs e₁) := .fn e₁ hp hr
  have mid : Covered (fnTyStr [fnTyStr ps rs e₁] qs e₂) :=
    .fn e₂ (by simpa using inner) hq
  ⟨fnParts?_covered e₁
      (by simpa using And.intro mid (Covered.name (s := "uint") (by decide) (by decide)))
      (by simpa using Covered.fn e₃ hq hp),
    fnParts?_covered e₂ (by simpa using inner) hq⟩

/-! ## Delimiters -/

/-- Commas and brackets inside a component's brackets are no boundary. -/
example : fnParts? "function(mapping(uint=>uint[2]),S[]memory)returns(function(uint,uint))"
    = some (["mapping(uint=>uint[2])", "S[]memory"], ["function(uint,uint)"], false) :=
  reads (by decide)

example : Well "mapping(uint=>function(uint,bool)external)" := by decide
example : Covered ("uint" ++ "[" ++ "2" ++ "]" ++ "memory") :=
  .suffix (.index (.name (by decide) (by decide)) (by decide)) (by decide)

/-- A location or array suffix after any covered component. -/
example (ext : Bool) {c : String} (h : Covered c) :
    fnParts? (fnTyStr [c ++ "[" ++ "" ++ "]" ++ "storage"] [c ++ "calldata"] ext)
      = some ([c ++ "[" ++ "" ++ "]" ++ "storage"], [c ++ "calldata"], ext) :=
  fnParts?_covered ext (by simpa using (h.index (n := "") (by decide)).suffix (t := "storage") (by decide))
    (by simpa using h.suffix (t := "calldata") (by decide))

example : splitTopCommas "f(a,b),g[1,2],{x,y}" = ["f(a,b)", "g[1,2]", "{x,y}"] :=
  (splitTopCommas_mk _).trans (by decide)
example {cs : List String} (h : ∀ c ∈ cs, SplitOk c) : splitTopCommas (",".intercalate cs) = cs :=
  splitTopCommas_intercalate h

/-- On covered components two signatures with one spelling are equal. -/
example {ps ps' : List String} {e e' : Bool} (h : ∀ p ∈ ps, Covered p) (h' : ∀ p ∈ ps', Covered p)
    (same : fnTyStr ps [] e = fnTyStr ps' [] e') : ps = ps' ∧ e = e' :=
  have r := fnTyStr_inj (fun p m => (h p m).well) (by simp) (fun p m => (h' p m).well) (by simp) same
  ⟨r.1, r.2.2⟩

/-! ## With the decoder's reader -/

/-- `part_fn`'s hypothesis discharged: a spelled signature reads as its
components read (the reader's fuel and its trees stay the decoder's). -/
example (n : Nat) {ps rs : List String} (ext : Bool)
    (hp : ∀ p ∈ ps, Well p) (hr : ∀ r ∈ rs, SplitOk r) :
    part (n + 1) (fnTyStr ps rs ext) = (partsWith (part n) ps).bind fun P =>
      (partsWith (part n) rs).map fun R => .fn ext () P R :=
  part_fn n (fnParts?_fnTyStr ext hp hr)

/-- A function-type tree's spelling splits into its components' spellings when
those are `Well`: a condition on the strings, not a property of every tree. -/
example {α : Type} (ext : Bool) (a : α) (P R : Parts α)
    (hp : ∀ p ∈ P.spells, Well p) (hr : ∀ r ∈ R.spells, SplitOk r) :
    fnParts? (Part.fn ext a P R).spell = some (P.spells, R.spells, ext) :=
  fnParts?_fnTyStr ext hp hr

/-! ## Refused, ambiguous and uncovered spellings -/

example : fnParts? "uint" = none := reads (by decide)
example : fnParts? "function(uint" = none := reads (by decide)
example : fnParts? "function(uint)returns(uint" = none := reads (by decide)
/-- Text written with a mutability or with `internal` is refused. -/
example : fnParts? "function(uint)view" = none ∧ fnParts? "function(uint)internal" = none :=
  ⟨reads (by decide), reads (by decide)⟩
/-- A function type that continues is no function-type spelling. -/
example : fnParts? "function(uint)[]memory" = none := reads (by decide)

/-- A lone empty component is not read back. -/
example : ¬ SplitOk "" := by decide
example : fnParts? (fnTyStr [""] ["uint"] false) = some ([], ["uint"], false) := reads (by decide)
example : fnParts? (fnTyStr ["uint"] [""] true) = some (["uint"], [], true) := reads (by decide)

/-- A comma at a component's own depth: one spelling, two signatures. -/
example : ¬ SplitOk "a,b" := by decide
example : fnTyStr ["a,b"] [] false = fnTyStr ["a", "b"] [] false := by decide
example : fnParts? (fnTyStr ["a,b"] [] false) = some (["a", "b"], [], false) := reads (by decide)

/-- A component closing below its depth ends the parameters early. -/
example : ¬ CloseOk "a)" ∧ ¬ CloseOk "uint]" ∧ ¬ SplitOk "x}" := by decide
example : fnParts? (fnTyStr ["a)returns(b"] [] false) = some (["a"], ["b"], false) :=
  reads (by decide)
example : fnParts? (fnTyStr ["a)"] [] false) = none := reads (by decide)
/-- A component leaving a bracket open swallows the closing `)`; components can merge. -/
example : ¬ Well "a(" := by decide
example : fnParts? (fnTyStr ["a("] ["uint"] true) = none := reads (by decide)
/-- `close` does not count braces, `splitTop` does: `SplitOk` and `CloseOk` differ. -/
example : CloseOk "{" ∧ ¬ SplitOk "{" := by decide
example : fnParts? (fnTyStr ["{", "}"] [] false) = some (["{,}"], [], false) := reads (by decide)

end Solidity.Examples.Lowering.Total.FunctionTypeParserLaws
