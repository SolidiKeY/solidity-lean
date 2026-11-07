import Solidity.Calculus.ReadBoundsStackCorrect

/-! Guards H126 ReadBounds traversal against stack growth, budget drift and
accidental DAG counting. General kernel equalities cover every intrinsic term
and formula; finite samples here check exact remaining fuel and deep compiled
paths at the existing 24,000/96,000 limits. These are not source/compiler/native
preservation proofs or acceptance of the historical browser/performance STOPs. -/
namespace ReadBoundsStackControls
open Solidity Solidity.Decide
private def C : Contract := { vars := [] }
private def atom : LTm C (.val .uint) := .var 0
private def flag : LTm C (.val .bool) := .var 0
private def termChain (depth : Nat) (left : Bool) : LTm C (.val .uint) :=
  (List.range depth).foldl (fun t _ => if left then .seq t atom else .seq atom t) atom
private def formulaChain (depth : Nat) (quantified : Bool) : LFml C :=
  (List.range depth).foldl (fun φ i => if quantified then .all i .bool φ else .not φ) .tt
private def sharedFormula (depth : Nat) : LFml C :=
  (List.range depth).foldl (fun φ _ => .and φ φ) .tt
private def fuels (nodes : Nat) : List Nat :=
  if nodes < concreteSize then [nodes - 1, nodes, nodes + 1] else [nodes - 1, nodes]
private def expected (nodes fuel : Nat) : Option Nat :=
  if nodes ≤ fuel then some (fuel - nodes) else none
private def checkTerm (name : String) {s : Srt} (t : LTm C s) (nodes : Nat) : IO Unit := do
  for fuel in fuels nodes do
    let want := expected nodes fuel
    unless t.fitsStack fuel == want && t.fitsM fuel == want && t.fits fuel == want do
      throw (IO.userError s!"term {name}: fuel={fuel} expected={want}")
    IO.println s!"READ_BOUNDS term {name} nodes={nodes} fuel={fuel}: {want}"
private def checkFormula (name : String) (φ : LFml C) (nodes : Nat) : IO Unit := do
  for fuel in fuels nodes do
    let want := expected nodes fuel
    unless φ.fitsStack fuel == want && φ.fitsM fuel == want && φ.fits fuel == want do
      throw (IO.userError s!"formula {name}: fuel={fuel} expected={want}")
    IO.println s!"READ_BOUNDS formula {name} nodes={nodes} fuel={fuel}: {want}"
#guard normalizationSize == 24000 && normalizationDepth == 12 &&
  concreteSize == 96000 && concreteDepth == 40
#eval show IO Unit from do
  checkTerm "leaf" atom 1
  checkTerm "error" (.err : LTm C (.val .uint)) 1
  checkTerm "sequence" (.seq flag atom) 3
  checkTerm "alternative" (.orElse atom atom) 3
  checkTerm "kite" (.kite flag flag atom atom) 5
  checkFormula "truth" .tt 1
  checkFormula "equality" (.eq atom atom) 3
  checkFormula "negation" (.not .tt) 2
  checkFormula "conjunction" (.and .tt .tt) 3
  checkFormula "implication" (.imp (.eq atom atom) .tt) 5
  checkFormula "quantifier" (.all 0 .uint .tt) 2
  checkTerm "left-normal" (termChain 11999 true) 23999
  checkTerm "right-concrete" (termChain 47999 false) 95999
  checkFormula "not-normal" (formulaChain 23999 false) normalizationSize
  checkFormula "all-concrete" (formulaChain 95999 true) concreteSize
  checkFormula "shared-small" (sharedFormula 12) 8191
  let large := sharedFormula 16
  unless large.fitsStack concreteSize == none && large.fitsM concreteSize == none &&
      large.fits concreteSize == none do throw (IO.userError "shared DAG counted only once")
  IO.println "READ_BOUNDS shared-large: refused at unchanged96000tree budget"
#print axioms LTm.fits_eq_fitsM
#print axioms LFml.fits_eq_fitsM
#print axioms LTm.fitsM_eq_fitsStack
#print axioms LFml.fitsM_eq_fitsStack
end ReadBoundsStackControls
