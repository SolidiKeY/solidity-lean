import Solidity.Calculus.ExactReduction
import Solidity.Calculus.Surface

/-!
# Exact reduction certificates

An equality leaf has the same positive and negative reduction. A pending
program does not: the ordinary positive reducer's `false` fallback must not
be misreported as a counterexample to that program's formula.
-/

namespace Solidity.Examples.ExactReduction

open Solidity.Decide
open scoped Solidity.Scoped

def Bank : Contract := contract!{ mapping(uint => uint) balances; }
local instance : InContract := ⟨Bank⟩

def aliases : Fml Bank [] := dl!{ a == b → balances[a] == balances[b] }

def aliasesReduction : ExactReduction aliases :=
  (exactReduction? aliases).get (by decide +kernel)

/-- The exact leaf and its read-eliminated form keep the original meaning
in every typed initial state, including equal symbolic mapping keys. -/
example (σ : State Bank []) :
    aliasesReduction.leaf.elim.holds σ AEnv.dflt ↔ σ ⊧ aliases :=
  aliasesReduction.elim_holds_iff σ

example : (exactReduction? (dl!{ [ balances[3] = 7; ] balances[3] == 7 })).isNone = true := by
  decide +kernel

example : (exactReduction? (dl!{ { storage := storage } balances[3] == 7 })).isNone = true := by
  decide +kernel

/-- info: 'Solidity.Decide.ExactReduction.elim_holds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExactReduction.elim_holds_iff

end Solidity.Examples.ExactReduction
