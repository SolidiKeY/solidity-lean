import Solidity.Yul.Views.SourceBalanceReads
import Solidity.Source.MonetaryFit

/-!
# `BALANCE` is exact under BalancesFit

The actual evaluator's `BALANCE` of an instance returns `wordView` of its
exact Nat balance (`sourceBalanceLocal_run`).  Under the state invariant
`ExecState.BalancesFit` (`Source/MonetaryFit.lean`) that word *is* the
balance; without it a wide balance is observed modulo `2 ^ 256`
(`sourceBalanceLocal_wide`).
-/
namespace Solidity.Yul.Views


/-- **`BALANCE` returns the exact balance** of an instance on a fitting state. -/
theorem sourceBalanceLocal_exact {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.address false)) (address : Roadmap.Address)
    (localValue : s.1.get index = Source.Val.address address) (code : Nat)
    (found : (s.2.ex.world.accounts address).code = some code) (fit : s.2.ex.BalancesFit) :
    (Source.evalE G F (n+2) (sourceBalanceExpr index)).run s =
      (.ok (.val (uintValueOfWord E.layout
        ⟨(s.2.ex.world.accounts address).balance, fit.1 address⟩)), s) := by
  rw [sourceBalanceLocal_run G F n s index address localValue]
  have same : sourceObservedBalance G s address =
      ⟨(s.2.ex.world.accounts address).balance, fit.1 address⟩ :=
    Fin.ext (sourceObservedBalance_system_exact G s address code found (fit.1 address))
  rw [same]

/-- The same, read as an integer: the returned `uint256` is the balance. -/
theorem sourceBalanceLocal_exact_int {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.address false)) (address : Roadmap.Address)
    (localValue : s.1.get index = Source.Val.address address) (code : Nat)
    (found : (s.2.ex.world.accounts address).code = some code) (fit : s.2.ex.BalancesFit) :
    (Source.evalE G F (n+2) (sourceBalanceExpr index)).run s =
      (.ok (.val (Source.intWrap Source.IntTy.u256
        ((s.2.ex.world.accounts address).balance : Int))), s) := by
  rw [sourceBalanceLocal_exact G F n s index address localValue code found fit,
    ← sourceUintWrapWord]

/-- **Negative control**: without the invariant, an instance holding exactly
`2 ^ 256` is observed as `0`. -/
theorem sourceBalanceLocal_wide {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.address false)) (address : Roadmap.Address)
    (localValue : s.1.get index = Source.Val.address address) (code : Nat)
    (found : (s.2.ex.world.accounts address).code = some code)
    (wide : (s.2.ex.world.accounts address).balance = Source.Monetary.wide) :
    (Source.evalE G F (n+2) (sourceBalanceExpr index)).run s =
      (.ok (.val (uintValueOfWord E.layout ⟨0, by decide⟩)), s) ∧
      ¬ s.2.ex.BalancesFit := by
  refine ⟨?_, fun fit => Source.Monetary.wide_not_fits (wide ▸ fit.1 address)⟩
  rw [sourceBalanceLocal_run G F n s index address localValue,
    sourceObservedBalance_system G s address code found, wide]
  rfl

end Solidity.Yul.Views

/-- info: 'Solidity.Yul.Views.sourceBalanceLocal_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Views.sourceBalanceLocal_exact

/-- info: 'Solidity.Yul.Views.sourceBalanceLocal_exact_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Views.sourceBalanceLocal_exact_int

/-- info: 'Solidity.Yul.Views.sourceBalanceLocal_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Views.sourceBalanceLocal_wide
