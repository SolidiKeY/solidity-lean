import Solidity.Yul.LocalDefaultUnchecked
import Solidity.Yul.LocalDefaultHorizon

/-! Completed-run fuel stability for the existing unchecked default-item wrapper
and ordinary continuation. Adds no unchecked arithmetic or readback semantics. -/
namespace Solidity.Yul.LocalUncheckedHorizon

theorem successor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,false⟩ rest)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types) (final : Solidity.Yul.LocalState env out),
 Solidity.Yul.LocalDefaultUnchecked.run inside tail fuel state = .normal final →
 Solidity.Yul.LocalDefaultUnchecked.run inside tail (fuel+1) state = .normal final := by
  intro env returns modifier l types middle out inner inside rest tail fuel state final completed
  cases fuel with
  | zero => cases completed
  | succ fuel =>
    cases actual : Solidity.Yul.LocalDefaultItems.run inside fuel state with
    | halted halt previous =>
      simp only [Solidity.Yul.LocalDefaultUnchecked.run,actual,Solidity.Yul.LocalDefaultItems.close] at completed
      cases completed
    | normal next =>
      have before := Solidity.Yul.LocalDefaultHorizon.successor env returns modifier ⟨l,true⟩ types middle inner inside fuel state next actual
      have tailDone : Solidity.Yul.LocalDefaultItems.run tail fuel
          (Solidity.Yul.LocalDefaultItems.restore inside next) = .normal final := by
        simpa only [Solidity.Yul.LocalDefaultUnchecked.run,actual,Solidity.Yul.LocalDefaultItems.close] using completed
      have after := Solidity.Yul.LocalDefaultHorizon.successor env returns modifier ⟨l,false⟩ types out rest tail fuel
        (Solidity.Yul.LocalDefaultItems.restore inside next) final tailDone
      simpa only [Solidity.Yul.LocalDefaultUnchecked.run,before,actual,Solidity.Yul.LocalDefaultItems.close] using after


theorem extension : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,false⟩ rest)
 (fuel extra : Nat) (state : Solidity.Yul.LocalState env types) (final : Solidity.Yul.LocalState env out),
 Solidity.Yul.LocalDefaultUnchecked.run inside tail fuel state = .normal final →
 Solidity.Yul.LocalDefaultUnchecked.run inside tail (fuel+extra) state = .normal final := by
  intro env returns modifier l types middle out inner inside rest tail fuel extra state final completed
  induction extra with
  | zero => exact completed
  | succ extra ih =>
    exact Solidity.Yul.LocalUncheckedHorizon.successor env returns modifier l types middle out inner inside rest tail (fuel+extra) state final ih

theorem blockSuccessor : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,false⟩ rest)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types) (final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultUnchecked.blockRun inside tail fuel state = .normal final →
 Solidity.Yul.LocalDefaultUnchecked.blockRun inside tail (fuel+1) state = .normal final := by
  intro env returns modifier l types middle out inner inside rest tail fuel state final completed
  cases fuel with
  | zero => cases completed
  | succ fuel =>
    cases actual : Solidity.Yul.LocalDefaultUnchecked.run inside tail fuel state with
    | normal middleState =>
      have same := Solidity.Yul.LocalUncheckedHorizon.successor env returns modifier l types middle out inner inside rest tail fuel state middleState actual
      simpa only [Solidity.Yul.LocalDefaultUnchecked.blockRun,same,actual] using completed
    | halted halt previous =>
      simp only [Solidity.Yul.LocalDefaultUnchecked.blockRun,actual,Solidity.Yul.LocalDefaultItems.close] at completed
      cases completed

theorem blockExtension : ∀ (env : Solidity.Source.Env) (returns : List Solidity.Source.STy)
 (modifier l : Bool) (types middle out : Solidity.Source.RCtx)
 (inner : Solidity.Source.RItems env returns modifier ⟨l,true⟩ types middle)
 (inside : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,true⟩ inner)
 (rest : Solidity.Source.RItems env returns modifier ⟨l,false⟩ types out)
 (tail : Solidity.Yul.LocalDefaultItems.Supported env returns modifier ⟨l,false⟩ rest)
 (fuel extra : Nat) (state : Solidity.Yul.LocalState env types) (final : Solidity.Yul.LocalState env types),
 Solidity.Yul.LocalDefaultUnchecked.blockRun inside tail fuel state = .normal final →
 Solidity.Yul.LocalDefaultUnchecked.blockRun inside tail (fuel+extra) state = .normal final := by
  intro env returns modifier l types middle out inner inside rest tail fuel extra state final completed
  induction extra with
  | zero => exact completed
  | succ extra ih =>
    exact Solidity.Yul.LocalUncheckedHorizon.blockSuccessor env returns modifier l types middle out inner inside rest tail (fuel+extra) state final ih

end Solidity.Yul.LocalUncheckedHorizon
