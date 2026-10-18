import Solidity.Calculus.DeclarationStaticReduction
import Solidity.Calculus.FunContract
import Solidity.Examples.ReadRealization

/-!
# Exact update guards and landing witnesses

Box updates accept ordinary failure; diamond updates require success.
The certificates describe the original formula, including writes and local
bindings. Programs, memory-local contexts and push exhaustion stay outside
the update recognizer.
-/

namespace Solidity.Examples.ExactUpdates

open Solidity.Decide Solidity.ReadRealization
open Solidity.Examples.ReadRealization (Bank three)
open scoped Solidity.Scoped

local instance : InContract := ⟨Bank⟩

def identityClaim : Fml Bank [] := dl!{ { storage := storage } balances[3] == 17 }
def identityReduction : StaticReduction identityClaim :=
  (checkedReduction? identityClaim).get (by decide +kernel)

/-- info: some true -/
#guard_msgs in
#eval match identityReduction.verify with
  | .inl _ => none
  | .inr cm => some (decide ((three.read cm.val.storage).val ≠ 17))

def localClaim : Fml Bank [] := dl!{ { x := find(storage, balances[3]) - 1 } x = x }
def localReduction : SourceReduction localClaim := (sourceReduction? localClaim).get (by decide +kernel)

def diamondClaim : Fml Bank [] := dl![.diamond]{ { x := find(storage, balances[3]) - 1 } x = x }
def diamondReduction : StaticReduction diamondClaim :=
  (checkedReduction? diamondClaim).get (by decide +kernel)

/-- info: some 0 -/
#guard_msgs in
#eval match diamondReduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.val.storage).val

def boxClaim : Fml Bank [] := dl![.box]{ { x := find(storage, balances[3]) - 1 } x = x }
def boxReduction : StaticReduction boxClaim := (checkedReduction? boxClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval boxReduction.verify.isLeft

def vacuousClaim : Fml Bank [] :=
  dl![.box]{ balances[3] == 0 → { x := find(storage, balances[3]) - 1 } false }
def vacuousReduction : StaticReduction vacuousClaim :=
  (checkedReduction? vacuousClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval vacuousReduction.verify.isLeft

def falseLocal : Fml Bank [] := dl![.diamond]{ { x := false } x = false }
def falseLocalReduction : StaticReduction falseLocal := (checkedReduction? falseLocal).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval falseLocalReduction.verify.isLeft

def writeClaim : Fml Bank [] := dl!{ { storage := save(storage, balances[3], 17) } balances[3] == 17 }
def writeReduction : SourceReduction writeClaim := (sourceReduction? writeClaim).get (by decide +kernel)

def writeChecked : StaticReduction writeClaim := (checkedReduction? writeClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval writeChecked.verify.isLeft

def simultaneousClaim : Fml Bank [] :=
  dl![.diamond]{ balances[3] == 17 → { x := find(storage, balances[3]) ‖ y := 17 }
    (x = 17 ∧ y = 17) }
def simultaneousReduction : StaticReduction simultaneousClaim :=
  (checkedReduction? simultaneousClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval simultaneousReduction.verify.isLeft

def swapClaim : Fml Bank [] :=
  dl![.diamond]{ balances[3] == 23 → { x := 17 ‖ y := find(storage, balances[3]) }
    { x := y ‖ y := x } (x = 23 ∧ y = 17) }
def swapReduction : StaticReduction swapClaim := (checkedReduction? swapClaim).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval swapReduction.verify.isLeft

def badWrite : Fml Bank [] :=
  dl!{ { storage := save(storage, balances[3], 17) } balances[3] == 18 }
def badWriteReduction : StaticReduction badWrite := (checkedReduction? badWrite).get (by decide +kernel)

/-- info: false -/
#guard_msgs in #eval badWriteReduction.verify.isLeft

def memoryClaim : Fml Bank [.mem (.struct "Person")] :=
  cdlIn[Bank | Person memory m]{ { storage := storage } true }

example : (ExactAt.ofFormula? 32
    (SymS.init.push (t := .mem (.struct "Person")) none) memoryClaim).isNone = true := by
  decide +kernel

def ArrayBank : Contract := contract!{ uint[] values; }
def pushClaim : Fml ArrayBank [] :=
  cdl[ArrayBank]{ { storage := save(save(storage, values[values.length], 1), values.length, values.length + 1) } true }

example : (sourceReduction? pushClaim).isNone = true := by decide +kernel

example : (sourceReduction? (dl!{ [ balances[3] = 7; ] balances[3] == 7 })).isNone = true := by
  decide +kernel

/-- info: 'Solidity.Decide.updateGuard_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updateGuard_iff

end Solidity.Examples.ExactUpdates
