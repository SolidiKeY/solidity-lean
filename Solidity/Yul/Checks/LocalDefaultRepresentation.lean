import Solidity.Yul.LocalDefaultRepresentation
import Solidity.Yul.Checks.LocalBoolRepresentation

namespace Solidity.Yul.Checks.LocalDefaultRepresentation
export Solidity.Yul.Checks.LocalBoolRepresentation (env raw cleanTrue)
def zero8 := RawDefaultDeclaration.intDefault env Solidity.Source.IntTy.u8
def zero256 := RawDefaultDeclaration.intDefault env Solidity.Source.IntTy.u256
abbrev Out : Solidity.Source.RCtx :=
  [.int Solidity.Source.IntTy.u256,.int Solidity.Source.IntTy.u8,.bool]
def initial (value : LocalValue env .bool) (world : Solidity.Source.St env) :
    LocalState env [.bool] := ((value,()),world)
def first (value : LocalValue env .bool) (world : Solidity.Source.St env) :
    LocalState env [.int Solidity.Source.IntTy.u8,.bool] :=
  ((.clean zero8.value,(value,())),world)
def full (value : LocalValue env .bool) (world : Solidity.Source.St env) :
    LocalState env Out :=
  ((.clean zero256.value,(.clean zero8.value,(value,()))),world)
def items (control : Solidity.Source.SCtx) :
    Solidity.Source.RItems env [] false control [.bool] Out :=
  .stmt (.declVar (.int Solidity.Source.IntTy.u8))
    (.stmt (.declVar (.int Solidity.Source.IntTy.u256))
      (.stmt (.expr (.local (.there (.there .here)))) .nil))
def proof (control : Solidity.Source.SCtx) :
    LocalDefaultItems.Supported env [] false control (items control) :=
  .declaration zero8 (.declaration zero256
    (.body (.expression (.base (.local (.there (.there .here)))) .nil)))
def witness : Nonempty (LocalDefaultItems.Supported env [] false ⟨false,false⟩
    (items ⟨false,false⟩)) := ⟨proof ⟨false,false⟩⟩
def concrete (fuel : Nat) (one two : LocalState env [.bool])
    (related : Solidity.Yul.LocalBoolRepresentation.State one two) :=
  Solidity.Yul.LocalDefaultRepresentation.unchecked env [] false false
    [.bool] Out Out (items ⟨false,true⟩) (proof ⟨false,true⟩)
    (items ⟨false,false⟩) (proof ⟨false,false⟩) fuel one two related

theorem inputRelated : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalBoolRepresentation.State (Solidity.Yul.Checks.LocalDefaultRepresentation.initial Solidity.Yul.Checks.LocalDefaultRepresentation.cleanTrue world) (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) := by
  intro world; exact ⟨.cons (.boolean (one := Solidity.Yul.Checks.LocalDefaultRepresentation.cleanTrue) (two := Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) rfl) (.same (ctx := []) ()),rfl⟩

theorem resultRelated : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalBoolItemRepresentation.Items Solidity.Yul.Checks.LocalDefaultRepresentation.env Solidity.Yul.Checks.LocalDefaultRepresentation.Out (Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial Solidity.Yul.Checks.LocalDefaultRepresentation.cleanTrue world)) (Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world)) := by
  intro world; exact .normal ⟨.cons (.same _) (.cons (.same _) (.cons (.boolean (one := Solidity.Yul.Checks.LocalDefaultRepresentation.cleanTrue) (two := Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) rfl) (.same (ctx := []) ()))),rfl⟩

theorem projectionDiffers : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), (Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial Solidity.Yul.Checks.LocalDefaultRepresentation.cleanTrue world))).isSome = true ∧ (Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world))).isSome = false := by
  intro world; exact ⟨rfl,rfl⟩

theorem firstPrefixHalt : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 3 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultRepresentation.first (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) := by
  intro world; rfl

theorem secondPrefixHalt : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultItems.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 4 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultRepresentation.full (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) := by
  intro world; rfl

theorem scopeClosure : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultItems.blockRun (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) := by
  intro world; rfl

theorem uncheckedContinuation : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultUnchecked.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.full (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) := by
  intro world; rfl

theorem uncheckedInnerHalt : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultUnchecked.run (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultRepresentation.full (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) := by
  intro world; rfl

theorem uncheckedScopeClosure : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultRepresentation.env), Solidity.Yul.LocalDefaultUnchecked.blockRun (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,true⟩) (Solidity.Yul.Checks.LocalDefaultRepresentation.proof ⟨false,false⟩) 7 (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) = .normal (Solidity.Yul.Checks.LocalDefaultRepresentation.initial (Solidity.Yul.Checks.LocalDefaultRepresentation.raw 1) world) := by
  intro world; rfl

#print axioms Solidity.Yul.LocalDefaultRepresentation.items
#print axioms Solidity.Yul.LocalDefaultRepresentation.restore
#print axioms Solidity.Yul.LocalDefaultRepresentation.close
#print axioms Solidity.Yul.LocalDefaultRepresentation.block
#print axioms Solidity.Yul.LocalDefaultRepresentation.unchecked
#print axioms Solidity.Yul.LocalDefaultRepresentation.uncheckedBlock
#print axioms inputRelated
#print axioms resultRelated
#print axioms projectionDiffers
#print axioms firstPrefixHalt
#print axioms secondPrefixHalt
#print axioms scopeClosure
#print axioms uncheckedContinuation
#print axioms uncheckedInnerHalt
#print axioms uncheckedScopeClosure

end Solidity.Yul.Checks.LocalDefaultRepresentation
