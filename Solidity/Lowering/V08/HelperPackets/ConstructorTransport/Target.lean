import Solidity.Lowering.V08.HelperPackets.ConstructorTransport.Source

/-! Actual intrinsic initialization, local capture, body execution and creation.
The model's constructor input program explicitly contains the initializer. -/
namespace Solidity.Lowering.V08.HelperPackets.ConstructorTransport
open Solidity
open Solidity.Lowering.V07

def Cell : Contract := contract!{
  uint saved;
  uint captured;
  constructor(uint n) { uint old = saved; saved = n; captured = old; }
}
def catalog : Unit → Contract := fun _ => Cell
def targetInitial : ContractWorld.World catalog := ContractWorld.World.empty catalog
  (fun a => if a=Controls.sender then ⟨93,by decide +kernel⟩
    else if a=Controls.self then ⟨5,by decide +kernel⟩ else ⟨0,by decide +kernel⟩)
def targetContext : ContractWorld.Context :=
  {sender:=Controls.sender,mode:=.ordinary ⟨0,by decide +kernel⟩}

def captureBody (n : Int) (h : range n) : Prog Cell [] [.val .uint] :=
  .cons (.declLocal .uint (.user "old") (some (.read (.root "saved" rfl))))
  (.cons (.assign (.root "saved" rfl)
    (.val (.simple (.lit n (integer_range Source.IntTy.u256 n h)))))
  (.cons (.assign (.root "captured" rfl) (.val (.simple (.local .here)))) .nil))
def targetBody (n : Int) (h : range n) : Prog Cell [] [] :=
  .cons (.assign (.root "saved" rfl) (.val (.simple (.lit 7 (by decide +kernel)))))
    (.cons (.block (captureBody n h)) .nil)

def entered : State Cell [] :=
  {storage:=Storage.init Cell,H:=[],heap:=Heap.empty,env:=(),
    selfBalance:=⟨5,by decide +kernel⟩,net:=[],
    tx:=targetContext.tx targetInitial Controls.self}
def targetStore (n : Int) (h : range n) : Storage Cell :=
  let s := Storage.init Cell
  let s := (s.write (SRef.ofRoot "saved" rfl) (.prim (integerValue Source.IntTy.u256 7 (by decide +kernel)))).getD s
  let s := (s.write (SRef.ofRoot "saved" rfl) (.prim (integerValue Source.IntTy.u256 n h))).getD s
  (s.write (SRef.ofRoot "captured" rfl) (.prim (integerValue Source.IntTy.u256 7 (by decide +kernel)))).getD s
def targetReached (n : Int) (h : range n) : State Cell [] := {entered with storage:=targetStore n h}
def targetNext (n : Int) (h : range n) : ContractWorld.World catalog :=
  {targetInitial with
    accounts:=fun a => if a=Controls.self then some ⟨(),targetStore n h⟩ else none
    funds:=fun a => if a=Controls.self then ⟨5,by decide +kernel⟩ else targetInitial.funds a}
def targetRun (n : Int) (h : range n) :=
  targetInitial.create () Controls.self (targetBody n h) targetContext

theorem frame_inputs : ConstructorScalarTransport.FrameInputs frame Controls.self targetContext :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem entry_actual : targetInitial.enter (k:=()) Controls.self targetContext (Storage.init Cell) false =
    .ok entered := by rfl

theorem target_body_actual (n : Int) (h : range n) :
    (targetBody n h).run entered = .ok ⟨targetReached n h,List.prefix_refl _⟩ := by
  unfold targetBody captureBody
  rfl

theorem settlement_actual :
    ContractWorld.settle targetInitial.funds Controls.self [] = .ok targetInitial.funds := rfl

theorem finish_actual (n : Int) (h : range n) :
    targetInitial.finish (k:=()) Controls.self (targetReached n h) = .ok (targetNext n h) := by rfl

theorem creation_actual (n : Int) (h : range n) :
    targetRun n h = .ok (targetNext n h,⟨Controls.self⟩) := by
  change (do
    let state ← targetInitial.enter (k:=()) Controls.self targetContext (Storage.init Cell) false
    let output ← (targetBody n h).run state
    let next ← targetInitial.finish (k:=()) Controls.self output.st
    pure (next,(⟨Controls.self⟩ : ContractWorld.Handle ()))) = _
  rw [entry_actual]
  simp only [bind,Except.bind,target_body_actual,finish_actual]
  rfl

theorem target_saved (n : Int) (h : range n) :
    (targetStore n h).find (SRef.ofRoot "saved" rfl) =
      some (.prim (integerValue Source.IntTy.u256 n h)) := by rfl

theorem target_captured (n : Int) (h : range n) :
    (targetStore n h).find (SRef.ofRoot "captured" rfl) =
      some (.prim (integerValue Source.IntTy.u256 7 (by decide +kernel))) := by rfl

theorem target_static (n : Int) (h : range n) :
    targetInitial.create () Controls.self (targetBody n h)
      {targetContext with mode:=.readOnly} = .error .revert := by rfl
end Solidity.Lowering.V08.HelperPackets.ConstructorTransport
