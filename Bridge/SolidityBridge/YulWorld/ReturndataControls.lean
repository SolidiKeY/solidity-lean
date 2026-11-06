import SolidityBridge.YulWorld.Returndata
namespace SolidityBridge.YulWorld.ReturndataControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open SolidityBridge.RoadmapV15.P10 SolidityBridge.YulWorld.Returndata

private def before : Backend.Program := [.push ⟨1,by decide⟩ #v[0x3e],.op .POP]
private def after : Backend.Program := [.op .STOP]
private def code : ByteArray := ⟨(Backend.encode (before ++ .op .RETURNDATACOPY :: after)).toArray⟩
private def seed (gas destination source length : Nat) : EVM.State :=
  {(default : EVM.State) with
    gasAvailable:=.ofNat gas,activeWords:=.ofNat 1,execLength:=41
    stack:=[.ofNat destination,.ofNat source,.ofNat length,.ofNat 258,.ofNat 513]
    memory:=⟨#[0xaa,0xbb,0xcc,0xdd,0xee,0xff,0x99,0x88]⟩
    returnData:=⟨#[0x11,0x22,0x33]⟩,H_return:=⟨#[0x91,0x92]⟩
    accountMap:=((default : EVM.State).accountMap.insert (.ofNat 21)
      {(default : Account .EVM) with nonce:=.ofNat 3,balance:=.ofNat 29,code:=code,storage:=(default : Storage).insert (.ofNat 3) (.ofNat 9),tstorage:=(default : Storage).insert (.ofNat 4) (.ofNat 17)}).insert (.ofNat 22)
      {(default : Account .EVM) with nonce:=.ofNat 5,balance:=.ofNat 41,code:=⟨#[0]⟩}
    substate:={(default : Substate) with logSeries:=#[
      ⟨.ofNat 21,#[.ofNat 17,.ofNat 34],⟨#[0xa1]⟩⟩,
      ⟨.ofNat 22,#[.ofNat 51],⟨#[0xb1,0xb2]⟩⟩]}
    executionEnv:={(default : EVM.State).executionEnv with codeOwner:=.ofNat 21,source:=.ofNat 22,sender:=.ofNat 23,weiValue:=.ofNat 7,perm:=false,code:=code,calldata:=⟨#[0x44,0x55,0x66]⟩}}
private def site (gas destination source length : Nat) : Site .RETURNDATACOPY :=
  ⟨seed gas destination source length,before,after,by decide +kernel⟩

private def copied : CopyInput (site 6 2 1 2) #[] :=
  {charged:=returnCopyCharged (site 6 2 1 2).state
   cost:=EVM.C' (returnCopyCharged (site 6 2 1 2).state) .RETURNDATACOPY
   tail:=[.ofNat 258,.ofNat 513],destination:=.ofNat 2,source:=.ofNat 1,length:=.ofNat 2
   gate:=return_copy_range_admitted #[] (site 6 2 1 2).state
     (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
   operands:=by rfl}

example : copied.window=some [0x22,0x33] := by decide +kernel
example : copied.window≠some [0x11,0x22] := by decide +kernel
example : copied.window≠some [0x91,0x92] := by decide +kernel
example : copied.window≠some [0x22] := by decide +kernel
example : copied.window≠some [] := by decide +kernel
example (fuel : Nat) : Assembly.driverSteps 1 (fuel+2) #[] (site 6 2 1 2).state=.ok copied.next :=
  (copied.agreement fuel).1
example : copied.next.toState=(site 6 2 1 2).state.toState := (copied.agreement 0).2.1
example : copied.next.returnData=⟨#[0x11,0x22,0x33]⟩ := (copied.agreement 0).2.2.1
example : copied.next.H_return=⟨#[0x91,0x92]⟩ := (copied.agreement 0).2.2.2.1
example : copied.next.substate.logSeries=(site 6 2 1 2).state.substate.logSeries :=
  congrArg (fun s=>s.substate.logSeries) (copied.agreement 0).2.1
example : (site 6 2 1 2).state.executionEnv.perm=false := by rfl
example : (site 6 2 1 2).state.substate.logSeries.size=2 := by rfl

private def zero : CopyInput (site 3 (2^256-1) 3 0) #[] :=
  {charged:=returnCopyCharged (site 3 (2^256-1) 3 0).state
   cost:=EVM.C' (returnCopyCharged (site 3 (2^256-1) 3 0).state) .RETURNDATACOPY
   tail:=[.ofNat 258,.ofNat 513],destination:=.ofNat (2^256-1),source:=.ofNat 3,length:=.ofNat 0
   gate:=return_copy_range_admitted #[] (site 3 (2^256-1) 3 0).state
     (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
   operands:=by rfl}
example : zero.window=some [] := by decide +kernel
example (fuel : Nat) : Assembly.driverSteps 1 (fuel+2) #[] (site 3 (2^256-1) 3 0).state=.ok zero.next :=
  (zero.agreement fuel).1
example : zero.next.memory=(site 3 (2^256-1) 3 0).state.memory := by rfl
example (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (site 3 2 4 0).state=.error .InvalidMemoryAccess ∧
    EVM.X (fuel+2) #[] (site 3 2 4 0).state=.error .InvalidMemoryAccess := by
  exact rejected_window (site 3 2 4 0) #[] fuel (.ofNat 2) (.ofNat 4) (.ofNat 0)
    [.ofNat 258,.ofNat 513] rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)

example (fuel : Nat) : Assembly.driverSteps 1 (fuel+2) #[] (site 2 2 4 0).state=.error .OutOfGass := by
  have gate : Assembly.driverGate #[] (site 2 2 4 0).state .RETURNDATACOPY=.error .OutOfGass := by
    rw [return_copy_gate_classification]
    rw [if_neg (by decide +kernel),if_pos (by decide +kernel)]
  rw [FrozenV1.api.charged.checked_return_copy _ _ fuel,gate]
end SolidityBridge.YulWorld.ReturndataControls
