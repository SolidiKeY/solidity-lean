import Solidity.Source.FailureCursor
open Solidity.Source.FailureExecution Solidity.Roadmap.Evm
namespace Solidity.Source.FailureCursorControls

def requestPlan : FailurePoints where
  tx i := if i = 0 then .dropped else .runs 257 (some 1)
  frame _ := some 1

def dropped : Cursor := (Cursor.empty.enterRequest requestPlan rfl).2
def running : Cursor := (dropped.enterRequest requestPlan rfl).2
def nested : Cursor := (running.enterFrame requestPlan).enterFrame requestPlan
def stopped : Cursor := nested.advanceEvent

#guard dropped.nextRequest = 1
#guard dropped.nextFrame = 0
#guard dropped.request.isNone
#guard running.nextRequest = 2
#guard running.request.map (fun b => (b.ordinal.val,b.senderBalance,b.emitted)) = some (1,257,0)
#guard nested.nextFrame = 2
#guard nested.frames.map (fun b => b.ordinal.val) = [1,0]
-- Request failure dominates simultaneous cuts in BOTH active frames.
#guard stopped.pending.map (fun stop => stop.isRequest 1) = some true
#guard stopped.pending.map (fun stop => stop.isFrame 1) = some false
#guard stopped.frames.map (fun b => b.emitted) = [1,1]
#guard stopped.advanceEvent.frames.map (fun b => b.emitted) = [1,1]
#guard stopped.leaveFrame.pending.map (fun stop => stop.isRequest 1) = some true
#guard stopped.leaveFrame.nextFrame = 2
#guard stopped.leaveFrame.leaveFrame.leaveRequest.pending.isNone

def framePlan : FailurePoints where
  tx _ := .runs 257 none
  frame _ := some 1

def frames : Cursor := ((Cursor.empty.enterRequest framePlan rfl).2.enterFrame framePlan).enterFrame framePlan
def frameStop : Cursor := frames.advanceEvent
-- The outermost failing frame owns the unwind; the child cannot swallow it.
#guard frameStop.pending.map (fun stop => stop.isFrame 0) = some true
#guard frameStop.pending.map (fun stop => stop.isFrame 1) = some false
#guard frameStop.leaveFrame.pending.map (fun stop => stop.isFrame 0) = some true
#guard frameStop.leaveFrame.frames.map (fun b => (b.ordinal.val,b.emitted)) = [(0,1)]
#guard frameStop.leaveFrame.leaveFrame.pending.isNone
#guard frameStop.leaveFrame.leaveFrame.nextFrame = 2
#guard (frameStop.leaveFrame.leaveFrame.enterFrame framePlan).frames.head?.map (fun b => b.ordinal.val) = some 2

def zeroPlan : FailurePoints where
  tx _ := .runs 9 none
  frame _ := some 0

def zero : Cursor := (Cursor.empty.enterRequest zeroPlan rfl).2.enterFrame zeroPlan
#guard zero.stop?.map (fun stop => stop.isFrame 0) = some true
#guard zero.advanceEvent.frames.map (fun b => b.emitted) = [0]

end Solidity.Source.FailureCursorControls
