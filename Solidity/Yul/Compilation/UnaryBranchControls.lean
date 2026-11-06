import Solidity.Yul.Compilation.UnaryBranch
import Solidity.Yul.Compilation.NormalStackTransport
/-! Whole source/model branch controls; no native/G24/admission claim. -/
namespace Solidity.Yul.Compilation.UnaryBranch.Controls
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
def sourceResult (a : Scalar.Word) :=
  (evalStmt 3 .nil True.intro source compiled.profile
    (ProducerExpressions.sourceLocals #v[a])).map
    (fun out => ((out.vars 0).val,out.flow.isNormal))
def modelResult (a : Scalar.Word) (tail : List Evm.Word) :=
  match Evm.run model {Evm.Machine.init with stack := coreWord a::tail} with
  | .ok out skip => some (out.stack,skip)
  | _ => none
#check compiled.source #v[dirty]
#check model_run dirty Evm.Machine.init [.slot (.root 17),coreWord 88]
#guard sourceResult 0 = some (dirty.toNat,true)
#guard sourceResult 1 = some (1,true)
#guard sourceResult highOnly = some (highOnly.toNat,true)
#guard sourceResult dirty = some (dirty.toNat,true)
#guard modelResult 0 [.slot (.root 17),coreWord 88] =
  some ([coreWord dirty,.slot (.root 17),coreWord 88],0)
#guard modelResult highOnly [.slot (.root 17),coreWord 88] =
  some ([coreWord highOnly,.slot (.root 17),coreWord 88],0)
#guard modelResult dirty [.slot (.root 17)] = some ([coreWord dirty,.slot (.root 17)],0)
#guard (NormalControl.compile 2 source).isNone
#guard ((compiled.emit 0).bind WordControl.blockCode).isSome
#guard ((compiled.emit 0).bind NormalStackTransport.blockCode).isNone
#guard match Evm.run model Evm.Machine.init with | .fault => true | _ => false
-- Uncapped model success does not certify native capacity.
#guard (modelResult 0 (List.replicate 1025 (.slot (.root 17)))).map
  (fun result => result.1.length) = some 1026
end Solidity.Yul.Compilation.UnaryBranch.Controls
