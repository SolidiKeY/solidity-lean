import Solidity.Yul.Compilation.ComparisonBranch
import Solidity.Yul.Compilation.NormalStackTransport
/-! Concrete comparison/control/source tests, not native/Source-G24 closure. -/
namespace Solidity.Yul.Compilation.ComparisonBranch.Controls
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
def sourceResult (a b : Scalar.Word) :=
  (evalStmt 3 .nil True.intro source compiled.profile
    (ProducerExpressions.sourceLocals #v[a,b])).map
    (fun out => ((out.vars 0).val,(out.vars 1).val,out.flow.isNormal))
def modelResult (a b : Scalar.Word) (tail : List Evm.Word) :=
  match Evm.run model {Evm.Machine.init with stack := coreWord a::coreWord b::tail} with
  | .ok out skip => some (out.stack,skip)
  | _ => none
#check compiled.source #v[dirty,7]
#check model_run dirty 7 Evm.Machine.init [.slot (.root 17),coreWord 88]
#guard sourceResult 1 3 = some (1,dirty.toNat,true)
#guard sourceResult 3 1 = some (3,1,true)
#guard sourceResult highOnly 1 = some (highOnly.toNat,1,true)
#guard sourceResult 1 highOnly = some (1,dirty.toNat,true)
#guard sourceResult dirty dirty = some (dirty.toNat,dirty.toNat,true)
#guard modelResult 1 3 [.slot (.root 17),coreWord 88] =
  some ([coreWord 1,coreWord dirty,.slot (.root 17),coreWord 88],0)
#guard modelResult highOnly 1 [.slot (.root 17),coreWord 88] =
  some ([coreWord highOnly,coreWord 1,.slot (.root 17),coreWord 88],0)
#guard modelResult 1 highOnly [.slot (.root 17)] =
  some ([coreWord 1,coreWord dirty,.slot (.root 17)],0)
#guard (NormalControl.compile 2 source).isNone
#guard ((compiled.emit 0).bind WordControl.blockCode).isSome
#guard ((compiled.emit 0).bind NormalStackTransport.blockCode).isNone
#guard match Evm.run model {Evm.Machine.init with stack := [coreWord 1]} with
  | .fault => true | _ => false
-- Uncapped model success does not certify native capacity.
#guard (modelResult 1 3 (List.replicate 1025 (.slot (.root 17)))).map
  (fun result => result.1.length) = some 1027
end Solidity.Yul.Compilation.ComparisonBranch.Controls
