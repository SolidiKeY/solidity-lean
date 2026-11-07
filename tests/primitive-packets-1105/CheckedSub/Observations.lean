import Lean.Util.CollectAxioms
import Solidity.Backend.PrimitivePackets.CheckedSub.Controls

namespace Solidity.Backend.PrimitivePackets.CheckedSub.Observations
open Evm Evm.Memory
open Source.SemanticsExamples (G0 F0)
open Controls.Fixture

def sourceObservation (p : Roadmap.Pipeline) (x y : Nat) (hx : x<W) (hy : y<W) :
    Except Source.Halt (Option Int) :=
  match (Source.evalE (G0 p) {F0 with checked := true} 3
    (.binary .sub (.local .here) (.local (.there .here)))).run (source x y hx hy) with
  | (.ok (.val v),_) => .ok v.key
  | (.error h,_) => .error h

def targetObservation : Evm.Out → String × Option (List Nat)
  | .ok m 0 => ("ok",(m.stack ++ protectedCells.map m.mem).mapM
      (fun w => match w with | .val n => some n.val | .slot _ => none))
  | .revert => ("revert",none)
  | .fault => ("fault",none)
  | .ok _ _ => ("skip",none)

#eval [sourceObservation .legacy 9 7 (by decide) (by decide),
  sourceObservation .viaIR 9 7 (by decide) (by decide)]
#eval [sourceObservation .legacy 0 1 (by decide) (by decide),
  sourceObservation .viaIR 0 1 (by decide) (by decide)]
#eval sourceObservation .legacy (W-1) 0 (by decide) (by decide)
#eval sourceObservation .viaIR (W-1) (W-1) (by decide) (by decide)
#eval targetObservation (run differenceCode {machine 9 7 (by decide) (by decide) with stack := [w[77],w[88]]})
#eval targetObservation (run differenceCode {machine 0 1 (by decide) (by decide) with stack := [w[77],w[88]]})
#eval targetObservation (run differenceCode {machine (W-1) 0 (by decide) (by decide) with stack := [w[77],w[88]]})
#eval targetObservation (run differenceCode {machine 7 7 (by decide) (by decide) with stack := [w[77],w[88]]})
#eval targetObservation (run differenceCode {machine 7 9 (by decide) (by decide) with stack := [w[77],w[88]]})

#print axioms public_selection
#print axioms classification
#print axioms target_underflow_iff
#print axioms Controls.Fixture.represented
#print axioms Controls.Fixture.regular
#print axioms Controls.Fixture.underflow
#print axioms Controls.Fixture.underflow_does_not_wrap
#print axioms Controls.Fixture.wrong_index_refused
#print axioms Controls.Fixture.wrong_value_refused
end Solidity.Backend.PrimitivePackets.CheckedSub.Observations

open Lean in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name,_) in env.constants.toList do
    if name.toString.startsWith "Solidity.Backend.PrimitivePackets.CheckedSub." then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "nonstandard axiom {ax} in {name}"
      logInfo m!"AXIOM-AUDIT {name}: {axioms}"
      count := count+1
  logInfo m!"AXIOM-AUDIT declarations={count} findings=0"
