import Lean.Util.CollectAxioms
import Solidity.Backend.PrimitivePackets.UnsignedMul.WidthControls
import Solidity.Backend.PrimitivePackets.UnsignedMul.WideControls

namespace Solidity.Backend.PrimitivePackets.UnsignedMul.Observations
open Evm Evm.Memory Source.SemanticsExamples

def sourceObservation (p : Roadmap.Pipeline) (x y : Fin 256) : Option Int :=
  match (Source.evalE (G0 p) {F0 with checked := false} 3
      (.binary .mul (.local (Controls.si false)) (.local (Controls.si true)))).run (Controls.source x y) with
  | (.ok (.val v),_) => v.key
  | _ => none

def wideSourceObservation (p : Roadmap.Pipeline) : Option Int :=
  match (Source.evalE (G0 p) {F0 with checked := false} 3
      (.binary .mul (.local (WideControls.si false)) (.local (WideControls.si true)))).run
        (WideControls.source ⟨W-1,by unfold W; decide⟩ (wmod 2)) with
  | (.ok (.val v),_) => v.key
  | _ => none

-- Actual evaluator observations; proofs live in the imported modules.
#eval [wideSourceObservation .legacy,wideSourceObservation .viaIR]
#eval ([Roadmap.Pipeline.legacy,.viaIR].map fun p =>
  [sourceObservation p 0 255,sourceObservation p 255 255,sourceObservation p 200 2])
#eval Controls.observe (run Controls.code {Controls.machine 200 2 with stack := [w[77],w[88]]})
#eval Controls.observe (run Controls.wrongCode {Controls.machine 200 2 with stack := [w[77],w[88]]})
#eval Controls.observe (run WideControls.code
  {WideControls.machine ⟨W-1,by unfold W; decide⟩ (wmod 2) with stack := [w[77],w[88]]})

#print axioms selectable
#print axioms selection
#print axioms execution
#print axioms Controls.represented
#print axioms Controls.wrap
#print axioms Controls.wrong_cleaning_refused
#print axioms Controls.insufficient_horizon
#print axioms WideControls.maximum_wrap
#print axioms WidthControls.emitted
end Solidity.Backend.PrimitivePackets.UnsignedMul.Observations

open Lean in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Solidity.Backend.PrimitivePackets.UnsignedMul." then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
          throwError "nonstandard axiom {ax} in {name}"
      logInfo m!"AXIOM-AUDIT {name}: {axioms}"
      count := count + 1
  logInfo m!"AXIOM-AUDIT declarations={count} findings=0"
