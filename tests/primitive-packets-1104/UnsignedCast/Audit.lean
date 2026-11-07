import Lean
import Solidity.Backend.PrimitivePackets.UnsignedCast.Controls

#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.zero_wrap
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.power_wrap
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.negative_one_mod
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.maximum_wrap
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.power_source_range
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.not_zero_width
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.not_nonbyte_width
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.not_narrowing_256
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.compile_selection
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.generated_code
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.machine_run
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.Controls.represented
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.Controls.executions
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.Controls.protected_observations
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.Controls.wrong_saved_tail
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.Controls.wrong_uint8_unmasked
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.source_total
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.source_run
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.wrapped
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.value_run
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.source_both_pipelines
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.source_timeout
#print axioms Solidity.Backend.PrimitivePackets.UnsignedCast.transport

open Lean in
run_cmd do
  let env ← getEnv
  let lanePrefix := `Solidity.Backend.PrimitivePackets.UnsignedCast
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index]!
      if lanePrefix.isPrefixOf moduleName then
        let axioms ← collectAxioms name
        rows := rows.push (Json.mkObj [
          ("name",toJson name.toString),("module",toJson moduleName.toString),
          ("theorem",toJson info.isTheorem),("unsafe",toJson info.isUnsafe),
          ("partial",toJson info.isPartial),("axiom",toJson info.isAxiom),
          ("axioms",toJson (axioms.map (fun n => n.toString)))])
  logInfo m!"UNSIGNED_CAST_DECLARATIONS {(Json.arr rows).compress}"
