import SolidityBridge.RoadmapV15.P10.FrozenInterface
import SolidityBridge.RoadmapV15.P10.Execution

/-! Concrete inhabitant of the H12 frozen signatures, using ONLY existing
checked P10 laws. This does not discharge the missing production prerequisites
listed by FrozenInterface; the field statements retain their exact boundaries. -/
namespace SolidityBridge.RoadmapV15.P10.FrozenV1

theorem api : API where
  decoded := {
    decode_call := _root_.SolidityBridge.RoadmapV15.P10.decode_call
    decode_return_size := _root_.SolidityBridge.RoadmapV15.P10.decode_return_size
    decode_return_copy := _root_.SolidityBridge.RoadmapV15.P10.decode_return_copy
    decode_jump := _root_.SolidityBridge.RoadmapV15.P10.decode_jump
    decode_jump_if := _root_.SolidityBridge.RoadmapV15.P10.decode_jump_if
    decode_jump_dest := _root_.SolidityBridge.RoadmapV15.P10.decode_jump_dest
  }
  charged := {
    checked_call := _root_.SolidityBridge.RoadmapV15.P10.checked_call
    checked_return_size := _root_.SolidityBridge.RoadmapV15.P10.checked_return_size
    checked_return_copy := _root_.SolidityBridge.RoadmapV15.P10.checked_return_copy
    checked_jump := _root_.SolidityBridge.RoadmapV15.P10.checked_jump
    checked_jump_if := _root_.SolidityBridge.RoadmapV15.P10.checked_jump_if
    checked_jump_dest := _root_.SolidityBridge.RoadmapV15.P10.checked_jump_dest
  }
  continuation := {
    x_call := _root_.SolidityBridge.RoadmapV15.P10.x_call
    x_return_size := _root_.SolidityBridge.RoadmapV15.P10.x_return_size
    x_return_copy := _root_.SolidityBridge.RoadmapV15.P10.x_return_copy
    x_jump := _root_.SolidityBridge.RoadmapV15.P10.x_jump
    x_jump_if := _root_.SolidityBridge.RoadmapV15.P10.x_jump_if
    x_jump_dest := _root_.SolidityBridge.RoadmapV15.P10.x_jump_dest
  }

#print axioms api
end SolidityBridge.RoadmapV15.P10.FrozenV1
