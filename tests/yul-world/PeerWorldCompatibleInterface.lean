import Solidity.Yul.World.PeerMemoryAgreement
import Solidity.Yul.World.PeerCreationAgreement
import Solidity.Yul.World.PeerWorldAgreement
import Solidity.Backend.AbiWorld.WorldFrames

#check Solidity.Yul.World.PeerMemoryAgreement.compiled_input_load
#check Solidity.Yul.World.PeerMemoryAgreement.compiled_byte_survives
#check Solidity.Yul.World.PeerCreationAgreement.target
#check Solidity.Yul.World.PeerCreationAgreement.probeAnswer
#check Solidity.Yul.World.PeerCreationAgreement.expected
#check Solidity.Yul.World.PeerCreationAgreement.compiled_initialization
#check Solidity.Yul.World.PeerCreationAgreement.compiled_success_size
#check Solidity.Yul.World.PeerCreationAgreement.compiled_revert_size
#check Solidity.Yul.World.PeerWorldAgreement.completion_unrelated
#check Solidity.Yul.World.PeerWorldAgreement.child_mark
#check Solidity.Yul.World.PeerWorldAgreement.actual_callback_rollback
#check Solidity.Backend.AbiWorld.operationOwner
#check Solidity.Backend.AbiWorld.unrelated_world_frame
#check Solidity.Backend.AbiWorld.heterogeneous_callback_rollback
#check Solidity.Backend.AbiWorld.prependEvents
#check Solidity.Backend.AbiWorld.prependEvents_monotone
#check Solidity.Backend.AbiWorld.prependEvents_assoc
#print axioms Solidity.Yul.World.PeerMemoryAgreement.compiled_input_load
#print axioms Solidity.Yul.World.PeerMemoryAgreement.compiled_byte_survives
#print axioms Solidity.Yul.World.PeerCreationAgreement.compiled_initialization
#print axioms Solidity.Yul.World.PeerCreationAgreement.compiled_success_size
#print axioms Solidity.Yul.World.PeerCreationAgreement.compiled_revert_size
#print axioms Solidity.Yul.World.PeerWorldAgreement.completion_unrelated
#print axioms Solidity.Yul.World.PeerWorldAgreement.child_mark
#print axioms Solidity.Yul.World.PeerWorldAgreement.actual_callback_rollback
#print axioms Solidity.Backend.AbiWorld.unrelated_world_frame
#print axioms Solidity.Backend.AbiWorld.heterogeneous_callback_rollback
#print axioms Solidity.Backend.AbiWorld.prependEvents_monotone
#print axioms Solidity.Backend.AbiWorld.prependEvents_assoc
