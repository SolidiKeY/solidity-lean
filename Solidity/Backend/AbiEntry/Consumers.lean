import Solidity.Backend.AbiEntry.RejectionInterface
import Solidity.Backend.AbiEntry.CompositionInterface
import Solidity.Backend.AbiEntry.EntryTransport
import Solidity.Backend.AbiEntry.EntryComposition

/-! Actual inhabitants of the narrow, previously committed helper interfaces.
These reuse the V13 proofs, not an assumed runner or decoder success. Rejection
is conditional emitter execution; composition is semantic entry recursion.
Neither is a certificate for emitted calldata decoding or complete entry. -/
namespace Solidity.Backend.AbiEntry.Consumers

def rejection : Interface.RejectionConsumer EntryTransport.rejection where
  selected := EntryTransport.rejection_iff
  checked := EntryTransport.entry_revert_exec

def orderedEntry : Interface.EntryCompositionCertificate EntryComposition.appendEntries where
  head_extent := EntryComposition.heads_append
  ordered := EntryComposition.enter_append

/-- info: 'Solidity.Backend.AbiEntry.Consumers.rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rejection
/-- info: 'Solidity.Backend.AbiEntry.Consumers.orderedEntry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms orderedEntry
end Solidity.Backend.AbiEntry.Consumers
