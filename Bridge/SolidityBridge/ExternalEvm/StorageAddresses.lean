import SolidityBridge.ExternalEvm.StorageAccounts
import EvmYul.MachineStateOps

/-! Numeric slot interpretation through the actual upstream scratch-memory
and hashing evaluators. No cryptographic equation or injectivity is assumed. -/
namespace Solidity.Evm.StorageSlots

/-- Concrete scratch-memory setup, using upstream MSTORE, independently of
any word-cell memory bridge. Byte extents depend on upstream FFI padding;
this definition alone does not prove canonical serialization. -/
def mapScratch (key parent : EvmYul.UInt256) : EvmYul.MachineState :=
  ((default : EvmYul.MachineState).mstore (.ofNat 0) key).mstore (.ofNat 32) parent

def arrayScratch (parent : EvmYul.UInt256) : EvmYul.MachineState :=
  (default : EvmYul.MachineState).mstore (.ofNat 0) parent

/-- Uses the actual pinned evaluator, including its opaque FFI hash and
padding operations. No equation about cryptographic hashes is postulated. -/
def mapHash (key parent : EvmYul.UInt256) : EvmYul.UInt256 :=
  ((mapScratch key parent).keccak256 (.ofNat 0) (.ofNat 64)).1

def arrayHash (parent : EvmYul.UInt256) : EvmYul.UInt256 :=
  ((arrayScratch parent).keccak256 (.ofNat 0) (.ofNat 32)).1

/-- Offsets wrap in the interpretation, unlike symbolic Slot.add. -/
def address : Slot → EvmYul.UInt256
  | .root n => .ofNat n
  | .hash k p n => if n = 0 then mapHash (encode k) (address p)
      else (mapHash (encode k) (address p)).add (.ofNat n)
  | .data p n => if n = 0 then arrayHash (address p)
      else (arrayHash (address p)).add (.ofNat n)


def wordAddress : Word → EvmYul.UInt256
  | .val v => encode v
  | .slot a => address a

theorem array_hash_setup (s : EvmYul.MachineState) (parent : EvmYul.UInt256)
    (hm : s.memory = (arrayScratch parent).memory) :
    (s.keccak256 (.ofNat 0) (.ofNat 32)).1 = arrayHash parent := by
  change EvmYul.UInt256.ofNat (EvmYul.fromByteArrayBigEndian
    (ffi.KEC (s.memory.readWithPadding 0 32))) = _
  rw [hm]
  rfl

theorem map_hash_setup (s : EvmYul.MachineState) (key parent : EvmYul.UInt256)
    (hm : s.memory = (mapScratch key parent).memory) :
    (s.keccak256 (.ofNat 0) (.ofNat 64)).1 = mapHash key parent := by
  change EvmYul.UInt256.ofNat (EvmYul.fromByteArrayBigEndian
    (ffi.KEC (s.memory.readWithPadding 0 64))) = _
  rw [hm]
  rfl

theorem root_alias : address (.root W) = address (.root 0) := rfl

/-- Narrow written-region assumptions, evaluated after the actual upstream
MSTORE prefix. No relation on the rest of memory is demanded. -/
def ArraySetup (s : EvmYul.MachineState) (parent : EvmYul.UInt256) : Prop :=
  (s.mstore (.ofNat 0) parent).memory.readWithPadding 0 32 =
    (arrayScratch parent).memory.readWithPadding 0 32

def MapSetup (s : EvmYul.MachineState) (key parent : EvmYul.UInt256) : Prop :=
  ((s.mstore (.ofNat 0) key).mstore (.ofNat 32) parent).memory.readWithPadding 0 64 =
    (mapScratch key parent).memory.readWithPadding 0 64

/-- MSTORE's byte result depends only on the initial byte memory and operands,
not gas/activeWords or other machine fields. This is not a byte-layout theorem. -/
theorem mstore_memory_congr (s t : EvmYul.MachineState) (hm : s.memory = t.memory)
    (pos value : EvmYul.UInt256) :
    (s.mstore pos value).memory = (t.mstore pos value).memory := by
  simp only [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord, EvmYul.writeBytes, hm]

theorem array_setup_empty (s : EvmYul.MachineState) (parent : EvmYul.UInt256)
    (hm : s.memory = (default : EvmYul.MachineState).memory) : ArraySetup s parent := by
  unfold ArraySetup arrayScratch
  exact congrArg (fun mem : ByteArray => mem.readWithPadding 0 32)
    (mstore_memory_congr s default hm (.ofNat 0) parent)

theorem map_setup_empty (s : EvmYul.MachineState) (key parent : EvmYul.UInt256)
    (hm : s.memory = (default : EvmYul.MachineState).memory) : MapSetup s key parent := by
  have hfirst := mstore_memory_congr s default hm (.ofNat 0) key
  exact congrArg (fun mem : ByteArray => mem.readWithPadding 0 64)
    (mstore_memory_congr (s.mstore (.ofNat 0) key) ((default : EvmYul.MachineState).mstore (.ofNat 0) key)
      hfirst (.ofNat 32) parent)

theorem array_setup_congr (s t : EvmYul.MachineState) (hm : s.memory = t.memory)
    (parent : EvmYul.UInt256) : ArraySetup s parent ↔ ArraySetup t parent := by
  unfold ArraySetup
  rw [mstore_memory_congr s t hm]

theorem map_setup_congr (s t : EvmYul.MachineState) (hm : s.memory = t.memory)
    (key parent : EvmYul.UInt256) : MapSetup s key parent ↔ MapSetup t key parent := by
  unfold MapSetup
  rw [mstore_memory_congr (s.mstore (.ofNat 0) key) (t.mstore (.ofNat 0) key)
    (mstore_memory_congr s t hm (.ofNat 0) key) (.ofNat 32) parent]

theorem array_hash_read_setup (s : EvmYul.MachineState) (parent : EvmYul.UInt256)
    (hm : s.memory.readWithPadding 0 32 = (arrayScratch parent).memory.readWithPadding 0 32) :
    (s.keccak256 (.ofNat 0) (.ofNat 32)).1 = arrayHash parent := by
  change EvmYul.UInt256.ofNat (EvmYul.fromByteArrayBigEndian (ffi.KEC
    (s.memory.readWithPadding 0 32))) = _
  rw [hm]
  rfl

theorem map_hash_read_setup (s : EvmYul.MachineState) (key parent : EvmYul.UInt256)
    (hm : s.memory.readWithPadding 0 64 = (mapScratch key parent).memory.readWithPadding 0 64) :
    (s.keccak256 (.ofNat 0) (.ofNat 64)).1 = mapHash key parent := by
  change EvmYul.UInt256.ofNat (EvmYul.fromByteArrayBigEndian (ffi.KEC
    (s.memory.readWithPadding 0 64))) = _
  rw [hm]
  rfl

end Solidity.Evm.StorageSlots
