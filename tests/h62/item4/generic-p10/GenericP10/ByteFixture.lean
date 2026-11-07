import SolidityBridge.RoadmapV15.P10.ByteObservation

/-! Additive BYTE fixtures. The execution proof consumes the actual fetched
native semantics; fixture arithmetic never decides a whole execution result. -/
namespace GenericP10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open SolidityBridge.RoadmapV15.P10

/-- Any complete native site and stack tail, with the original resource bounds.
The word equality is byte algebra; fetched execution and continuation follow
from the existing semantic theorem, rather than from a finite decision table. -/
theorem execute (site : Site .BYTE) (index value result : Scalar.Word)
    (word : UInt256.byteAt (UInt256.mk index.toFin) (UInt256.mk value.toFin) = UInt256.mk result.toFin)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (index :: value :: tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (UInt256.mk result.toFin :: tail.map (fun w => UInt256.mk w.toFin))
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  simpa only [word] using (byte_fetched site index value tail room gas fuel)

/-- A native word index/value and an intrinsically byte-sized result. -/
structure ByteFixture where
  index : Fin UInt256.size
  value : Fin UInt256.size
  result : Fin 256
  word_eq : UInt256.byteAt (UInt256.ofNat index.val) (UInt256.ofNat value.val) =
    UInt256.ofNat result.val

/-- Exactly the nine original positive BYTE execution controls. -/
inductive ByteCase where
  | first | second | middle | penultimate | last | outside | maximumIndex | zero | maximumWord

private def payload : Nat := 0x12*2^248+0x34*2^240+0x56*256+0x78

/-- Typed fixture values; the original boundary indices and words are retained. -/
def fixtureValues : ByteCase → Fin UInt256.size × Fin UInt256.size × Fin 256
  | .first => (0,Fin.ofNat _ payload,0x12)
  | .second => (1,Fin.ofNat _ payload,0x34)
  | .middle => (15,Fin.ofNat _ payload,0)
  | .penultimate => (30,Fin.ofNat _ payload,0x56)
  | .last => (31,Fin.ofNat _ payload,0x78)
  | .outside => (32,Fin.ofNat _ payload,0)
  | .maximumIndex => (Fin.ofNat _ (2^256-1),Fin.ofNat _ payload,0)
  | .zero => (0,0,0)
  | .maximumWord => (31,Fin.ofNat _ (2^256-1),255)

/-- Closed byte algebra only. No fetched execution is decided by this table. -/
theorem fixture_word (c : ByteCase) :
    UInt256.byteAt (UInt256.ofNat (fixtureValues c).1.val)
      (UInt256.ofNat (fixtureValues c).2.1.val) = UInt256.ofNat (fixtureValues c).2.2.val := by
  cases c <;> rfl

/-- Every table row contains its byte-algebra witness. -/
def fixture (c : ByteCase) : ByteFixture :=
  ⟨(fixtureValues c).1,(fixtureValues c).2.1,(fixtureValues c).2.2,fixture_word c⟩

/-- info: 'GenericP10.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms execute
/-- info: 'GenericP10.fixture_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixture_word
/-- info: 'GenericP10.fixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixture

end GenericP10
