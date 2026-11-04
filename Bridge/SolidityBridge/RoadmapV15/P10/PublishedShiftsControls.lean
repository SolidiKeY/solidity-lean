import SolidityBridge.RoadmapV15.P10.PublishedShifts
import SolidityBridge.RoadmapV15.P10.LogicalShiftFixtures
import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Explicit unchecked Source clients and populated two-step native records.
Counts retain all256bits; no physical load, frame or whole compiler claim. -/
namespace SolidityBridge.RoadmapV15.P10.PublishedShiftsControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open Solidity.Backend.PrimitivePackets.Shifts
open PublishedShifts
open WordPushFixtures (seed before after spill u accounts)
namespace Fixture
export Solidity.Backend.PrimitivePackets.SignedMod.Controls (E globals frame)
end Fixture

def word (n : Nat) (h : n<Solidity.Evm.W) : Fin Solidity.Evm.W := ⟨n,h⟩
def source (x k : Fin Solidity.Evm.W) : Source.EMState Fixture.E SourceCtx :=
  (locals (x.val:Int) (word_range x) (k.val:Int) (word_range k),Source.St.init Fixture.E)

private theorem word_bits (n : Nat) (h : n<Solidity.Evm.W) :
    BitVec.ofFin (word n h)=BitVec.ofNat 256 n := by
  apply BitVec.eq_of_toNat_eq
  change n=n%2^256
  exact (Nat.mod_eq_of_lt h).symm

private theorem shape (op : Backend.Op) (perm : Bool) (value count result : Scalar.Word) :
    (Assembly.chargedPrepare (logicalShiftSwapped (seed 12 perm) before after op value count spill) 3).replaceStackAndIncrPC
      ((result::spill).map (fun z=>UInt256.mk z.toFin))=
      LogicalShiftFixtures.observed op 12 perm value count spill result := by
  simp only [LogicalShiftFixtures.observed,LogicalShiftFixtures.input,logicalShiftInput,logicalShiftSwapped,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
    WordPushFixtures.seed,WordPushFixtures.u,WordPushFixtures.before]
  rfl

theorem shl_client (pipeline : Roadmap.Pipeline) (perm : Bool) (x k : Fin Solidity.Evm.W) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame false) 3
      (Src.expression true .here (.there .here))).run (source x k)=
      (.ok (.val (.int ((resultWord true x k).val:Int) (word_range (resultWord true x k)))),source x k) ∧
    Scalar.run Scalar.uintShl.code (BitVec.ofFin x::BitVec.ofFin k::spill)=some (BitVec.ofFin (resultWord true x k)::spill) ∧
    Assembly.driverSteps 2 3 #[] (LogicalShiftFixtures.input .SHL 12 perm (BitVec.ofFin x) (BitVec.ofFin k) spill)=
      .ok (LogicalShiftFixtures.observed .SHL 12 perm (BitVec.ofFin x) (BitVec.ofFin k) spill (BitVec.ofFin (resultWord true x k))) ∧
    EVM.X 3 #[] (LogicalShiftFixtures.input .SHL 12 perm (BitVec.ofFin x) (BitVec.ofFin k) spill)=
      EVM.X 1 #[] (LogicalShiftFixtures.observed .SHL 12 perm (BitVec.ofFin x) (BitVec.ofFin k) spill (BitVec.ofFin (resultWord true x k))) := by
  have h := shl_fetched (Fixture.globals pipeline) (Fixture.frame false) 0 (source x k).1 (source x k).2
    .here (.there .here) x k rfl rfl (seed 12 perm) before after spill LogicalShiftFixtures.fits (by decide) (by change 6≤12;decide) 0
  dsimp only at h
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem shr_client (pipeline : Roadmap.Pipeline) (perm : Bool) (x k : Fin Solidity.Evm.W) :
    (Source.evalE (Fixture.globals pipeline) (Fixture.frame false) 3
      (Src.expression false .here (.there .here))).run (source x k)=
      (.ok (.val (.int ((resultWord false x k).val:Int) (word_range (resultWord false x k)))),source x k) ∧
    Scalar.run Scalar.uintShr.code (BitVec.ofFin x::BitVec.ofFin k::spill)=some (BitVec.ofFin (resultWord false x k)::spill) ∧
    Assembly.driverSteps 2 3 #[] (LogicalShiftFixtures.input .SHR 12 perm (BitVec.ofFin x) (BitVec.ofFin k) spill)=
      .ok (LogicalShiftFixtures.observed .SHR 12 perm (BitVec.ofFin x) (BitVec.ofFin k) spill (BitVec.ofFin (resultWord false x k))) ∧
    EVM.X 3 #[] (LogicalShiftFixtures.input .SHR 12 perm (BitVec.ofFin x) (BitVec.ofFin k) spill)=
      EVM.X 1 #[] (LogicalShiftFixtures.observed .SHR 12 perm (BitVec.ofFin x) (BitVec.ofFin k) spill (BitVec.ofFin (resultWord false x k))) := by
  have h := shr_fetched (Fixture.globals pipeline) (Fixture.frame false) 0 (source x k).1 (source x k).2
    .here (.there .here) x k rfl rfl (seed 12 perm) before after spill LogicalShiftFixtures.fits (by decide) (by change 6≤12;decide) 0
  dsimp only at h
  rw [shape] at h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem nonzero_clients (pipeline : Roadmap.Pipeline) (perm : Bool) :
    Assembly.driverSteps 2 3 #[] (LogicalShiftFixtures.input .SHL 12 perm 3 2 spill)=
      .ok (LogicalShiftFixtures.observed .SHL 12 perm 3 2 spill 12) ∧
    Assembly.driverSteps 2 3 #[] (LogicalShiftFixtures.input .SHR 12 perm 128 7 spill)=
      .ok (LogicalShiftFixtures.observed .SHR 12 perm 128 7 spill 1) := by
  have hl := (shl_client pipeline perm (word 3 (by decide)) (word 2 (by decide))).2.2.1
  have hr := (shr_client pipeline perm (word 128 (by decide)) (word 7 (by decide))).2.2.1
  have ol : (BitVec.ofFin (resultWord true (word 3 (by decide)) (word 2 (by decide))) : Scalar.Word)=12 := by decide
  have oright : (BitVec.ofFin (resultWord false (word 128 (by decide)) (word 7 (by decide))) : Scalar.Word)=1 := by decide
  rw [ol] at hl
  rw [oright] at hr
  exact ⟨by simpa only [word_bits] using hl,by simpa only [word_bits] using hr⟩

theorem count_boundaries (pipeline : Roadmap.Pipeline) (perm : Bool) :
    Assembly.driverSteps 2 3 #[] (LogicalShiftFixtures.input .SHL 12 perm 258 0 spill)=
      .ok (LogicalShiftFixtures.observed .SHL 12 perm 258 0 spill 258) ∧
    Assembly.driverSteps 2 3 #[] (LogicalShiftFixtures.input .SHL 12 perm 1 255 spill)=
      .ok (LogicalShiftFixtures.observed .SHL 12 perm 1 255 spill (BitVec.ofNat 256 (2^255))) ∧
    Assembly.driverSteps 2 3 #[] (LogicalShiftFixtures.input .SHL 12 perm 1 256 spill)=
      .ok (LogicalShiftFixtures.observed .SHL 12 perm 1 256 spill 0) ∧
    Assembly.driverSteps 2 3 #[] (LogicalShiftFixtures.input .SHR 12 perm (BitVec.ofNat 256 ((2^256:Nat)-1)) (BitVec.ofNat 256 ((2^256:Nat)-1)) spill)=
      .ok (LogicalShiftFixtures.observed .SHR 12 perm (BitVec.ofNat 256 ((2^256:Nat)-1)) (BitVec.ofNat 256 ((2^256:Nat)-1)) spill 0) := by
  have hz := (shl_client pipeline perm (word 258 (by decide)) (word 0 (by decide))).2.2.1
  have he := (shl_client pipeline perm (word 1 (by decide)) (word 255 (by decide))).2.2.1
  have hs := (shl_client pipeline perm (word 1 (by decide)) (word 256 (by decide))).2.2.1
  have hm := (shr_client pipeline perm (word ((2^256:Nat)-1) (by decide)) (word ((2^256:Nat)-1) (by decide))).2.2.1
  have oz : (BitVec.ofFin (resultWord true (word 258 (by decide)) (word 0 (by decide))) : Scalar.Word)=258 := by decide
  have oe : BitVec.ofFin (resultWord true (word 1 (by decide)) (word 255 (by decide)))=BitVec.ofNat 256 (2^255) := by decide
  have os : (BitVec.ofFin (resultWord true (word 1 (by decide)) (word 256 (by decide))) : Scalar.Word)=0 := by decide
  have om : (BitVec.ofFin (resultWord false (word ((2^256:Nat)-1) (by decide)) (word ((2^256:Nat)-1) (by decide))) : Scalar.Word)=0 := by decide
  rw [oz] at hz
  rw [oe] at he
  rw [os] at hs
  rw [om] at hm
  exact ⟨by simpa only [word_bits] using hz,by simpa only [word_bits] using he,
    by simpa only [word_bits] using hs,by simpa only [word_bits] using hm⟩

theorem complete_observation (perm : Bool) :
    let next := LogicalShiftFixtures.observed .SHL 12 perm 3 2 spill 12
    next.stack=[u 12,u 258,u 513] ∧ next.stack≠[u 16,u 258,u 513] ∧ next.stack≠[u 12,u 513,u 258] ∧
    next.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x90,0x1b,0x00] ∧
    next.pc=u 5 ∧ next.gasAvailable=u 6 ∧ next.execLength=43 ∧
    next.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    next.returnData.data.toList=[0xcc,0xdd] ∧ next.H_return.data.toList=[0xee,0xff] ∧
    next.executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧ next.accountMap=accounts ∧ next.σ₀=accounts ∧
    (BitVec.ofFin (resultWord true (word 1 (by decide)) (word 256 (by decide))) : Scalar.Word)≠1 := by
  refine ⟨rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  · change [u 12,u 258,u 513]≠[u 16,u 258,u 513];decide
  · change [u 12,u 258,u 513]≠[u 12,u 513,u 258];decide
  · decide

#print axioms shl_client
#print axioms shr_client
#print axioms nonzero_clients
#print axioms count_boundaries
#print axioms complete_observation
end SolidityBridge.RoadmapV15.P10.PublishedShiftsControls
