import Solidity.Backend.FailurePaths.ReasonCodec
import Solidity.Backend.MemoryOps.PhysicalByteStore

/-! Disjoint physical word frames through the actual checked payload emitter.
The byte-store producer preserves only untouched words: no abstract overlapping
store, Source transaction rollback or general runtime encoder is inferred. -/
namespace Solidity.Backend.FailurePaths.FramedEmission
open Source
open MemoryOps.Physical

theorem preserve_bytes {m : Evm.Machine} {bytes : Environment.Memory} {live : Nat → Prop}
    (initial : WordFrame m bytes live) (offset : Nat) (payload : Roadmap.Bytes)
    (apart : ∀ c, live c → offset+payload.length≤32*c ∨ 32*c+32≤offset) :
    WordFrame m (Failure.Slice.putBytes bytes offset payload) live := by
  induction payload generalizing bytes offset with
  | nil => exact initial
  | cons b rest ih =>
    have one : ∀ c,live c → offset<32*c ∨ 32*c+32≤offset := by
      intro c hc
      have split := apart c hc
      simp only [List.length_cons] at split
      omega
    have tail : ∀ c,live c → offset+1+rest.length≤32*c ∨ 32*c+32≤offset+1 := by
      intro c hc
      have split := apart c hc
      simp only [List.length_cons] at split
      omega
    rw [Failure.Slice.putBytes,←writeByte_eq_putByte]
    exact ih (initial.writeByte_outside offset b one) (offset+1) tail

/-- Frame validity is about the reached machine of the actual checked program,
not a separately assumed final byte array. The suffix is stopped by the emitter. -/
theorem emitter {m : Evm.Machine} (slice : Failure.Slice.Machine) {live : Nat → Prop}
    (initial : WordFrame m slice.memory live) (offset : Nat) (input : Failure.Input)
    (suffix : Backend.Program) (fits : Failure.Fits offset input.bytes)
    (room : slice.stack.length+2≤1024)
    (apart : ∀ c,live c → offset+input.bytes.length≤32*c ∨ 32*c+32≤offset) :
    ∃ reached,
      Failure.Slice.checkedRun (Failure.emit offset input ++ suffix) slice =
        some (reached,some input.observation) ∧
      WordFrame m reached.memory live ∧ reached.stack=slice.stack :=
  ⟨{slice with memory := Failure.Slice.putBytes slice.memory offset input.bytes},
    Failure.checkedRun_emit_suffix offset input suffix slice fits room,
    preserve_bytes initial offset input.bytes apart,rfl⟩

/-- Existing public literal-statement selection, actual Source execution and
readback are joined with reached physical word-frame preservation. General
runtime ABI and internal-frame failure transport remain separate. -/
theorem compiled_reason {E : Source.Env} {R : List STy} {Γ : RCtx}
    (global : Glob E) (frame : Fr) (extra parameters offset : Nat) (reason : Roadmap.Bytes)
    (locals : Locals E.layout Γ) (state : St E) (suffix : Backend.Program)
    (slice : Failure.Slice.Machine) (m : Evm.Machine) (live : Nat → Prop)
    (initial : WordFrame m slice.memory live)
    (fits : Failure.Fits offset (Source.errorData reason)) (room : slice.stack.length+2≤1024)
    (apart : ∀ c,live c → offset+(Source.errorData reason).length≤32*c ∨ 32*c+32≤offset) :
    Parametric.compile global offset (ReasonCodec.statement (E:=E) (R:=R) (Γ:=Γ) reason) =
      some (Failure.emit offset (.custom (Source.errorData reason))) ∧
    Parametric.Reverts global frame (extra+7) parameters (ReasonCodec.statement (E:=E) (R:=R) (Γ:=Γ) reason)
      locals state (Source.errorData reason) ∧
    ∃ reached,
      Failure.Slice.checkedRun (Failure.emit offset (.custom (Source.errorData reason)) ++ suffix) slice =
        some (reached,some (.revert (Source.errorData reason))) ∧
      WordFrame m reached.memory live ∧ reached.stack=slice.stack ∧
      Semantics.decodeError (Failure.Slice.getBytes reached.memory offset (Source.errorData reason).length) = some reason := by
  have actual := ReasonCodec.compiled_readback (R:=R) global frame extra parameters offset reason locals state suffix slice fits room
  generalize packetEq : Source.errorData reason = packet at *
  refine ⟨actual.1,actual.2.1,
    ({slice with memory := Failure.Slice.putBytes slice.memory offset packet} : Failure.Slice.Machine),
    actual.2.2.1,?_,rfl,actual.2.2.2⟩
  exact @preserve_bytes m slice.memory live initial offset packet apart

#print axioms preserve_bytes
#print axioms emitter
#print axioms compiled_reason
end Solidity.Backend.FailurePaths.FramedEmission
