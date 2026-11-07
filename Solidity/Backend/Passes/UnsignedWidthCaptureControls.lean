import Solidity.Backend.Passes.UnsignedWidthCapture
import Solidity.Backend.PrimitivePackets.UnsignedMul.WideControls

/-! Publicly selected cleanup/capture over a populated caller and old array.
All local/alias/allocator/reserved/sentinel/array cells and saved stack remain
in each ordered vector; numeric cleanup bytes are not whole-pass bytecode. -/
namespace Solidity.Backend.Passes.UnsignedWidthCaptureControls
open Evm Evm.Memory Evm.Compiler Backend.Scalar
open UnsignedWidthCapture
open Backend.PrimitivePackets.UnsignedMul.WideControls (F target machine represented)
open Backend.PrimitivePackets.UnsignedMul.WideControls.Seed (C bases)
def name : Var := .user "cleaned"
def u8 : Fin 32 := ⟨0,by decide⟩
def u16 : Fin 32 := ⟨1,by decide⟩
def u256 : Fin 32 := ⟨31,by decide⟩
def actual (w : Fin 32) := code (C := C) 1 F w .here name

theorem inhabited (w : Fin 32) (x : Fin W) :
    type_of% (application w .here name (represented x (wmod 9)) (by decide)) :=
  application w .here name (represented x (wmod 9)) (by decide)

def cells : List Nat := [5,4,3,2,1,0,16,63,128,129]
def observe : Evm.Out → Option (List Evm.Word × List Evm.Word)
  | .ok m _ => some (cells.map m.mem,m.stack)
  | _ => none

theorem initial_vector : (cells.map (machine (wmod 291) (wmod 9)).mem,(machine (wmod 291) (wmod 9)).stack) =
    ([w[0],w[291],w[9],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem low_byte : observe (Evm.run (actual u8).code (machine (wmod 291) (wmod 9))) =
    some ([w[35],w[0],w[9],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem wider_word : observe (Evm.run (actual u16).code (machine (wmod 291) (wmod 9))) =
    some ([w[291],w[0],w[9],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem sign_bit_stays_unsigned : observe (Evm.run (actual u8).code (machine (wmod 255) (wmod 9))) =
    some ([w[255],w[0],w[9],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem full_width_maximum : observe (Evm.run (actual u256).code (machine (wmod (W-1)) (wmod 9))) =
    some ([w[W-1],w[0],w[9],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem out_of_width_is_success (tail : List Evm.Word) :
    Evm.run (actual u8).code {(machine (wmod 291) (wmod 9)) with stack := tail} ≠ .revert :=
  never_reverts u8 .here name (represented (wmod 291) (wmod 9)) (by decide) tail

def wrongProgram : Prog C Backend.PrimitivePackets.UnsignedMul.WideControls.Γ
    (.val .uint :: Backend.PrimitivePackets.UnsignedMul.WideControls.Γ) :=
  .cons (.assignLocal .here (.simple (.lit 0 (by decide))))
    (.cons (.declLocal .uint name (some (expression u8 .here))) .nil)
def wrong : CompiledProg 1 F wrongProgram := (Memory.compileProg 1 F wrongProgram).get (by rfl)
theorem wrong_public : Memory.compileProg 1 F wrongProgram = some wrong := by rfl

theorem wrong_order : observe (Evm.run wrong.code (machine (wmod 291) (wmod 9))) =
    some ([w[0],w[0],w[9],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem wrong_native_read : (expression u8 (.here : Idx Backend.PrimitivePackets.UnsignedMul.WideControls.Γ (.val .uint))).evalT
    ((target (wmod 291) (wmod 9)).setLocal .here zero) = .ok zero := by rfl

theorem read_captured : observe (Evm.run ((actual u8).code ++ (reader (C := C) 1 F u8 .here name).code)
    (machine (wmod 291) (wmod 9))) =
    some ([w[35],w[0],w[9],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[35],w[77]]) := by decide +kernel

theorem stale_read : observe (Evm.run ((actual u8).code ++ [.mload (cell 4)]) (machine (wmod 291) (wmod 9))) =
    some ([w[35],w[0],w[9],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[0],w[77]]) := by decide +kernel

theorem corrupted_tail : observe (Evm.run (actual u8).code {(machine (wmod 291) (wmod 9)) with stack := [w[88]]}) ≠
    some ([w[35],w[0],w[9],w[7],w[128],w[130],w[20],w[99],w[1],w[0]],[w[77]]) := by decide +kernel

theorem insufficient_frame : ¬ (Compilation.memory (actual u8)).Input 1 5 bases
    (target (wmod 291) (wmod 9)) (machine (wmod 291) (wmod 9)) := by
  intro h
  have bad : 6 ≤ 5 := h.2.1
  omega

/-- Exact bytes of the owner's independent numeric cleanup fragment only. -/
theorem numeric_bytes : Backend.encode (unsignedCode u8) =
    [127] ++ List.replicate 31 0 ++ [255,22] := by decide +kernel

/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inhabited
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.initial_vector' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms initial_vector
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.low_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_byte
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.wider_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wider_word
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.sign_bit_stays_unsigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_bit_stays_unsigned
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.full_width_maximum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms full_width_maximum
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.out_of_width_is_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms out_of_width_is_success
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.wrong_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_public
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_order
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.wrong_native_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_native_read
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.read_captured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms read_captured
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.stale_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stale_read
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.corrupted_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corrupted_tail
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.insufficient_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms insufficient_frame
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCaptureControls.numeric_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms numeric_bytes
end Solidity.Backend.Passes.UnsignedWidthCaptureControls
