import Solidity.Backend.Passes.RelatedMemoryCapture
import Solidity.Backend.Passes.EffectfulReferencePairControls

namespace Solidity.Backend.Passes.RelatedMemoryCapture.Controls
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open CompileExamples
open Source.SemanticsExamples (E0 G0 F0)
abbrev srcΓ : Source.RCtx := [.bytes .memory]
abbrev oldIndex : Idx Γ (.mem bytesR) := .there .here
abbrev newIndex : Idx Γ (.mem bytesR) := .there (.there (.there .here))
def source : Source.EMState E0 srcΓ :=
  (.cons (.memRef rfl 0) .nil,EffectfulReferencePair.Controls.source.2)
def alignment : ContextMap srcΓ Γ :=
  ((ContextMap.empty.wk (.drop (.drop .refl))).cons (.bytes .memory) (.mem bytesR)).wk (.drop .refl)
def relation (τ : Source.STy) (u : LTy) : Source.Val E0.layout τ → u.TDenote C H → Prop :=
  match τ,u with
  | .bytes .memory,.mem (.array (.prim .uint)) =>
      fun value ref => ∃ r : HRef H bytesR, ref = some r ∧ value = .memRef rfl r.id
  | _,_ => fun _ _ => False

theorem aligned : alignment.Related relation source.1 σ.env := by
  intro τ i
  cases i with
  | here => exact ⟨r0,rfl,rfl⟩
  | there i => nomatch i

def program : Prog C Γ (.mem bytesR :: Γ) := memoryCapture oldIndex rfl
def compiled : CompiledProg 0 (Frag.init Γ) program :=
  (Memory.compileProg 0 (Frag.init Γ) program).get (by decide +kernel)
theorem input : (Compilation.memory compiled).Input 1 6 base σ machine :=
  ⟨fixture_six_cells,by decide +kernel,.inl rfl⟩

def application (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  execution (G0 pipeline) F0 fuel source σ alignment relation aligned .here oldIndex
    0 r0 rfl rfl rfl compiled input

def wrongProgram : Prog C Γ (.mem bytesR :: Γ) := memoryCapture newIndex rfl
def wrong : CompiledProg 0 (Frag.init Γ) wrongProgram :=
  (Memory.compileProg 0 (Frag.init Γ) wrongProgram).get (by decide +kernel)
def cells : List Nat := [4,3,2,1,0,10,16,17,18,20,21]
private def observation : Evm.Out → Option (List Word × List Word)
  | .ok m 0 => some (cells.map m.mem,m.stack)
  | _ => none

theorem source_heap_live : source.2.heap.get 0 = some ⟨.bytes .memory,.bytes [7,9]⟩ ∧
    source.2.heap.get 1 = some ⟨.bytes .memory,.bytes [4]⟩ := ⟨rfl,rfl⟩

theorem initial_vector : (cells.map machine.mem,machine.stack) =
    ([w[0],w[0],w[16],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]],[]) := rfl

theorem complete_vector : observation (run (compiled.code ++ [.mload 4])
    {machine with stack := [w[77],w[88]]}) =
    some ([w[16],w[0],w[16],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]],
      [w[16],w[77],w[88]]) := by decide +kernel

theorem wrong_vector : observation (run (wrong.code ++ [.mload 4])
    {machine with stack := [w[77],w[88]]}) =
    some ([w[20],w[0],w[16],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]],
      [w[20],w[77],w[88]]) := by decide +kernel

theorem wrong_reference_refused : observation (run (compiled.code ++ [.mload 4])
    {machine with stack := [w[77],w[88]]}) ≠ observation (run (wrong.code ++ [.mload 4])
    {machine with stack := [w[77],w[88]]}) := by
  rw [complete_vector,wrong_vector]
  decide

theorem skipped_capture_refused : observation (run (compiled.code ++ [.mload 4])
    {machine with stack := [w[77],w[88]]}) ≠ observation (run [.mload 4]
    {machine with stack := [w[77],w[88]]}) := by decide +kernel

theorem wrong_relation_refused : ¬ relation (.bytes .memory) (.mem bytesR)
    (.memRef rfl 0) (some r1) := by
  rintro ⟨r,hr,hv⟩
  have same : r1 = r := Option.some.inj hr
  subst r
  cases hv

theorem corrupted_tail_refused : observation (run (compiled.code ++ [.mload 4])
    {machine with stack := [w[77],w[88]]}) ≠
    some ([w[16],w[0],w[16],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]],
      [w[16],w[78],w[88]]) := by
  rw [complete_vector]
  decide

end Solidity.Backend.Passes.RelatedMemoryCapture.Controls
