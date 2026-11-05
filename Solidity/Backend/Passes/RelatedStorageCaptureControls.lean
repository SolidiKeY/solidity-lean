import Solidity.Backend.Passes.RelatedStorageCapture
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.Passes.RelatedStorageCapture.Controls
open Evm Evm.Compiler Solidity.Lowering.V07
open Source.SemanticsExamples (F0 s0 toyFixed)
def C : Contract := {vars := [("live",.ref bytesR),("other",.ref bytesR)]}
def live : SRef C (.ref bytesR) := SRef.ofRoot "live" rfl
def other : SRef C (.ref bytesR) := SRef.ofRoot "other" rfl
abbrev Γ : Ctx := [.alias bytesR,.alias bytesR]
abbrev F := Frag.init Γ
def state : State C Γ := ((State.init C).push (t := .alias bytesR) (some other)).push (t := .alias bytesR) (some live)
def machine : Machine := Memory.writeMachine (Memory.writeMachine Machine.init 0 (.slot (.root 1))) 1 (.slot (.root 0))
def program : Prog C Γ (.alias bytesR :: Γ) := storageCapture .here
def outFrag : Frag (.alias bytesR :: Γ) := F.push (.alias bytesR) .ok
theorem certificate : inFragP F program = some outFrag := by decide +kernel
def checked : Compilation 0 F program := .core outFrag certificate

theorem public_code : (Compiler.compile 0 F program).map (·.code) = some checked.code := by rfl

theorem represented : Sim C 1 0 F state machine := by
  have h := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  have first := h.consAlias (PathSlot.root (C := C) (r := "other") rfl)
  have second := first.consAlias (PathSlot.root (C := C) (r := "live") rfl)
  apply second.congrLook
  intro t i
  cases i with
  | here => rfl
  | there i => cases i with
    | here => rfl
    | there i => nomatch i

theorem input : checked.Input 1 0 (fun _ => wmod 0) state machine :=
  ⟨represented,by decide +kernel⟩

def E : Source.Env := ⟨[⟨.stateVar,"live",some "C",false,
  .stateVar (.elem .bytes) none none none false "live" .none⟩,
  ⟨.stateVar,"other",some "C",false,
  .stateVar (.elem .bytes) none none none false "other" .none⟩]⟩
def P : Source.Program E where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []
def G (pipeline : Roadmap.Pipeline) : Source.Glob E :=
  ⟨P,pipeline,toyFixed,fun _ => Source.SemanticsExamples.word 0,fun _ _ => false,fun _ => .answer (.success []),Source.SemanticsExamples.word 0⟩
def path : Source.SPath := ⟨⟨some "C","live"⟩,[]⟩
abbrev srcΓ : Source.RCtx := [.bytes .storage]
def source : Source.EMState E srcΓ := (.cons (.storRef rfl path) .nil,s0)
def alignment : ContextMap srcΓ Γ :=
  (ContextMap.empty.wk (.drop .refl)).cons (.bytes .storage) (.alias bytesR)
def relation (τ : Source.STy) (u : LTy) : Source.Val E.layout τ → u.TDenote C [] → Prop :=
  match τ,u with
  | .bytes .storage,.alias (.array (.prim .uint)) =>
    fun value ref => value = .storRef rfl path ∧ ref = some live
  | _,_ => fun _ _ => False

theorem aligned : alignment.Related relation source.1 state.env := by
  intro τ i
  cases i with
  | here => exact ⟨rfl,rfl⟩
  | there i => nomatch i

def application (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  execution (G pipeline) F0 fuel source state alignment relation aligned .here .here path live
    rfl rfl rfl certificate rfl input

def wrongProgram : Prog C Γ (.alias bytesR :: Γ) := storageCapture (.there .here)
theorem wrong_certificate : inFragP F wrongProgram = some outFrag := by decide +kernel
def wrong : Compilation 0 F wrongProgram := .core outFrag wrong_certificate

def cells : List Nat := [0,1,2,3]
private def observe : Evm.Out → Option (List Word × List Word)
  | .ok m 0 => some (cells.map m.mem,m.stack)
  | _ => none

theorem complete_vector : observe (run (checked.code ++ [.mload 2]) {machine with stack := [w[77],w[88]]}) =
    some ([.slot (.root 1),.slot (.root 0),.slot (.root 0),w[0]],
      [.slot (.root 0),w[77],w[88]]) := by decide +kernel

theorem wrong_vector : observe (run (wrong.code ++ [.mload 2]) {machine with stack := [w[77],w[88]]}) =
    some ([.slot (.root 1),.slot (.root 0),.slot (.root 1),w[0]],
      [.slot (.root 1),w[77],w[88]]) := by decide +kernel

theorem wrong_alias_refused : observe (run (checked.code ++ [.mload 2]) {machine with stack := [w[77],w[88]]}) ≠
    observe (run (wrong.code ++ [.mload 2]) {machine with stack := [w[77],w[88]]}) := by
  rw [complete_vector,wrong_vector]
  decide

theorem skipped_capture_refused : observe (run (checked.code ++ [.mload 2]) {machine with stack := [w[77],w[88]]}) ≠
    observe (run [.mload 2] {machine with stack := [w[77],w[88]]}) := by decide +kernel

theorem numeric_slot_collapse_refused : observe (run (checked.code ++ [.mload 2]) {machine with stack := [w[77],w[88]]}) ≠
    some ([.slot (.root 1),.slot (.root 0),w[0],w[0]],[w[0],w[77],w[88]]) := by
  rw [complete_vector]
  decide

end Solidity.Backend.Passes.RelatedStorageCapture.Controls
