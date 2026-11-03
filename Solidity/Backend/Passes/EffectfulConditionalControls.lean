import Solidity.Backend.Passes.EffectfulConditionalAssignment
import Solidity.Backend.Passes.PositiveAllocationFailure
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.Passes.EffectfulConditionalAssignment.Controls
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open Source.SemanticsExamples (E0 G0 F0 s0)
abbrev C := PositiveAllocationFailure.C
abbrev Γ : Ctx := [.val .bool,.val .bool,.val .bool,.val .bool,.val .uint]
abbrev srcΓ : Source.RCtx := [.bool,.bool,.bool,.bool]
abbrev F := Frag.init Γ
abbrev ci : Idx Γ (.val .bool) := .here
abbrev ca : Idx Γ (.val .bool) := .there .here
abbrev j : Idx Γ (.val .bool) := .there (.there .here)
abbrev b : Idx Γ (.val .bool) := .there (.there (.there .here))
def state (x : Bool) : State C Γ :=
  (((PositiveAllocationFailure.before.push (t := .val .bool) false).push
    (t := .val .bool) true).push (t := .val .bool) x).push (t := .val .bool) false
def source (x : Bool) : Source.EMState E0 srcΓ :=
  (.cons (.bool false) (.cons (.bool x) (.cons (.bool true) (.cons (.bool false) .nil))),s0)
def alignment : ContextMap srcΓ Γ :=
  ((((ContextMap.empty.wk (.drop .refl)).cons .bool (.val .bool)).cons
    .bool (.val .bool)).cons .bool (.val .bool)).cons .bool (.val .bool)
def relation (τ : Source.STy) (u : LTy) :
    Source.Val E0.layout τ → u.TDenote C [] → Prop :=
  match τ,u with
  | .bool,.val .bool => fun v x => v = .bool x
  | _,_ => fun _ _ => False

theorem aligned (x : Bool) : alignment.Related relation (source x).1 (state x).env := by
  intro τ idx
  cases idx with
  | here => rfl
  | there idx => cases idx with
    | here => rfl
    | there idx => cases idx with
      | here => rfl
      | there idx => cases idx with
        | here => rfl
        | there idx => nomatch idx

/-- One compiled program for both runtime choices; the selected true arm
writes the SAME caller local which originally held the condition. -/
def program : Prog C Γ (.val .bool :: .val .bool :: Γ) :=
  ConditionalAssignments.code ci ca ci b j b
def compiled : CompiledProg 1 F program := (Memory.compileProg 1 F program).get (by decide +kernel)
def readback : CompiledVal 1 compiled.frag (.simple (.local .here) : Val C (.val .bool :: .val .bool :: Γ) .bool) :=
  (Memory.compileVal 1 compiled.frag (.simple (.local .here))).get (by decide +kernel)
def machine (x : Bool) : Machine :=
  {writeMachine (writeMachine (writeMachine (writeMachine (PositiveAllocationFailure.machine (wmod 64))
    2 w[0]) 3 w[1]) 4 (.val (bword x))) 5 w[0] with stack := []}

theorem represented (x : Bool) : StateRepr 1 1 16 F (state x) PositiveAllocationFailure.base (machine x) := by
  have h := (PositiveAllocationFailure.initial (wmod 64) (by decide)).1
  exact ((((h.consVal (p := .bool) false w[0] rfl (by decide)).consVal (p := .bool)
    true w[1] rfl (by decide)).consVal (p := .bool) x (.val (bword x)) rfl (by decide)).consVal
    (p := .bool) false w[0] rfl (by decide)).stack []

theorem input (x : Bool) : (Compilation.memory compiled).Input 1 16 PositiveAllocationFailure.base (state x) (machine x) :=
  ⟨represented x,by decide +kernel,.inl rfl⟩

def application (pipeline : Roadmap.Pipeline) (fuel : Nat) (x : Bool) :=
  execution (G0 pipeline) F0 fuel (source x) (state x) alignment relation (aligned x)
    (fun _ _ h => h) .here (.there .here) .here (.there (.there (.there .here)))
    (.there (.there .here)) (.there (.there (.there .here))) ci ca ci b j b rfl rfl rfl rfl rfl rfl
    compiled readback (input x)

def cells : List Nat := [0,1,2,3,4,5,6,7,8,9]
private def okMachine : Evm.Out → Option Machine
  | .ok m 0 => some m | _ => none
private theorem extracted {out : Evm.Out} (h : (okMachine out).isSome) :
    out = .ok ((okMachine out).get h) 0 := by
  cases out with
  | ok m skip => cases skip with
    | zero => rfl
    | succ n => cases h
  | revert => cases h
  | fault => cases h
@[irreducible] def executed (x : Bool) : Machine :=
  (okMachine (run compiled.code (machine x))).get (by cases x <;> decide +kernel)
def observed (x : Bool) (tail : List Word) : Machine := {executed x with stack := tail}
theorem actual (x : Bool) : run compiled.code (machine x) = .ok (executed x) 0 := by
  unfold executed
  exact extracted _
theorem target_tail (x : Bool) (tail : List Word) :
    run compiled.code {machine x with stack := tail} = .ok (observed x tail) 0 := by
  have ht := compilation_tail_exact (.memory compiled) (input x) (payment_free ci ca ci b j b) tail
  change run compiled.code {machine x with stack := tail} = replaceOutStack tail (run compiled.code (machine x)) at ht
  simpa only [actual,replaceOutStack,observed] using ht

theorem initial_vector (x : Bool) : (cells.map (machine x).mem,(machine x).stack) =
    ([w[64],w[0],w[0],w[1],.val (bword x),w[0],w[0],w[0],w[10],w[99]],[]) := by
  cases x <;> rfl

theorem complete_vector (x : Bool) (tail : List Word) : (cells.map (observed x tail).mem,(observed x tail).stack) =
    ([w[64],w[0],w[0],.val (bword x),.val (bword x),w[0],.val (bword x),w[0],w[10],w[99]],tail) := by
  apply Prod.ext
  · change cells.map (executed x).mem =
      [w[64],w[0],w[0],.val (bword x),.val (bword x),w[0],.val (bword x),w[0],w[10],w[99]]
    cases x <;> with_unfolding_all decide +kernel
  · rfl

def eagerSuffix : Prog C (.val .bool :: .val .bool :: Γ) (.val .bool :: .val .bool :: Γ) :=
  ConditionalAssignments.branch j b
def eager : CompiledProg 1 compiled.frag eagerSuffix :=
  (Memory.compileProg 1 compiled.frag eagerSuffix).get (by decide +kernel)

def recaptureSuffix : Prog C (.val .bool :: .val .bool :: Γ) (.val .bool :: .val .bool :: Γ) :=
  .cons (.assignLocal (.there .here) (.simple (.local (.there (.there ci)))))
    (.cons (.ite (.simple (.local (.there .here)))
      (ConditionalAssignments.branch ci b) (ConditionalAssignments.branch j b)) .nil)
def recapture : CompiledProg 1 compiled.frag recaptureSuffix :=
  (Memory.compileProg 1 compiled.frag recaptureSuffix).get (by decide +kernel)
private def observation : Evm.Out → Option (List Word × List Word)
  | .ok m 0 => some (cells.map m.mem,m.stack)
  | _ => none

theorem readback_vector (x : Bool) : observation (run (compiled.code ++ readback.code)
    {machine x with stack := [w[77],w[88]]}) =
    some ([w[64],w[0],w[0],.val (bword x),.val (bword x),w[0],.val (bword x),w[0],w[10],w[99]],
      [w[0],w[77],w[88]]) := by
  cases x <;> with_unfolding_all decide +kernel

theorem insufficient_frame (x : Bool) :
    ¬ (Compilation.memory compiled).Input 1 6 PositiveAllocationFailure.base (state x) (machine x) := by
  intro h
  have bound := h.2.1
  have need : 6 < 1 + frameNeedProg program := by decide +kernel
  omega

theorem eager_vector : observation (run (compiled.code ++ eager.code)
    {machine true with stack := [w[77],w[88]]}) =
    some ([w[64],w[0],w[0],w[0],w[1],w[0],w[1],w[0],w[10],w[99]],[w[77],w[88]]) := by
  with_unfolding_all decide +kernel

theorem recapture_vector : observation (run (compiled.code ++ recapture.code)
    {machine true with stack := [w[77],w[88]]}) =
    some ([w[64],w[0],w[0],w[0],w[1],w[0],w[0],w[0],w[10],w[99]],[w[77],w[88]]) := by
  with_unfolding_all decide +kernel

theorem eager_false_arm_refused : observation (run compiled.code {machine true with stack := [w[77],w[88]]}) ≠
    observation (run (compiled.code ++ eager.code) {machine true with stack := [w[77],w[88]]}) := by
  rw [target_tail,eager_vector]
  change some (cells.map (observed true [w[77],w[88]]).mem,_) ≠ _
  rw [complete_vector]
  decide

theorem recaptured_condition_refused : observation (run compiled.code {machine true with stack := [w[77],w[88]]}) ≠
    observation (run (compiled.code ++ recapture.code) {machine true with stack := [w[77],w[88]]}) := by
  rw [target_tail,recapture_vector]
  change some (cells.map (observed true [w[77],w[88]]).mem,_) ≠ _
  rw [complete_vector]
  decide

theorem corrupted_tail_refused : (observed true [w[77],w[88]]).stack ≠ [w[78],w[88]] := by decide +kernel

end Solidity.Backend.Passes.EffectfulConditionalAssignment.Controls
