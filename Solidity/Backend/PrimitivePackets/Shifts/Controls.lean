import Solidity.Backend.PrimitivePackets.Shifts.General
import Solidity.Source.SemanticsExamples

/-! Concrete native boundary executions with a nonempty saved stack, nonzero
protected storage/balances/context/memory, and populated Source machines.
These controls supplement General.transport; they are not whole-call, ABI
or physical-bytecode adequacy claims. -/
namespace Solidity.Backend.PrimitivePackets.Shifts.Controls
open Solidity Solidity.Evm Solidity.Evm.Memory
open Solidity.Source.SemanticsExamples (E0 G0 F0 word addr)

def machine (x k : Nat) : Machine :=
  {Machine.init (fun a => if a.val=7 then 93 else 12) (wmod 2) with
    stack := [w[17],w[99]]
    store := WordStore.ofFn (fun _ => 41)
    mem := fun a => if a=0 then .val (wmod k) else if a=1 then .val (wmod x) else w[201]
    bal₀ := fun _ => 100
    caller := wmod 1
    callvalue := wmod 7
    timestamp := wmod 12345
    accepts := fun _ _ => false}

def targetRun (C : Contract) (left : Bool) (x k : Nat) :=
  run (selected (C:=C) 0 left).code (machine x k)

theorem target_zero_count (C : Contract) (left : Bool) :
    targetRun C left 1 0 = .ok ((machine 1 0).push w[1]) 0 := by
  first | rfl | (cases left <;> rfl)

theorem target_left_255 (C : Contract) :
    targetRun C true 1 255 = .ok ((machine 1 255).push (.val (wmod (2^255)))) 0 := by
  first | rfl | decide

theorem target_right_255 (C : Contract) :
    targetRun C false (2^255) 255 = .ok ((machine (2^255) 255).push w[1]) 0 := by
  first | rfl | decide

theorem target_saturation_boundaries (C : Contract) (left : Bool) :
    targetRun C left 1 256 = .ok ((machine 1 256).push w[0]) 0 ∧
    targetRun C left 1 257 = .ok ((machine 1 257).push w[0]) 0 ∧
    targetRun C left 1 (2^256-1) = .ok ((machine 1 (2^256-1)).push w[0]) 0 := by
  first | rfl | (cases left <;> exact ⟨rfl,rfl,rfl⟩)

def populated (bytes : Roadmap.Bytes) : Source.St E0 :=
  {Source.St.init E0 with
    ex := (Source.St.init E0).ex.run [.account (addr 1)
      (fun a => {a with balance:=word 93,nonce:=3,code:=some 0})]
    heap := (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes bytes⟩).1
    events := [.call (addr 2) (word 7) bytes false]
    logs := [(addr 1,bytes),(addr 2,[0,255,128])]
    fnLocals := ⟨[.bool],.cons (.bool true) .nil⟩}

def sourceRun (pipeline : Roadmap.Pipeline) (static left : Bool) (bytes : Roadmap.Bytes)
    (k : Int) (hk : Range k) :=
  (Source.evalE (G0 pipeline) {F0 with static:=static,checked:=false} 3 (expression left)).run
    (locals 1 (by decide) k hk,populated bytes)

theorem source_zero_count (pipeline : Roadmap.Pipeline) (static left : Bool)
    (bytes : Roadmap.Bytes) :
    sourceRun pipeline static left bytes 0 (by decide) =
      (.ok (.val (.int 1 (by decide))),
        (locals 1 (by decide) 0 (by decide),populated bytes)) := by
  first
  | rfl
  | unfold sourceRun
    rw [source_execution (G0 pipeline) {F0 with static:=static} 0 left
      1 (by decide) 0 (by decide) (populated bytes)]
    cases left <;> rfl

theorem source_left_255 (pipeline : Roadmap.Pipeline) (static : Bool)
    (bytes : Roadmap.Bytes) :
    sourceRun pipeline static true bytes 255 (by decide) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 ((2^255 : Nat) : Int))),
        (locals 1 (by decide) 255 (by decide),populated bytes)) := by
  first
  | rfl
  | unfold sourceRun
    rw [source_execution (G0 pipeline) {F0 with static:=static} 0 true
      1 (by decide) 255 (by decide) (populated bytes)]
    change ((Except.ok (Source.RVal.val (Source.intWrap Source.IntTy.u256 (1 * (2 : Int)^255))) :
        Except Source.Halt (Source.RVal E0.layout (.int Source.IntTy.u256))),
      (locals 1 (by decide) 255 (by decide),populated bytes)) = _
    have power : (2 : Int)^255 = ((2^255 : Nat) : Int) := by
      simpa only using (Int.natCast_pow 2 255).symm
    rw [power, Int.one_mul]

theorem source_saturation_boundaries (pipeline : Roadmap.Pipeline) (static left : Bool)
    (bytes : Roadmap.Bytes) :
    sourceRun pipeline static left bytes 256 (by decide) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 0)),
        (locals 1 (by decide) 256 (by decide),populated bytes)) ∧
    sourceRun pipeline static left bytes 257 (by decide) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 0)),
        (locals 1 (by decide) 257 (by decide),populated bytes)) ∧
    sourceRun pipeline static left bytes (((2^256-1 : Nat) : Int)) (by decide) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 0)),
        (locals 1 (by decide) (((2^256-1 : Nat) : Int)) (by decide),populated bytes)) := by
  first
  | rfl
  | exact ⟨source_saturated (G0 pipeline) {F0 with static:=static} 0 left
        1 (by decide) 256 (by decide) (populated bytes) (by decide),
      source_saturated (G0 pipeline) {F0 with static:=static} 0 left
        1 (by decide) 257 (by decide) (populated bytes) (by decide),
      source_saturated (G0 pipeline) {F0 with static:=static} 0 left
        1 (by decide) (((2^256-1 : Nat) : Int)) (by decide) (populated bytes) (by decide)⟩

theorem zero_horizon (pipeline : Roadmap.Pipeline) (static left : Bool)
    (bytes : Roadmap.Bytes) :
    (Source.evalE (G0 pipeline) {F0 with static:=static,checked:=false} 0 (expression left)).run
      (locals 1 (by decide) 256 (by decide),populated bytes) =
      (.error .timeout,(locals 1 (by decide) 256 (by decide),populated bytes)) := by rfl

theorem wrong_masked_count (C : Contract) :
    targetRun C true 1 256 ≠ .ok ((machine 1 256).push w[1]) 0 := by
  rw [(target_saturation_boundaries C true).1]
  intro wrong
  have stack := congrArg (fun out => match out with
    | .ok m _ => m.stack
    | _ => []) wrong
  change [w[0],w[17],w[99]] = [w[1],w[17],w[99]] at stack
  cases stack

def Client : Contract := {vars:=[]}

/-- An inhabited client of the arbitrary-context theorem, for arbitrary input
words and bytes, BOTH real pipelines and either static mode. No execution or
post-state equation is supplied to the transport. -/
theorem client (pipeline : Roadmap.Pipeline) (static left : Bool) (bytes : Roadmap.Bytes)
    (x k : Fin W) :
    (Source.evalE (G0 pipeline) {F0 with static:=static,checked:=false} 3
      (General.expression left (.here : Source.Idx SourceCtx (.int Source.IntTy.u256))
        (.there .here))).run
      (locals (x.val : Int) (word_range x) (k.val : Int) (word_range k),populated bytes) =
      (.ok (.val (.int ((resultWord left x k).val : Int) (word_range (resultWord left x k)))),
        (locals (x.val : Int) (word_range x) (k.val : Int) (word_range k),populated bytes)) ∧
    run (General.selected (C:=Client) 0 left (.here : Idx TargetCtx (.val .uint))
      (.there .here)).code (machine x.val k.val) =
      .ok ((machine x.val k.val).push (.val (resultWord left x k))) 0 := by
  have value : (machine x.val k.val).mem (cellOf 0 (.here : Idx TargetCtx (.val .uint))) = .val x := by
    change Word.val (wmod x.val) = Word.val x
    rw [wmod_of_lt x.isLt]
  have amount : (machine x.val k.val).mem (cellOf 0 (.there .here : Idx TargetCtx (.val .uint))) = .val k := by
    change Word.val (wmod k.val) = Word.val k
    rw [wmod_of_lt k.isLt]
  have actual := General.transport (C:=Client) (G0 pipeline) {F0 with static:=static} 0 0 left
    (.here : Source.Idx SourceCtx (.int Source.IntTy.u256)) (.there .here)
    (.here : Idx TargetCtx (.val .uint)) (.there .here)
    (locals (x.val : Int) (word_range x) (k.val : Int) (word_range k))
    (populated bytes) x k (machine x.val k.val) rfl rfl value amount
  exact ⟨actual.2.1,actual.2.2.1⟩

theorem source_right_255 (pipeline : Roadmap.Pipeline) (static : Bool)
    (bytes : Roadmap.Bytes) :
    sourceRun pipeline static false bytes 255 (by decide) =
      (.ok (.val (.int 0 (by decide))),
        (locals 1 (by decide) 255 (by decide),populated bytes)) := by
  unfold sourceRun
  rw [source_execution (G0 pipeline) {F0 with static:=static} 0 false
    1 (by decide) 255 (by decide) (populated bytes)]
  rfl

theorem argument_timeout (pipeline : Roadmap.Pipeline) (static left : Bool)
    (bytes : Roadmap.Bytes) :
    (Source.evalE (G0 pipeline) {F0 with static:=static,checked:=false} 1 (expression left)).run
      (locals 1 (by decide) 256 (by decide),populated bytes) =
      (.error .timeout,(locals 1 (by decide) 256 (by decide),populated bytes)) := by rfl

theorem wrong_order (C : Contract) :
    targetRun C true 255 1 = .ok ((machine 255 1).push w[510]) 0 := by rfl

theorem wrong_order_rejected (C : Contract) :
    targetRun C true 255 1 ≠ .ok ((machine 255 1).push (.val (wmod (2^255)))) 0 := by
  rw [wrong_order]
  intro wrong
  have stack := congrArg (fun out => match out with
    | .ok m _ => m.stack
    | _ => []) wrong
  change [w[510],w[17],w[99]] = [.val (wmod (2^255)),w[17],w[99]] at stack
  have different : (w[510] : Word) ≠ .val (wmod (2^255)) := by decide +kernel
  exact different (List.cons.inj stack).1

end Solidity.Backend.PrimitivePackets.Shifts.Controls

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.machine' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.machine

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.targetRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.targetRun

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.target_zero_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.target_zero_count

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.target_left_255' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.target_left_255

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.target_right_255' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.target_right_255

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.target_saturation_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.target_saturation_boundaries

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.populated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.populated

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.sourceRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.sourceRun

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.source_zero_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.source_zero_count

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.source_left_255' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.source_left_255

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.source_saturation_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.source_saturation_boundaries

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.zero_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.zero_horizon

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.wrong_masked_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.wrong_masked_count

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.Client' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.Client

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.client

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.source_right_255' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.source_right_255

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.argument_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.argument_timeout

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.wrong_order

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Controls.wrong_order_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Controls.wrong_order_rejected
