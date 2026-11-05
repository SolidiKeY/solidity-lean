import Solidity.Backend.AbiEntry.DispatchRefusal
import Solidity.Source.SemanticsExamples

/-! Actual routing failures plus a later short-head failure deliberately
outside the classification. The fixed hash is synthetic, not Keccak evidence. -/
namespace Solidity.Backend.AbiEntry.DispatchRefusalControls
open Solidity.Evm
open Interface (dispatchRefuses rawSelectorWord)
private def fn : Source.Syn (.part false) :=
  .function (.ident "f") (.cons (.param (.elem .bool) none (some "b")) .nil)
    (some .pub) none .nil false none .nil (.some (.block .nil))
private def publicVar : Source.Syn (.part false) :=
  .stateVar (.elem (.int false 256 (by decide))) (some .pub) none none false "x" .none
private def fallback : Source.Syn (.part false) :=
  .fallback .fbNoParams true none .nil false none (.some (.block .nil))
private def parts : List (Source.Syn (.part false)) → Source.Syn (.list (.part false))
  | [] => .nil
  | entry::rest => .cons entry (parts rest)
private def unit (ordinary getter special : Bool) : Source.Syn .unit :=
  .unit (.cons (.contract true "C" .none .nil (parts ((if ordinary then [fn] else [])++
    (if getter then [publicVar] else [])++(if special then [fallback] else [])))) .nil)
private def E (ordinary getter special : Bool) : Source.Env := (unit ordinary getter special).env
private def body (ordinary getter special : Bool) : Source.RBody (E ordinary getter special) :=
  {ps := [.bool],rs := [],inModifier := false,locals := [.bool],out := [.bool],items := .nil}
private def fixed : Roadmap.Fixed :=
  {Source.SemanticsExamples.toyFixed with evm := {Source.SemanticsExamples.toyFixed.evm with
    keccak := fun _ => 0xdeadbe00*2^224,keccak_lt := fun _ => by decide}}
private def global (ordinary getter special : Bool) (pipeline : Roadmap.Pipeline) : Source.Glob (E ordinary getter special) :=
  ⟨{body declaration := if declaration.kind==.function then some (body ordinary getter special) else none
    consts _ := none,inits _ := [],ctor _ := none,ctorLocals _ := [],baseArgs _ := [],contracts := ["C"]},
    pipeline,fixed,fun _ => wmod 0,fun _ _ => false,fun _ => .answer (.success []),wmod 0⟩
private def bytes : List UInt8 := [0xde,0xad,0xbe,0]
private def frame (value : Fin W) : Source.Fr := {Source.SemanticsExamples.F0 with cd := bytes,value := value}
private def labels (declaration : Source.Decl) : Fin W :=
  if declaration.name="f" then wmod 33 else if declaration.name="x" then wmod 11 else wmod 99
private def C : Contract := {vars := []}
private def machine (value : Fin W) : Machine :=
  {Machine.init with
    callvalue := value
    mem := fun address => if address=7 then .val (rawSelectorWord (frame value))
      else if address=8 then .val (wmod bytes.length) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def compiled (ordinary getter special : Bool) (pipeline : Roadmap.Pipeline) :=
  GetterRoutes.compiled (global ordinary getter special pipeline) "C" labels C 7

private theorem classified (ordinary getter special : Bool) (pipeline : Roadmap.Pipeline) (value : Fin W) :
    (run (compiled ordinary getter special pipeline).code (machine value)=.revert ↔
      dispatchRefuses (global ordinary getter special pipeline) (frame value)=true) :=
  DispatchRefusal.compiled (global ordinary getter special pipeline) (frame value) labels C 7
    (compiled ordinary getter special pipeline) (GetterRoutes.selected (global ordinary getter special pipeline) "C" labels C 7)
    (machine value) (wmod bytes.length) rfl rfl (by change (wmod bytes.length).val=bytes.length;decide) rfl

private theorem fixture (ordinary getter special : Bool) (pipeline : Roadmap.Pipeline) (value : Fin W) :
    dispatchRefuses (global ordinary getter special pipeline) (frame value)=
      if ordinary || getter || special then Bool.not (decide (value.val=0)) else true := by
  have chosen : Interface.sourceDispatchRow (global ordinary getter special pipeline) (frame value) labels=
      if ordinary then some (wmod 33,false) else if getter then some (wmod 11,false)
        else if special then some (wmod 99,false) else none := by
    change Interface.sourceDispatchRow (global ordinary getter special pipeline) (frame (wmod 0)) labels=_
    cases ordinary <;> cases getter <;> cases special <;> cases pipeline <;> decide
  rw [DispatchRefusal.row_classification _ _ labels,chosen]
  cases ordinary <;> cases getter <;> cases special <;> rfl

theorem absent_even_zero (pipeline : Roadmap.Pipeline) :
    run (compiled false false false pipeline).code (machine (wmod 0))=.revert := by
  apply (classified false false false pipeline (wmod 0)).mpr
  cases pipeline <;> decide

theorem present_zero_not_routing_refusal (ordinary getter special : Bool) (pipeline : Roadmap.Pipeline)
    (present : (ordinary || getter || special)=true) :
    dispatchRefuses (global ordinary getter special pipeline) (frame (wmod 0))=false := by
  rw [fixture,if_pos present]
  rfl

theorem nonzero_runtime (ordinary getter special : Bool) (pipeline : Roadmap.Pipeline) (value : Fin W)
    (nonzero : value.val≠0) : run (compiled ordinary getter special pipeline).code (machine value)=.revert := by
  apply (classified ordinary getter special pipeline value).mpr
  rw [fixture]
  by_cases present : (ordinary || getter || special)=true
  · simp only [if_pos present,decide_eq_false nonzero,Bool.not_false]
  · simp only [if_neg present]

theorem nonzero_source_bytes (ordinary getter special : Bool) (pipeline : Roadmap.Pipeline)
    (value : Fin W) (nonzero : value.val≠0) (fuel : Nat) :
    Source.dispatch (global ordinary getter special pipeline) (frame value) (fuel+1) bytes=
      Source.EM.halt (.revert []) := by
  apply DispatchRefusal.source
  exact (classified ordinary getter special pipeline value).mp
    (nonzero_runtime ordinary getter special pipeline value nonzero)
theorem zero_runtime_not_revert (ordinary getter special : Bool) (pipeline : Roadmap.Pipeline)
    (present : (ordinary || getter || special)=true) :
    run (compiled ordinary getter special pipeline).code (machine (wmod 0))≠.revert := by
  intro rejected
  have contradiction := (classified ordinary getter special pipeline (wmod 0)).mp rejected
  rw [present_zero_not_routing_refusal ordinary getter special pipeline present] at contradiction
  cases contradiction

/-- A later actual Source head failure is deliberately outside routing refusal. -/
theorem zero_head_failure (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    dispatchRefuses (global true false false pipeline) (frame (wmod 0))=false ∧
    Source.dispatch (global true false false pipeline) (frame (wmod 0)) (fuel+1) bytes=
      Source.EM.halt (.revert []) := by
  constructor
  · exact present_zero_not_routing_refusal true false false pipeline rfl
  · have signatures : ((global true false false pipeline).pickFn (frame (wmod 0)) bytes).map
        (fun declaration => declaration.fnSig (E true false false))=some (some ([.bool],[])) := by
      cases pipeline <;> decide
    cases picked : (global true false false pipeline).pickFn (frame (wmod 0)) bytes with
    | none => rw [picked] at signatures; cases signatures
    | some declaration =>
      rw [picked] at signatures
      have signature := Option.some.inj signatures
      have nonempty : bytes.isEmpty=false := rfl
      have noValue : decide ((frame (wmod 0)).value.val≠0)=false := by decide
      have short : bytes.length<4+32*([Source.STy.bool].length) := by decide
      simp only [Source.dispatch,picked,signature,nonempty,noValue,Bool.false_and,Bool.false_eq_true,if_false,if_pos short]
      rfl

/-- info: 'Solidity.Backend.AbiEntry.DispatchRefusalControls.absent_even_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_even_zero
/-- info: 'Solidity.Backend.AbiEntry.DispatchRefusalControls.present_zero_not_routing_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms present_zero_not_routing_refusal
/-- info: 'Solidity.Backend.AbiEntry.DispatchRefusalControls.nonzero_runtime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonzero_runtime
/-- info: 'Solidity.Backend.AbiEntry.DispatchRefusalControls.nonzero_source_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonzero_source_bytes
/-- info: 'Solidity.Backend.AbiEntry.DispatchRefusalControls.zero_runtime_not_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_runtime_not_revert
/-- info: 'Solidity.Backend.AbiEntry.DispatchRefusalControls.zero_head_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_head_failure
end Solidity.Backend.AbiEntry.DispatchRefusalControls
