import Solidity.Backend.AbiEntry.SourcePayable
import Solidity.Source.SemanticsExamples

/-! Synthetic colliding selectors and actual Source declaration mutability,
not a Keccak/deployment or body-compilation test. -/
namespace Solidity.Backend.AbiEntry.SourcePayableControls
open Solidity.Evm
open Interface (RouteCtx rawSelectorWord sourcePayableResult sourcePayableOutcome)
private def fn (payable : Bool) (name : String) : Source.Syn (.part false) :=
  .function (.ident name) .nil (some .pub) (if payable || name="g" then some .payable else none) .nil (decide (name="skip")) none .nil
    (if name="skip" then .none else .some (.block .nil))
private def unit (payable : Bool) : Source.Syn .unit :=
  .unit (.cons (.contract true "C" .none .nil (.cons (fn payable "skip") (.cons (fn payable "f") (.cons (fn payable "g") .nil)))) .nil)
private def E (payable : Bool) : Source.Env := (unit payable).env
private def body (payable : Bool) : Source.RBody (E payable) :=
  {ps := [],rs := [],inModifier := false,locals := [],out := [],items := .nil}
private def fixed : Roadmap.Fixed :=
  {Source.SemanticsExamples.toyFixed with
    evm := {Source.SemanticsExamples.toyFixed.evm with
      keccak := fun _ => 0xdeadbe00*2^224
      keccak_lt := fun _ => by decide}}
private def global (payable : Bool) (pipeline : Roadmap.Pipeline) : Source.Glob (E payable) :=
  ⟨{body declaration := if declaration.kind == .function && declaration.name != "skip" then some (body payable) else none
    consts _ := none,inits _ := [],ctor _ := none,ctorLocals _ := [],baseArgs _ := [],contracts := ["C"]},
    pipeline,fixed,fun _ => ⟨0,by decide⟩,fun _ _ => false,fun _ => .answer (.success []),⟨0,by decide⟩⟩
private def labels (declaration : Source.Decl) : Fin W :=
  if declaration.name="f" then wmod 11 else if declaration.name="g" then wmod 22 else wmod 77
private def fallback : Fin W := wmod 99
private def C : Contract := {vars := []}
private def fullBytes : List UInt8 := [0xde,0xad,0xbe,0,0xaa,0xbb]
private def missBytes : List UInt8 := [0x12,0x34,0x56,0x78]
private def frame (bytes : List UInt8) (value : Roadmap.Word) : Source.Fr := {Source.SemanticsExamples.F0 with cd := bytes,value := value}
private def machine (bytes : List UInt8) (value : Roadmap.Word) : Machine :=
  {Machine.init with
    callvalue := value
    mem := fun address => if address=7 then .val (rawSelectorWord (frame bytes value)) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def written (bytes : List UInt8) (value : Roadmap.Word) (label : Fin W) : Machine :=
  {machine bytes value with mem := upd (machine bytes value).mem 8 (.val label)}
private def compiled (payable : Bool) (pipeline : Roadmap.Pipeline) :=
  PayableRoutes.compiled C 7 (SourcePayable.table (global payable pipeline) "C" labels) fallback

theorem source_table (payable : Bool) (pipeline : Roadmap.Pipeline) :
    (SourcePayable.table (global payable pipeline) "C" labels).length=2 ∧
    sourcePayableResult (global payable pipeline) (frame fullBytes 0) labels fallback=(wmod 11,payable) := by
  cases payable <;> cases pipeline <;> decide

private theorem reached (payable : Bool) (pipeline : Roadmap.Pipeline) (bytes : List UInt8)
    (value : Roadmap.Word) (full : 4≤bytes.length) :
    run (compiled payable pipeline).code (machine bytes value)=
      sourcePayableOutcome (global payable pipeline) (frame bytes value) labels fallback 7 (machine bytes value) :=
  SourcePayable.executed (global payable pipeline) (frame bytes value) labels fallback full C 7
    (compiled payable pipeline) (SourcePayable.selected (global payable pipeline) "C" labels fallback C 7)
    (machine bytes value) rfl rfl

private theorem matched (payable : Bool) (pipeline : Roadmap.Pipeline) (value : Roadmap.Word) :
    sourcePayableResult (global payable pipeline) (frame fullBytes value) labels fallback=(wmod 11,payable) := by
  change sourcePayableResult (global payable pipeline) (frame fullBytes 0) labels fallback=(wmod 11,payable)
  exact (source_table payable pipeline).2

theorem zero_nonpayable (pipeline : Roadmap.Pipeline) :
    run (compiled false pipeline).code (machine fullBytes 0)=.ok (written fullBytes 0 (wmod 11)) 0 := by
  have actual := reached false pipeline fullBytes 0 (by decide)
  have observed : (frame fullBytes 0).value.val=0 := rfl
  simpa only [written,Bool.false_eq_true,sourcePayableOutcome,matched,Bool.false_or,decide_eq_true observed,ite_true] using actual

theorem payable_all_values (pipeline : Roadmap.Pipeline) (value : Roadmap.Word) :
    run (compiled true pipeline).code (machine fullBytes value)=.ok (written fullBytes value (wmod 11)) 0 := by
  have actual := reached true pipeline fullBytes value (by decide)
  simpa only [written,Bool.false_eq_true,sourcePayableOutcome,matched,Bool.true_or,ite_true] using actual

theorem rejected_collision (pipeline : Roadmap.Pipeline) (value : Roadmap.Word) (nonzero : value.val≠0) :
    run (compiled false pipeline).code (machine fullBytes value)=.revert := by
  have actual := reached false pipeline fullBytes value (by decide)
  have observed : (frame fullBytes value).value.val≠0 := nonzero
  simpa only [written,Bool.false_eq_true,sourcePayableOutcome,matched,Bool.false_or,decide_eq_false observed,ite_false] using actual

theorem no_collision_fallthrough (pipeline : Roadmap.Pipeline) (value : Roadmap.Word) (nonzero : value.val≠0) :
    run (compiled false pipeline).code (machine fullBytes value)≠.ok (written fullBytes value (wmod 22)) 0 := by
  rw [rejected_collision pipeline value nonzero]
  intro impossible
  cases impossible

private theorem missed (payable : Bool) (pipeline : Roadmap.Pipeline) (value : Roadmap.Word) :
    sourcePayableResult (global payable pipeline) (frame missBytes value) labels fallback=(fallback,true) := by
  change sourcePayableResult (global payable pipeline) (frame missBytes 0) labels fallback=(fallback,true)
  cases payable <;> cases pipeline <;> decide

theorem no_match (payable : Bool) (pipeline : Roadmap.Pipeline) (value : Roadmap.Word) :
    run (compiled payable pipeline).code (machine missBytes value)=.ok (written missBytes value fallback) 0 := by
  have actual := reached payable pipeline missBytes value (by decide)
  simpa only [written,Bool.false_eq_true,sourcePayableOutcome,missed,Bool.true_or,ite_true] using actual

theorem source_revert_bytes (pipeline : Roadmap.Pipeline) (fuel : Nat) (value : Roadmap.Word)
    (nonzero : value.val≠0) :
    Source.dispatch (global false pipeline) (frame fullBytes value) (fuel+1) fullBytes=
      Source.EM.halt (.revert []) := by
  have metadata : (((global false pipeline).pickFn (frame fullBytes value) fullBytes).map
      fun declaration => (declaration.fnSig (E false),declaration.fnMut == some .payable))=
        some (some ([],[]),false) := by
    change (((global false pipeline).pickFn (frame fullBytes 0) fullBytes).map
      fun declaration => (declaration.fnSig (E false),declaration.fnMut == some .payable))=
        some (some ([],[]),false)
    cases pipeline <;> decide
  cases picked : (global false pipeline).pickFn (frame fullBytes value) fullBytes with
  | none => rw [picked] at metadata; cases metadata
  | some declaration =>
    rw [picked] at metadata
    have fields := Option.some.inj metadata
    exact SourcePayable.source_rejection (global false pipeline) (frame fullBytes value) fuel
      declaration [] [] picked (congrArg Prod.fst fields) rfl nonzero (congrArg Prod.snd fields)

theorem protected_and_saved (bytes : List UInt8) (value : Roadmap.Word) (label : Fin W) :
    (written bytes value label).mem 7=.val (rawSelectorWord (frame bytes value)) ∧
    (written bytes value label).mem 9=.val (wmod 71) ∧
    (written bytes value label).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (written bytes value label).callvalue=value := ⟨rfl,rfl,rfl,rfl⟩
/-- info: 'Solidity.Backend.AbiEntry.SourcePayableControls.source_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_table
/-- info: 'Solidity.Backend.AbiEntry.SourcePayableControls.zero_nonpayable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_nonpayable
/-- info: 'Solidity.Backend.AbiEntry.SourcePayableControls.payable_all_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payable_all_values
/-- info: 'Solidity.Backend.AbiEntry.SourcePayableControls.rejected_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_collision
/-- info: 'Solidity.Backend.AbiEntry.SourcePayableControls.no_collision_fallthrough' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_collision_fallthrough
/-- info: 'Solidity.Backend.AbiEntry.SourcePayableControls.no_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_match
/-- info: 'Solidity.Backend.AbiEntry.SourcePayableControls.source_revert_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_revert_bytes
/-- info: 'Solidity.Backend.AbiEntry.SourcePayableControls.protected_and_saved' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.SourcePayableControls
