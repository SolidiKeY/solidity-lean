import Solidity.Backend.AbiEntry.GetterRoutes
import Solidity.Source.SemanticsExamples

/-! Typed Source public variables and a colliding payable function/fallback.
These model-hash controls certify continuation order, not storage/body output. -/
namespace Solidity.Backend.AbiEntry.GetterRoutesControls
open Solidity.Evm
open Interface (sourceDispatchRow rawSelectorWord specialRowOutcome)
private def publicVar (name : String) : Source.Syn (.part false) :=
  .stateVar (.elem (.int false 256 (by decide))) (some .pub) none none false name .none
private def fn : Source.Syn (.part false) :=
  .function (.ident "f") .nil (some .pub) (some .payable) .nil false none .nil (.some (.block .nil))
private def fallback : Source.Syn (.part false) :=
  .fallback .fbNoParams true (some .payable) .nil false none (.some (.block .nil))
private def parts : List (Source.Syn (.part false)) → Source.Syn (.list (.part false))
  | [] => .nil
  | entry::rest => .cons entry (parts rest)
private def unit (ordinary getters : Bool) : Source.Syn .unit :=
  .unit (.cons (.contract true "C" .none .nil
    (parts ((if ordinary then [fn] else [])++(if getters then [publicVar "x",publicVar "y"] else [])++[fallback]))) .nil)
private def E (ordinary getters : Bool) : Source.Env := (unit ordinary getters).env
private def body (ordinary getters : Bool) : Source.RBody (E ordinary getters) :=
  {ps := [],rs := [],inModifier := false,locals := [],out := [],items := .nil}
private def fixed : Roadmap.Fixed :=
  {Source.SemanticsExamples.toyFixed with evm := {Source.SemanticsExamples.toyFixed.evm with
    keccak := fun _ => 0xdeadbe00*2^224,keccak_lt := fun _ => by decide}}
private def global (ordinary getters : Bool) (pipeline : Roadmap.Pipeline) : Source.Glob (E ordinary getters) :=
  ⟨{body declaration := if declaration.kind==.function then some (body ordinary getters) else none
    consts _ := none,inits _ := [],ctor _ := none,ctorLocals _ := [],baseArgs _ := [],contracts := ["C"]},
    pipeline,fixed,fun _ => wmod 0,fun _ _ => false,fun _ => .answer (.success []),wmod 0⟩
private def labels (declaration : Source.Decl) : Fin W :=
  if declaration.name="f" then wmod 33 else if declaration.name="x" then wmod 11
    else if declaration.name="y" then wmod 22 else wmod 99
private def C : Contract := {vars := []}
private def fullBytes : List UInt8 := [0xde,0xad,0xbe,0]
private def shortBytes : List UInt8 := [0xde,0xad,0xbe]
private def missBytes : List UInt8 := [0x12,0x34,0x56,0x78]
private def frame (bytes : List UInt8) (value : Fin W) : Source.Fr :=
  {Source.SemanticsExamples.F0 with cd := bytes,value := value}
private def machine (bytes : List UInt8) (value : Fin W) : Machine :=
  {Machine.init with
    callvalue := value
    mem := fun address => if address=7 then .val (rawSelectorWord (frame bytes value))
      else if address=8 then .val (wmod bytes.length) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def written (bytes : List UInt8) (value label : Fin W) : Machine :=
  {machine bytes value with mem := upd (machine bytes value).mem 8 (.val label)}
private def compiled (ordinary getters : Bool) (pipeline : Roadmap.Pipeline) :=
  GetterRoutes.compiled (global ordinary getters pipeline) "C" labels C 7

private theorem reached (ordinary getters : Bool) (pipeline : Roadmap.Pipeline) (bytes : List UInt8)
    (value : Fin W) (fits : bytes.length<W) :
    run (compiled ordinary getters pipeline).code (machine bytes value)=
      specialRowOutcome 7 (sourceDispatchRow (global ordinary getters pipeline) (frame bytes value) labels)
        (machine bytes value) := by
  have exactLength : (wmod bytes.length).val=bytes.length := Nat.mod_eq_of_lt fits
  exact GetterRoutes.executed (global ordinary getters pipeline) (frame bytes value) labels C 7
    (compiled ordinary getters pipeline) (GetterRoutes.selected (global ordinary getters pipeline) "C" labels C 7)
    (machine bytes value) (wmod bytes.length) rfl rfl exactLength

private theorem chosen (ordinary getters : Bool) (pipeline : Roadmap.Pipeline) (value : Fin W) :
    sourceDispatchRow (global ordinary getters pipeline) (frame fullBytes value) labels=
      if ordinary then some (wmod 33,true) else if getters then some (wmod 11,false) else some (wmod 99,true) := by
  change sourceDispatchRow (global ordinary getters pipeline) (frame fullBytes (wmod 0)) labels=_
  cases ordinary <;> cases getters <;> cases pipeline <;> decide

theorem getter_count (ordinary : Bool) (pipeline : Roadmap.Pipeline) :
    ((E ordinary true).getters "C").length=2 ∧
    (GetterRoutes.table (global ordinary true pipeline) "C" labels).length=(if ordinary then 3 else 2) := by
  cases ordinary <;> cases pipeline <;> decide

theorem ordinary_priority (pipeline : Roadmap.Pipeline) (value : Fin W) :
    run (compiled true true pipeline).code (machine fullBytes value)=.ok (written fullBytes value (wmod 33)) 0 := by
  have actual := reached true true pipeline fullBytes value (by decide)
  simpa only [written,Bool.false_eq_true,ite_false,chosen,specialRowOutcome,Bool.true_or,ite_true] using actual

theorem getter_zero (pipeline : Roadmap.Pipeline) :
    run (compiled false true pipeline).code (machine fullBytes (wmod 0))=.ok (written fullBytes (wmod 0) (wmod 11)) 0 := by
  have actual := reached false true pipeline fullBytes (wmod 0) (by decide)
  have observed : (machine fullBytes (wmod 0)).callvalue.val=0 := rfl
  simpa only [written,Bool.false_eq_true,ite_false,chosen,specialRowOutcome,Bool.false_or,decide_eq_true observed,ite_true] using actual

theorem getter_nonzero (pipeline : Roadmap.Pipeline) (value : Fin W) (nonzero : value.val≠0) :
    run (compiled false true pipeline).code (machine fullBytes value)=.revert := by
  have actual := reached false true pipeline fullBytes value (by decide)
  have observed : (machine fullBytes value).callvalue.val≠0 := nonzero
  simpa only [written,Bool.false_eq_true,ite_false,chosen,specialRowOutcome,Bool.false_or,decide_eq_false observed,ite_true,ite_false] using actual

private theorem fallback_selected (ordinary getters : Bool) (pipeline : Roadmap.Pipeline)
    (bytes : List UInt8) (notSelector : bytes=shortBytes ∨ bytes=missBytes) (value : Fin W) :
    sourceDispatchRow (global ordinary getters pipeline) (frame bytes value) labels=some (wmod 99,true) := by
  change sourceDispatchRow (global ordinary getters pipeline) (frame bytes (wmod 0)) labels=_
  rcases notSelector with rfl | rfl <;> cases ordinary <;> cases getters <;> cases pipeline <;> decide

theorem padded_short_fallback (ordinary getters : Bool) (pipeline : Roadmap.Pipeline) (value : Fin W) :
    run (compiled ordinary getters pipeline).code (machine shortBytes value)=.ok (written shortBytes value (wmod 99)) 0 := by
  have actual := reached ordinary getters pipeline shortBytes value (by decide)
  simpa only [written,Bool.false_eq_true,ite_false,fallback_selected ordinary getters pipeline shortBytes (Or.inl rfl),specialRowOutcome,
    Bool.true_or,ite_true] using actual

theorem full_miss_fallback (ordinary getters : Bool) (pipeline : Roadmap.Pipeline) (value : Fin W) :
    run (compiled ordinary getters pipeline).code (machine missBytes value)=.ok (written missBytes value (wmod 99)) 0 := by
  have actual := reached ordinary getters pipeline missBytes value (by decide)
  simpa only [written,Bool.false_eq_true,ite_false,fallback_selected ordinary getters pipeline missBytes (Or.inr rfl),specialRowOutcome,
    Bool.true_or,ite_true] using actual

theorem source_revert_bytes (pipeline : Roadmap.Pipeline) (fuel : Nat) (value : Fin W)
    (nonzero : value.val≠0) :
    Source.dispatch (global false true pipeline) (frame fullBytes value) (fuel+1) fullBytes=
      Source.EM.halt (.revert []) := by
  have existsGetter : ((global false true pipeline).pickGetter (frame fullBytes value) fullBytes).isSome=true := by
    change ((global false true pipeline).pickGetter (frame fullBytes (wmod 0)) fullBytes).isSome=true
    cases pipeline <;> decide
  cases getter : (global false true pipeline).pickGetter (frame fullBytes value) fullBytes with
  | none => rw [getter] at existsGetter; cases existsGetter
  | some entry =>
    exact GetterRoutes.source_getter_rejection (global false true pipeline) (frame fullBytes value)
      fuel entry rfl getter nonzero

theorem getter_no_retry (pipeline : Roadmap.Pipeline) (value : Fin W) (nonzero : value.val≠0) :
    run (compiled false true pipeline).code (machine fullBytes value)≠.ok (written fullBytes value (wmod 99)) 0 := by
  rw [getter_nonzero pipeline value nonzero]
  intro impossible
  cases impossible

theorem protected_and_saved (bytes : List UInt8) (value label : Fin W) :
    (written bytes value label).mem 7=.val (rawSelectorWord (frame bytes value)) ∧
    (written bytes value label).mem 9=.val (wmod 71) ∧
    (written bytes value label).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (written bytes value label).callvalue=value := ⟨rfl,rfl,rfl,rfl⟩
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutesControls.getter_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms getter_count
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutesControls.ordinary_priority' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ordinary_priority
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutesControls.getter_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms getter_zero
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutesControls.getter_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms getter_nonzero
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutesControls.padded_short_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padded_short_fallback
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutesControls.full_miss_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_miss_fallback
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutesControls.source_revert_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_revert_bytes
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutesControls.getter_no_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms getter_no_retry
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutesControls.protected_and_saved' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.GetterRoutesControls
