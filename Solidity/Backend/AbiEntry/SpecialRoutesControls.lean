import Solidity.Backend.AbiEntry.SpecialRoutes
import Solidity.Source.SemanticsExamples

/-! General selected-route controls and actual Source special metadata. Labels
are continuation observations, never supplied special body executions. -/
namespace Solidity.Backend.AbiEntry.SpecialRoutesControls
open Solidity.Evm
open Interface (SpecialRow specialOutcome specialResult specialRowOutcome sourceSpecial)
private def C : Contract := {vars := []}
private def machine (size value : Fin W) : Machine :=
  {Machine.init with
    callvalue := value
    mem := fun address => if address=8 then .val size else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def written (size value label : Fin W) : Machine :=
  {machine size value with mem := upd (machine size value).mem 8 (.val label)}
private def recv : SpecialRow := (wmod 11,true)
private def fb : SpecialRow := (wmod 22,false)
private def compiled (receive fallback : Option SpecialRow) := SpecialRoutes.compiled C 7 receive fallback
private theorem actual (receive fallback : Option SpecialRow) (size value : Fin W) :
    run (compiled receive fallback).code (machine size value)=specialOutcome 7 receive fallback size (machine size value) :=
  SpecialRoutes.executed C 7 receive fallback (compiled receive fallback) (SpecialRoutes.selected C 7 receive fallback)
    (machine size value) size rfl

theorem empty_receive (value : Fin W) :
    run (compiled (some recv) (some fb)).code (machine (wmod 0) value)=
      .ok (written (wmod 0) value recv.1) 0 := by
  have reached := actual (some recv) (some fb) (wmod 0) value
  have empty : (wmod 0).val=0 := rfl
  simpa only [written,Bool.false_eq_true,specialOutcome,specialResult,ite_eq_left empty,Option.orElse_some,specialRowOutcome,recv,Bool.true_or,ite_true] using reached

theorem absent_receive_fallback_zero :
    run (compiled none (some fb)).code (machine (wmod 0) (wmod 0))=
      .ok (written (wmod 0) (wmod 0) fb.1) 0 := by
  have reached := actual none (some fb) (wmod 0) (wmod 0)
  exact reached

theorem nonempty_fallback_reject (size value : Fin W) (nonempty : size.val≠0) (nonzero : value.val≠0) :
    run (compiled (some recv) (some fb)).code (machine size value)=.revert := by
  have reached := actual (some recv) (some fb) size value
  have observed : (machine size value).callvalue.val≠0 := nonzero
  simpa only [written,Bool.false_eq_true,specialOutcome,specialResult,ite_eq_right nonempty,specialRowOutcome,fb,Bool.false_or,
    decide_eq_false observed,ite_false] using reached

theorem absent_receive_reject (value : Fin W) (nonzero : value.val≠0) :
    run (compiled none (some fb)).code (machine (wmod 0) value)=.revert := by
  have reached := actual none (some fb) (wmod 0) value
  have empty : (wmod 0).val=0 := rfl
  have observed : (machine (wmod 0) value).callvalue.val≠0 := nonzero
  simpa only [written,Bool.false_eq_true,specialOutcome,specialResult,ite_eq_left empty,Option.orElse_none,specialRowOutcome,fb,
    Bool.false_or,decide_eq_false observed,ite_false] using reached

theorem no_special (size value : Fin W) :
    run (compiled none none).code (machine size value)=.revert := by
  have reached := actual none none size value
  by_cases empty : size.val=0
  · simpa only [written,Bool.false_eq_true,specialOutcome,specialResult,ite_eq_left empty,Option.orElse_none,specialRowOutcome] using reached
  · simpa only [written,Bool.false_eq_true,specialOutcome,specialResult,ite_eq_right empty,specialRowOutcome] using reached

theorem payable_fallback (size value : Fin W) :
    run (compiled none (some (wmod 22,true))).code (machine size value)=
      .ok (written size value (wmod 22)) 0 := by
  have reached := actual none (some (wmod 22,true)) size value
  by_cases empty : size.val=0
  · simpa only [written,Bool.false_eq_true,specialOutcome,specialResult,ite_eq_left empty,Option.orElse_none,specialRowOutcome,Bool.true_or,ite_true] using reached
  · simpa only [written,Bool.false_eq_true,specialOutcome,specialResult,ite_eq_right empty,specialRowOutcome,Bool.true_or,ite_true] using reached

private def receiveDecl : Source.Decl :=
  {kind := .receive,name := "",scope := some "C",top := false,
    node := .receive true true .nil false none (.some (.block .nil))}
private def fallbackDecl (payable : Bool) : Source.Decl :=
  {kind := .fallback,name := "",scope := some "C",top := false,
    node := .fallback .fbNoParams true (if payable then some .payable else none) .nil false none (.some (.block .nil))}
private def E (receive payable : Bool) : Source.Env :=
  ⟨(if receive then [receiveDecl] else [])++[fallbackDecl payable]⟩
private def labels (declaration : Source.Decl) : Fin W := if declaration.kind==.receive then wmod 11 else wmod 22
private def frame (bytes : List UInt8) : Source.Fr := {Source.SemanticsExamples.F0 with cd := bytes}

theorem actual_source_rows (payable : Bool) :
    SpecialRoutes.receiveRow (E true payable) "C" labels=some recv ∧
    SpecialRoutes.fallbackRow (E true payable) "C" labels=some (wmod 22,payable) := by
  cases payable <;> decide

theorem source_absence_bytes (pipeline : Roadmap.Pipeline) (bytes : List UInt8) (fuel : Nat) :
    Source.dispatch (Source.SemanticsExamples.G0 pipeline) (frame bytes) (fuel+1) bytes=
      Source.EM.halt (.revert []) := by
  apply SpecialRoutes.source_absent
  · rfl
  · rfl
  · cases bytes <;> rfl

private def global (pipeline : Roadmap.Pipeline) : Source.Glob (E false false) :=
  ⟨{body _ := none,consts _ := none,inits _ := [],ctor _ := none,ctorLocals _ := [],baseArgs _ := [],contracts := []},
    pipeline,Source.SemanticsExamples.toyFixed,fun _ => wmod 0,fun _ _ => false,
    fun _ => .answer (.success []),wmod 0⟩

theorem source_rejection_bytes (pipeline : Roadmap.Pipeline) (fuel : Nat) (value : Fin W)
    (nonzero : value.val≠0) :
    Source.dispatch (global pipeline) {frame [1,2,3] with value := value} (fuel+1) [1,2,3]=
      Source.EM.halt (.revert []) := by
  exact SpecialRoutes.source_rejection (global pipeline) {frame [1,2,3] with value := value}
    fuel (fallbackDecl false) rfl rfl rfl nonzero rfl

theorem malformed_length_fault :
    run (compiled (some recv) (some fb)).code
      {machine (wmod 0) (wmod 0) with mem := fun _ => .slot (.root 0)}=.fault := by rfl

theorem protected_and_saved (size value label : Fin W) :
    (written size value label).mem 7=.val (wmod 71) ∧
    (written size value label).mem 9=.val (wmod 71) ∧
    (written size value label).stack=[.val (wmod 258),.val (wmod 513)] ∧
    (written size value label).callvalue=value := ⟨rfl,rfl,rfl,rfl⟩
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutesControls.empty_receive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_receive
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutesControls.absent_receive_fallback_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_receive_fallback_zero
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutesControls.nonempty_fallback_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_fallback_reject
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutesControls.absent_receive_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_receive_reject
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutesControls.no_special' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_special
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutesControls.payable_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms payable_fallback
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutesControls.actual_source_rows' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms actual_source_rows
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutesControls.source_absence_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_absence_bytes
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutesControls.source_rejection_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_rejection_bytes
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutesControls.malformed_length_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_length_fault
/-- info: 'Solidity.Backend.AbiEntry.SpecialRoutesControls.protected_and_saved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.SpecialRoutesControls
