import Solidity.Backend.AbiEntry.DispatchRefusalInterface

/-! Exact refusal of the actual compiled continuation path, and the matching
Source empty-byte halt. Later argument/type/body failures are not classified. -/
namespace Solidity.Backend.AbiEntry.DispatchRefusal
open Solidity.Evm
open Interface (RouteCtx SpecialRow sourceDispatchRow specialRowOutcome dispatchRefuses)

private def rowRefuses (row : Option SpecialRow) (value : Nat) : Bool :=
  match row with
  | none => true
  | some pair => !(pair.2 || decide (value=0))

private theorem row_iff (base : Nat) (row : Option SpecialRow) (machine : Machine) (value : Nat)
    (aligned : machine.callvalue.val=value) :
    (specialRowOutcome base row machine=.revert ↔ rowRefuses row value=true) := by
  cases row with
  | none => exact ⟨fun _ => rfl,fun _ => rfl⟩
  | some pair =>
    cases allowed : pair.2 || decide (value=0) with
    | false =>
      simp only [specialRowOutcome,rowRefuses,aligned,allowed,Bool.false_eq_true,if_false,Bool.not_false]
    | true =>
      simp only [specialRowOutcome,rowRefuses,aligned,allowed,if_true,Bool.not_true]
      constructor <;> intro impossible <;> cases impossible

private theorem row_source {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) :
    rowRefuses (sourceDispatchRow global frame labels) frame.value.val=dispatchRefuses global frame := by
  unfold sourceDispatchRow dispatchRefuses
  cases ordinary : global.pickFn frame frame.cd with
  | some declaration => rfl
  | none =>
    cases getter : global.pickGetter frame frame.cd with
    | some entry => rfl
    | none =>
      cases special : Interface.sourceSpecial E frame <;> rfl

theorem row_classification {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) : dispatchRefuses global frame=
      match sourceDispatchRow global frame labels with
      | none => true
      | some pair => Bool.not (pair.2 || decide (frame.value.val=0)) :=
  (row_source global frame labels).symm

theorem compiled {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr) (labels : Source.Decl → Fin W)
    (C : Contract) (base : Nat)
    (result : Compiler.Compilation base (Frag.init RouteCtx)
      (EntryRoutes.route C (GetterRoutes.table global frame.contract labels)
        (SpecialRoutes.receiveRow E frame.contract labels) (SpecialRoutes.fallbackRow E frame.contract labels)))
    (found : Compiler.compile base (Frag.init RouteCtx)
      (EntryRoutes.route C (GetterRoutes.table global frame.contract labels)
        (SpecialRoutes.receiveRow E frame.contract labels) (SpecialRoutes.fallbackRow E frame.contract labels))=some result)
    (machine : Machine) (size : Fin W) (initial : machine.mem base=.val (Interface.rawSelectorWord frame))
    (length : machine.mem (base+1)=.val size) (bytes : size.val=frame.cd.length)
    (value : machine.callvalue.val=frame.value.val) :
    (run result.code machine=.revert ↔ dispatchRefuses global frame=true) := by
  rw [GetterRoutes.executed global frame labels C base result found machine size initial length bytes]
  rw [row_iff base _ machine frame.value.val value,row_source]

private theorem refused (payable : Bool) (value : Nat)
    (no : Bool.not (payable || decide (value=0))=true) : value≠0 ∧ payable=false := by
  cases payable with
  | true => simp only [Bool.true_or,Bool.not_true] at no; cases no
  | false =>
    constructor
    · intro zero
      simp only [zero,decide_true,Bool.false_or,Bool.not_true] at no
      cases no
    · rfl

theorem source {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr) (fuel : Nat)
    (no : dispatchRefuses global frame=true) :
    Source.dispatch global frame (fuel+1) frame.cd=Source.EM.halt (.revert []) := by
  cases ordinary : global.pickFn frame frame.cd with
  | some declaration =>
    have denied : Bool.not ((declaration.fnMut == some .payable) || decide (frame.value.val=0))=true := by
      simpa only [dispatchRefuses,ordinary] using no
    have properties := refused _ _ denied
    have full : 4≤frame.cd.length := by
      apply Nat.le_of_not_gt
      intro short
      have absent := ShortRoutes.source_short global frame short
      rw [ordinary] at absent
      cases absent
    have nonempty : frame.cd.isEmpty=false := by
      apply List.isEmpty_eq_false_iff.mpr
      intro empty
      rw [empty] at full
      exact (by decide : ¬4≤([] : List UInt8).length) full
    have eligible := List.find?_some (p := fun declaration =>
      (global.prog.body (global.dispatchFn frame.contract declaration)).isSome &&
        match declaration.fnSig E with
        | some (ps,_) => global.selector (Source.sigOf E.layout declaration.name ps)==frame.cd.take 4
        | none => false) ordinary
    have hit :=  (Bool.and_eq_true_iff.mp eligible).2
    cases signature : declaration.fnSig E with
    | none => rw [signature] at hit; cases hit
    | some pair =>
      exact SourcePayable.source_rejection global frame fuel declaration pair.1 pair.2 ordinary signature
        nonempty properties.1 properties.2
  | none =>
    cases getter : global.pickGetter frame frame.cd with
    | some entry =>
      have denied : Bool.not (false || decide (frame.value.val=0))=true := by
        simpa only [dispatchRefuses,ordinary,getter,Bool.false_or] using no
      exact GetterRoutes.source_getter_rejection global frame fuel entry ordinary getter (refused _ _ denied).1
    | none =>
      cases special : Interface.sourceSpecial E frame with
      | none => exact SpecialRoutes.source_absent global frame fuel ordinary getter special
      | some declaration =>
        have denied : Bool.not (declaration.specialPayable || decide (frame.value.val=0))=true := by
          simpa only [dispatchRefuses,ordinary,getter,special] using no
        have properties := refused _ _ denied
        exact SpecialRoutes.source_rejection global frame fuel declaration ordinary getter special properties.1 properties.2

def certificate : Interface.DispatchRefusalCertificate where
  source := source
  compiled := compiled
/-- info: 'Solidity.Backend.AbiEntry.DispatchRefusal.compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compiled
/-- info: 'Solidity.Backend.AbiEntry.DispatchRefusal.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source
/-- info: 'Solidity.Backend.AbiEntry.DispatchRefusal.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
/-- info: 'Solidity.Backend.AbiEntry.DispatchRefusal.row_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms row_classification
end Solidity.Backend.AbiEntry.DispatchRefusal
