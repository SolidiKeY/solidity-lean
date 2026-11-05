import Solidity.Backend.AbiEntry.GetterRoutesInterface

/-! Actual exposed ordinary rows followed by actual Source getter rows, then
special choice, through EntryRoutes. These are labels, not executed bodies. -/
namespace Solidity.Backend.AbiEntry.GetterRoutes
open Solidity.Evm
open Interface (RouteCtx PayableRouteTable SpecialRow ordinaryResult rawSelectorWord getterRow sourceDispatchRow
  specialOutcome specialRowOutcome)

def getterEntry {E : Source.Env} (global : Source.Glob E) (labels : Source.Decl → Fin W)
    (entry : Source.Decl × List Source.STy × Source.STy) : Fin W × Fin W × Bool :=
  (SourceRoutes.selectorWord global (Source.sigOf E.layout entry.1.name entry.2.1),labels entry.1,false)
def getterTable {E : Source.Env} (global : Source.Glob E) (contract : String)
    (labels : Source.Decl → Fin W) : PayableRouteTable :=
  (E.getters contract).map (getterEntry global labels)
def table {E : Source.Env} (global : Source.Glob E) (contract : String)
    (labels : Source.Decl → Fin W) : PayableRouteTable :=
  SourcePayable.table global contract labels++getterTable global contract labels

private theorem append_lookup (left right : PayableRouteTable) (selector : Fin W) :
    ordinaryResult (left++right) selector=(ordinaryResult left selector).orElse (fun _ => ordinaryResult right selector) := by
  simp only [ordinaryResult,List.find?_append]
  cases left.find? (fun row => decide (row.1.val=selector.val)) <;> rfl

private theorem getter_list {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) (full : 4≤frame.cd.length)
    (getters : List (Source.Decl × List Source.STy × Source.STy)) :
    ordinaryResult (getters.map (getterEntry global labels)) (rawSelectorWord frame)=
      (getters.find? fun entry => global.selector (Source.sigOf E.layout entry.1.name entry.2.1)==frame.cd.take 4).map
        (getterRow labels) := by
  induction getters with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨declaration,parameters,returns⟩
    have compared := SourceRoutes.predicate global (Source.sigOf E.layout declaration.name parameters) frame full
    cases matched : global.selector (Source.sigOf E.layout declaration.name parameters)==frame.cd.take 4 with
    | false =>
      simpa only [List.map_cons,getterEntry,ordinaryResult,List.find?_cons,compared,matched,
        Bool.false_eq_true,if_false] using ih
    | true =>
      simp only [List.map_cons,getterEntry,ordinaryResult,List.find?_cons,compared,matched,
        Option.map_some,getterRow]

private theorem nonempty (frame : Source.Fr) (full : 4≤frame.cd.length) : frame.cd.isEmpty=false := by
  apply List.isEmpty_eq_false_iff.mpr
  intro empty
  rw [empty] at full
  exact (by decide : ¬4≤([] : List UInt8).length) full

theorem getter_lookup {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) (full : 4≤frame.cd.length) :
    ordinaryResult (getterTable global frame.contract labels) (rawSelectorWord frame)=
      (global.pickGetter frame frame.cd).map (getterRow labels) := by
  rw [getterTable,getter_list global frame labels full]
  simp only [Source.Glob.pickGetter,nonempty frame full,Bool.not_false,Bool.true_and]

theorem lookup {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) (full : 4≤frame.cd.length) :
    ordinaryResult (table global frame.contract labels) (rawSelectorWord frame)=
      ((global.pickFn frame frame.cd).map (EntryRoutes.ordinaryRow labels)).orElse
        (fun _ => (global.pickGetter frame frame.cd).map (getterRow labels)) := by
  rw [table,append_lookup,EntryRoutes.source_ordinary global frame labels full,getter_lookup global frame labels full]

/-- Getters also require a full four-byte selector; no storage/type execution
premise is needed to prove short-input absence. -/
theorem getter_short {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (short : frame.cd.length<4) : global.pickGetter frame frame.cd=none := by
  unfold Source.Glob.pickGetter
  apply List.find?_eq_none.mpr
  intro entry _ yes
  have matched := (Bool.and_eq_true_iff.mp yes).2
  have same := eq_of_beq matched
  have absent := SelectorMatch.short_no_match (SelectorMatch.sourceSelector global
    (Source.sigOf E.layout entry.1.name entry.2.1)) frame.cd short
  rw [SelectorMatch.source_bytes] at absent
  have reverse : (frame.cd.take 4==global.selector (Source.sigOf E.layout entry.1.name entry.2.1))=true :=
    beq_iff_eq.mpr same.symm
  rw [reverse] at absent
  cases absent

def compiled {E : Source.Env} (global : Source.Glob E) (contract : String) (labels : Source.Decl → Fin W)
    (C : Contract) (base : Nat) :=
  EntryRoutes.compiled C base (table global contract labels)
    (SpecialRoutes.receiveRow E contract labels) (SpecialRoutes.fallbackRow E contract labels)

theorem selected {E : Source.Env} (global : Source.Glob E) (contract : String) (labels : Source.Decl → Fin W)
    (C : Contract) (base : Nat) :
    Compiler.compile base (Frag.init RouteCtx)
      (EntryRoutes.route C (table global contract labels)
        (SpecialRoutes.receiveRow E contract labels) (SpecialRoutes.fallbackRow E contract labels))=
      some (compiled global contract labels C base) := EntryRoutes.selected C base _ _ _

theorem executed {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr) (labels : Source.Decl → Fin W)
    (C : Contract) (base : Nat)
    (result : Compiler.Compilation base (Frag.init RouteCtx)
      (EntryRoutes.route C (table global frame.contract labels)
        (SpecialRoutes.receiveRow E frame.contract labels) (SpecialRoutes.fallbackRow E frame.contract labels)))
    (found : Compiler.compile base (Frag.init RouteCtx)
      (EntryRoutes.route C (table global frame.contract labels)
        (SpecialRoutes.receiveRow E frame.contract labels) (SpecialRoutes.fallbackRow E frame.contract labels))=some result)
    (machine : Machine) (size : Fin W) (initial : machine.mem base=.val (rawSelectorWord frame))
    (length : machine.mem (base+1)=.val size) (bytes : size.val=frame.cd.length) :
    run result.code machine=specialRowOutcome base (sourceDispatchRow global frame labels) machine := by
  have reached := EntryRoutes.executed C base (table global frame.contract labels) _ _ result found
    machine (rawSelectorWord frame) size initial length
  have special : specialOutcome base (SpecialRoutes.receiveRow E frame.contract labels)
      (SpecialRoutes.fallbackRow E frame.contract labels) size machine=
        specialRowOutcome base ((Interface.sourceSpecial E frame).map (SpecialRoutes.row labels)) machine := by
    rw [specialOutcome,SpecialRoutes.source_lookup E frame labels size bytes]
  by_cases short : frame.cd.length<4
  · simpa only [Interface.entryRouteOutcome,bytes,if_pos short,special,sourceDispatchRow,
      ShortRoutes.source_short global frame short,getter_short global frame short,
      Option.map_none,Option.orElse_none] using reached
  · have full : 4≤frame.cd.length := Nat.le_of_not_gt short
    rw [Interface.entryRouteOutcome,bytes,if_neg short,lookup global frame labels full] at reached
    rw [special] at reached
    cases ordinary : global.pickFn frame frame.cd with
    | none =>
      cases getter : global.pickGetter frame frame.cd <;>
        simpa only [sourceDispatchRow,ordinary,getter,Option.map_none,Option.map_some,Option.orElse_none,Option.orElse_some]
          using reached
    | some declaration =>
      simpa only [sourceDispatchRow,ordinary,Option.map_some,Option.orElse_some] using reached

/-- Exact existing Source getter value refusal, before argument/storage work. -/
theorem source_getter_rejection {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (fuel : Nat) (entry : Source.Decl × List Source.STy × Source.STy)
    (ordinary : global.pickFn frame frame.cd=none) (getter : global.pickGetter frame frame.cd=some entry)
    (nonzero : frame.value.val≠0) :
    Source.dispatch global frame (fuel+1) frame.cd=Source.EM.halt (.revert []) := by
  simp only [Source.dispatch,ordinary,getter,if_pos nonzero]
  rfl

def certificate : Interface.GetterRoutesCertificate table where
  lookup := lookup
  executed := executed
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutes.getter_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms getter_lookup
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutes.lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lookup
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutes.getter_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms getter_short
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutes.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutes.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutes.source_getter_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_getter_rejection
/-- info: 'Solidity.Backend.AbiEntry.GetterRoutes.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.GetterRoutes
