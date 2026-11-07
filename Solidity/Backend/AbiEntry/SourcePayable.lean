import Solidity.Backend.AbiEntry.SourcePayableInterface

/-! Payability flags come from the actual exposed Source declarations. The
existing eligibility/selector predicate and actual compiler are reused. -/
namespace Solidity.Backend.AbiEntry.SourcePayable
open Solidity.Evm
open Interface (RouteCtx PayableRouteTable payableRouteResult payableRouteOutcome rawSelectorWord
  sourcePayableResult sourcePayableOutcome)

def entry {E : Source.Env} (global : Source.Glob E) (contract : String)
    (labels : Source.Decl → Fin W) (declaration : Source.Decl) : Option (Fin W × Fin W × Bool) :=
  if (global.prog.body (global.dispatchFn contract declaration)).isSome then
    match declaration.fnSig E with
    | some (parameters,_) => some (SourceRoutes.selectorWord global
        (Source.sigOf E.layout declaration.name parameters),labels declaration,declaration.fnMut == some .payable)
    | none => none
  else none

def tableFor {E : Source.Env} (global : Source.Glob E) (contract : String)
    (labels : Source.Decl → Fin W) (declarations : List Source.Decl) : PayableRouteTable :=
  declarations.filterMap (entry global contract labels)

def table {E : Source.Env} (global : Source.Glob E) (contract : String)
    (labels : Source.Decl → Fin W) : PayableRouteTable := tableFor global contract labels (E.exposed contract)

private theorem list_lookup {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) (fallback : Fin W) (full : 4≤frame.cd.length)
    (declarations : List Source.Decl) :
    payableRouteResult (tableFor global frame.contract labels declarations) fallback (rawSelectorWord frame)=
      ((declarations.find? fun declaration =>
        (global.prog.body (global.dispatchFn frame.contract declaration)).isSome &&
          match declaration.fnSig E with
          | some (parameters,_) => global.selector (Source.sigOf E.layout declaration.name parameters)==frame.cd.take 4
          | none => false).map fun declaration => (labels declaration,declaration.fnMut == some .payable)).getD (fallback,true) := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
    cases body : (global.prog.body (global.dispatchFn frame.contract declaration)).isSome with
    | false =>
      simp only [tableFor,List.filterMap_cons,entry,body,List.find?_cons,Bool.false_and]
      exact ih
    | true =>
      cases signature : declaration.fnSig E with
      | none =>
        simp only [tableFor,List.filterMap_cons,entry,body,if_true,signature,List.find?_cons,Bool.and_false]
        exact ih
      | some pair =>
        rcases pair with ⟨parameters,returns⟩
        have compared := SourceRoutes.predicate global (Source.sigOf E.layout declaration.name parameters) frame full
        cases matched : global.selector (Source.sigOf E.layout declaration.name parameters)==frame.cd.take 4 with
        | false =>
          simpa only [tableFor,List.filterMap_cons,entry,body,if_true,signature,payableRouteResult,
            List.find?_cons,Bool.true_and,compared,matched,Bool.false_eq_true,if_false] using ih
        | true =>
          simp only [tableFor,List.filterMap_cons,entry,body,if_true,signature,payableRouteResult,
            List.find?_cons,Bool.true_and,compared,matched,Option.map_some,Option.getD_some]

theorem lookup {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) (fallback : Fin W) (full : 4≤frame.cd.length) :
    payableRouteResult (table global frame.contract labels) fallback (rawSelectorWord frame)=
      sourcePayableResult global frame labels fallback :=
  list_lookup global frame labels fallback full (E.exposed frame.contract)

theorem selected {E : Source.Env} (global : Source.Glob E) (contract : String)
    (labels : Source.Decl → Fin W) (fallback : Fin W) (C : Contract) (base : Nat) :
    Compiler.compile base (Frag.init RouteCtx) (PayableRoutes.route C (table global contract labels) fallback)=
      some (PayableRoutes.compiled C base (table global contract labels) fallback) :=
  PayableRoutes.selected C base _ fallback

theorem executed {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) (fallback : Fin W) (full : 4≤frame.cd.length)
    (C : Contract) (base : Nat)
    (result : Compiler.Compilation base (Frag.init RouteCtx)
      (PayableRoutes.route C (table global frame.contract labels) fallback))
    (found : Compiler.compile base (Frag.init RouteCtx)
      (PayableRoutes.route C (table global frame.contract labels) fallback)=some result)
    (machine : Machine) (initial : machine.mem base=.val (rawSelectorWord frame))
    (value : machine.callvalue.val=frame.value.val) :
    run result.code machine=sourcePayableOutcome global frame labels fallback base machine := by
  have reached := PayableRoutes.executed C base (table global frame.contract labels) fallback result found
    machine (rawSelectorWord frame) initial
  simpa only [payableRouteOutcome,lookup global frame labels fallback full,value,sourcePayableOutcome] using reached

/-- The actual ordinary Source dispatch rejects before decoding, with empty
revert bytes. No statement about the unmatched special-function path. -/
theorem source_rejection {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (fuel : Nat) (declaration : Source.Decl) (parameters returns : List Source.STy)
    (picked : global.pickFn frame frame.cd=some declaration)
    (signature : declaration.fnSig E=some (parameters,returns))
    (nonempty : frame.cd.isEmpty=false) (nonzero : frame.value.val≠0)
    (nonpayable : (declaration.fnMut == some .payable)=false) :
    Source.dispatch global frame (fuel+1) frame.cd=Source.EM.halt (.revert []) := by
  simp only [Source.dispatch,picked,signature,nonempty,decide_eq_true nonzero,bne,nonpayable,
    Bool.not_false,Bool.true_and,if_true]
  rfl

def certificate : Interface.SourcePayableCertificate table where
  lookup := lookup
  executed := executed
/-- info: 'Solidity.Backend.AbiEntry.SourcePayable.lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lookup
/-- info: 'Solidity.Backend.AbiEntry.SourcePayable.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.SourcePayable.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.SourcePayable.source_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_rejection
/-- info: 'Solidity.Backend.AbiEntry.SourcePayable.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.SourcePayable
