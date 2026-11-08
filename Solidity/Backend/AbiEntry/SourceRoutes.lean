import Solidity.Backend.AbiEntry.SourceRoutesInterface
import Solidity.Backend.AbiEntry.SelectorMatch

/-! Source-derived ordinary route tables. Construction reads only compile-time
contract/declaration facts, never calldata or the chosen declaration. Body and
getter/receive/fallback execution remain separate obligations. -/
namespace Solidity.Backend.AbiEntry.SourceRoutes
open Solidity.Evm
open Interface (RouteCtx RouteTable routeResult rawSelectorWord)

def selectorWord {E : Source.Env} (global : Source.Glob E) (signature : List Char) : Fin W :=
  ⟨(global.fixed.hash (Source.asciiBytes signature)).val/2^224,
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (global.fixed.hash (Source.asciiBytes signature)).isLt⟩

private theorem flags (left right : Bool) (same : Scalar.flag left=Scalar.flag right) : left=right := by
  cases left with
  | false => cases right with
    | false => rfl
    | true => exact False.elim ((by decide : (0 : Scalar.Word)≠1) same)
  | true => cases right with
    | false => exact False.elim ((by decide : (1 : Scalar.Word)≠0) same)
    | true => rfl

private theorem eq_reverse (left right : Nat) : decide (left=right)=decide (right=left) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact eq_comm

set_option backward.isDefEq.respectTransparency false in
theorem predicate {E : Source.Env} (global : Source.Glob E) (signature : List Char)
    (frame : Source.Fr) (full : 4≤frame.cd.length) :
    decide ((selectorWord global signature).val=(rawSelectorWord frame).val)=
      (global.selector signature==frame.cd.take 4) := by
  have numeric := SelectorMatch.numeric (SelectorMatch.sourceSelector global signature)
    (BitVec.ofNat 256 (Solidity.AbiEntry.load frame.cd 0)) []
  have source := SelectorMatch.source_raw global signature frame full []
  have bounded : Solidity.AbiEntry.load frame.cd 0<2^256 := Solidity.AbiEntry.load_lt frame.cd 0
  have normalized : Scalar.run (SelectorMatch.code (SelectorMatch.sourceSelector global signature))
      [BitVec.ofNat 256 (Solidity.AbiEntry.load frame.cd 0)]=
      some [Scalar.flag (decide ((rawSelectorWord frame).val=(selectorWord global signature).val))] := by
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounded,SelectorMatch.source_value,
      rawSelectorWord,selectorWord] using numeric
  have same := (List.cons.inj (Option.some.inj (normalized.symm.trans source))).1
  have checked := flags (decide ((rawSelectorWord frame).val=(selectorWord global signature).val))
    (global.selector signature==frame.cd.take 4) same
  exact (eq_reverse (selectorWord global signature).val (rawSelectorWord frame).val).trans checked

def entry {E : Source.Env} (global : Source.Glob E) (contract : String)
    (labels : Source.Decl → Fin W) (declaration : Source.Decl) : Option (Fin W × Fin W) :=
  if (global.prog.body (global.dispatchFn contract declaration)).isSome then
    match declaration.fnSig E with
    | some (parameters,_) => some (selectorWord global (Source.sigOf E.layout declaration.name parameters),labels declaration)
    | none => none
  else none

def tableFor {E : Source.Env} (global : Source.Glob E) (contract : String)
    (labels : Source.Decl → Fin W) (declarations : List Source.Decl) : RouteTable :=
  declarations.filterMap (entry global contract labels)

def table {E : Source.Env} (global : Source.Glob E) (contract : String)
    (labels : Source.Decl → Fin W) : RouteTable := tableFor global contract labels (E.exposed contract)

private theorem list_lookup {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) (fallback : Fin W) (full : 4≤frame.cd.length)
    (declarations : List Source.Decl) :
    routeResult (tableFor global frame.contract labels declarations) fallback (rawSelectorWord frame)=
      ((declarations.find? fun declaration =>
        (global.prog.body (global.dispatchFn frame.contract declaration)).isSome &&
          match declaration.fnSig E with
          | some (parameters,_) => global.selector (Source.sigOf E.layout declaration.name parameters)==frame.cd.take 4
          | none => false).map labels).getD fallback := by
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
        have compared := predicate global (Source.sigOf E.layout declaration.name parameters) frame full
        cases matched : global.selector (Source.sigOf E.layout declaration.name parameters)==frame.cd.take 4 with
        | false =>
          simpa only [tableFor,List.filterMap_cons,entry,body,if_true,signature,routeResult,
            List.find?_cons,Bool.true_and,compared,matched,Bool.false_eq_true,if_false] using ih
        | true =>
          simp only [tableFor,List.filterMap_cons,entry,body,if_true,signature,routeResult,
            List.find?_cons,Bool.true_and,compared,matched,Option.map_some,Option.getD_some]

theorem lookup {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) (fallback : Fin W) (full : 4≤frame.cd.length) :
    routeResult (table global frame.contract labels) fallback (rawSelectorWord frame)=
      ((global.pickFn frame frame.cd).map labels).getD fallback :=
  list_lookup global frame labels fallback full (E.exposed frame.contract)

theorem selected {E : Source.Env} (global : Source.Glob E) (contract : String)
    (labels : Source.Decl → Fin W) (fallback : Fin W) (C : Contract) (base : Nat) :
    Compiler.compile base (Frag.init RouteCtx) (SelectorRoutes.route C (table global contract labels) fallback)=
      some (SelectorRoutes.compiled C base (table global contract labels) fallback) :=
  SelectorRoutes.selected C base _ fallback

theorem executed {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin W) (fallback : Fin W) (full : 4≤frame.cd.length)
    (C : Contract) (base : Nat)
    (result : Compiler.Compilation base (Frag.init RouteCtx) (SelectorRoutes.route C (table global frame.contract labels) fallback))
    (found : Compiler.compile base (Frag.init RouteCtx)
      (SelectorRoutes.route C (table global frame.contract labels) fallback)=some result)
    (machine : Machine) (initial : machine.mem base=.val (rawSelectorWord frame)) :
    run result.code machine=.ok
      {machine with mem := upd machine.mem (base+1) (.val (((global.pickFn frame frame.cd).map labels).getD fallback))} 0 := by
  have reached := SelectorRoutes.executed C base (table global frame.contract labels) fallback result found
    machine (rawSelectorWord frame) initial
  rw [lookup global frame labels fallback full] at reached
  exact reached

def certificate : Interface.SourceRoutesCertificate table where
  lookup := lookup
  executed := executed

/-- info: 'Solidity.Backend.AbiEntry.SourceRoutes.predicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms predicate
/-- info: 'Solidity.Backend.AbiEntry.SourceRoutes.lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lookup
/-- info: 'Solidity.Backend.AbiEntry.SourceRoutes.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.SourceRoutes.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.SourceRoutes.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.SourceRoutes
