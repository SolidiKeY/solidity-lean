import Solidity.Examples.Roadmap.V16.CalculusConsumer
import tests.«roadmap-v16».CoreConsumerControls
import tests.«roadmap-v16».MixedMemoryControls
import Lean

/-! Nontrivial clients reuse existing checked fixtures without recreating source
or compiler implementations. Fml, callback readings and exhaustion stay intact.
Imported test fixture oleans are built from these exact committed sources in
the single toolchain-keyed cache before this file is checked. -/
set_option autoImplicit false
namespace Solidity.Roadmap.V16.CalculusControls
open Solidity.Evm
namespace core
open CoreConsumerControls
abbrev K := Memory.CompileExamples.C
abbrev Γ := Memory.CompileExamples.Γ
abbrev bases := Memory.CompileExamples.base

theorem fml_diamond : holds initial (.modal .diamond P .nil post.toFml) :=
  (Spec.sat_iff_holds (.diamond P post) initial).mp diamond

theorem fml_box : holds initial (.modal .box P .nil post.toFml) :=
  (Spec.sat_iff_holds (.box P post) initial).mp box

theorem callback_diamond :
    holdsC (.tt : Fml K []) true initial (.modal .diamond P .nil post.toFml) :=
  (holdsC_iff_holds _ (by decide +kernel) initial).mpr fml_diamond

theorem client : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ compiled.Rep (1 + Evm.Prog.pushes P) 4 bases initial machine o.st m' ∧
    holds o.st post.toFml :=
  callback_compiler_nonpaying compiled input (by decide +kernel) (by decide +kernel) callback_diamond

theorem source_post_and_cell : ∃ o m', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = [w[77]] ∧
    compiled.Rep (1 + Evm.Prog.pushes P) 4 bases initial machine o.st m' ∧
    holds o.st post.toFml ∧ m'.mem 3 = w[8] := by
  obtain ⟨o,m',hs,ht,stack,rep,hpost⟩ := client
  obtain ⟨n,hn,_,cell⟩ := machine_value
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  exact ⟨o,m',hs,ht,stack,rep,hpost,cell⟩

theorem wrong_output : ¬ ∃ m', run compiled.code machine = .ok m' 0 ∧ m'.mem 3 = w[9] := by
  rintro ⟨m',ht,wrong⟩
  obtain ⟨o,n,_,hn,_,_,_,cell⟩ := source_post_and_cell
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  exact (by decide +kernel : w[8] ≠ w[9]) (cell.symm.trans wrong)

theorem wrong_post : ¬ holds initial (.modal .diamond P .nil (.not .tt)) := by
  intro h
  obtain ⟨o,m',_,_,_,_,hpost⟩ := calculus_compiler_nonpaying compiled input (by decide +kernel) h
  exact hpost trivial

theorem box_at_actual_target : ∃ m' o, run compiled.code machine = .ok m' 0 ∧
    P.run initial = .ok o ∧ m'.stack = [w[77]] ∧
    compiled.Rep (1 + Evm.Prog.pushes P) 4 bases initial machine o.st m' ∧ holds o.st post.toFml := by
  obtain ⟨o,m',hs,ht,_,_,_⟩ := client
  obtain ⟨u,hu,stack,rep,hpost⟩ := calculus_compiler_box_target compiled input fml_box ht
  exact ⟨m',u,ht,hu,stack,rep,hpost⟩

theorem callback_box :
    holdsC (.tt : Fml K []) true initial (.modal .box P .nil post.toFml) :=
  (holdsC_iff_holds _ (by decide +kernel) initial).mpr fml_box

theorem callback_box_at_target : ∃ m' o, run compiled.code machine = .ok m' 0 ∧
    P.run initial = .ok o ∧ m'.stack = [w[77]] ∧
    compiled.Rep (1 + Evm.Prog.pushes P) 4 bases initial machine o.st m' ∧ holds o.st post.toFml := by
  obtain ⟨o,m',hs,ht,_,_,_⟩ := client
  obtain ⟨u,hu,stack,rep,hpost⟩ := callback_compiler_box_target compiled input
    (by decide +kernel) callback_box ht
  exact ⟨m',u,ht,hu,stack,rep,hpost⟩

theorem panic_rejected : ¬ holds initial (.modal .box panic.P .nil (.tt : Fml K Γ)) := by
  intro h
  have bad : Spec.sat initial (.box panic.P .tt) :=
    (Spec.sat_iff_holds (.box panic.P .tt) initial).mpr h
  exact panic.no_box bad
end core

namespace memory
open MixedMemoryControls

theorem fml_diamond : holds initial (.modal .diamond P .nil post.toFml) :=
  (Spec.sat_iff_holds (.diamond P post) initial).mp diamond

theorem callback_diamond :
    holdsC (.tt : Fml K []) true initial (.modal .diamond P .nil post.toFml) :=
  (holdsC_iff_holds _ (by decide +kernel) initial).mpr fml_diamond

/-- Actual frame6, reached cost5, aliases, cursor21 and complete protected tail.
Rep is unchanged; the named ordered observations remain the full existing list,
not an assertion of equality at every unobserved memory cell. -/
theorem client : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ compiled.Rep (1 + Evm.Prog.pushes P) 6 bases initial machine o.st m' ∧
    holds o.st post.toFml ∧ targetObserve (.ok m' 0) = some [1,21,3,16,20,99,3,0,0,0,0] := by
  obtain ⟨o,m',hs,ht,stack,rep,hpost⟩ := callback_compiler_nonpaying compiled whole_input
    (by decide +kernel) (by decide +kernel) callback_diamond
  refine ⟨o,m',hs,ht,stack,rep,hpost,?_⟩
  rw [← ht]
  exact target_observed

theorem wrong_alias : ¬ ∃ m', run compiled.code machine = .ok m' 0 ∧
    targetObserve (.ok m' 0) = some [1,21,3,16,16,99,3,0,0,0,0] := by
  rintro ⟨m',ht,wrong⟩
  obtain ⟨o,n,_,hn,_,_,_,good⟩ := client
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  rw [wrong] at good
  cases good

theorem wrong_frame : ¬ compiled.Input 1 3 bases initial machine := MixedMemoryControls.wrong_frame

theorem wrong_allocation : compiled.allocationCost initial ≠ suffixCompiled.allocationCost initial :=
  wrong_stale_cost

theorem wrong_failure : run compiled.code machine ≠ .revert := by
  intro h
  obtain ⟨_,m',_,ht,_⟩ := client
  rw [h] at ht; cases ht
end memory

namespace boundaries
open CoreConsumerControls

theorem payment_alternatives : ∃ o, payment.P.run payment.initial = .ok o ∧
    holds o.st payment.post.toFml ∧
    ((∃ m', run payment.compiled.code payment.machine = .ok m' 0 ∧
      m'.stack = payment.machine.stack ∧
      payment.compiled.Rep (1 + Evm.Prog.pushes payment.P) 0 payment.bases payment.initial payment.machine o.st m') ∨
     (Evm.Prog.pays payment.P = true ∧ run payment.compiled.code payment.machine = .revert ∧
       ∃ candidate, payment.compiled.Rep (1 + Evm.Prog.pushes payment.P) 0 payment.bases payment.initial payment.machine o.st candidate)) :=
  calculus_compiler_diamond payment.compiled payment.input
    ((Spec.sat_iff_holds (.diamond payment.P payment.post) payment.initial).mp payment.diamond)

theorem rejected_payment_diamond :
    ¬ holds payment.initial (.modal .diamond payment.refused .nil .tt) := by
  intro h
  obtain ⟨o,hs,_⟩ := calculus_compiler_source payment.refusedCompiled payment.refused_input h
  rw [payment.refused_source] at hs; cases hs

theorem wrong_oracle_input : ¬ payment.compiled.Input 1 0 payment.bases payment.initial payment.corrupt :=
  payment.corrupt_input_refused

theorem post_callback_present :
    (Fml.modal .box payment.P .nil (.tt : Fml Memory.CompileExamples.C [])).callsBack true = true := by
  decide +kernel

open SpecificationControls in
/-- The unchanged Fml diamond accepts exhaustion, even at a false postcondition. -/
theorem exhausted_false_diamond :
    holds entryState (.modal .diamond (Prog.recBase : Prog TransactionControls.contract [] []) .nil (.not .tt)) := by
  exact ⟨rfl,by intro h; cases h⟩

open SpecificationControls in
/-- The new bridge cannot consume that exhausted execution with a valid Input. -/
theorem exhausted_no_checked_input : ¬ ∃ (c : Compiler.Compilation 0 (Frag.init [])
    (Prog.recBase : Prog TransactionControls.contract [] [])) (base : Nat → Fin W) (m : Machine),
    c.Input 1 0 base entryState m := by
  rintro ⟨c,base,m,input⟩
  obtain ⟨o,hs,_⟩ := calculus_compiler_source c input exhausted_false_diamond
  cases hs
end boundaries
end Solidity.Roadmap.V16.CalculusControls

#print axioms Solidity.Roadmap.V16.calculus_compiler_source

#print axioms Solidity.Roadmap.V16.calculus_compiler_diamond

#print axioms Solidity.Roadmap.V16.calculus_compiler_nonpaying

#print axioms Solidity.Roadmap.V16.calculus_compiler_box_target

#print axioms Solidity.Roadmap.V16.callback_compiler_nonpaying

#print axioms Solidity.Roadmap.V16.callback_compiler_box_target

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut inductives : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity).isPrefixOf n then
      if let .inductInfo info := info then
        inductives := inductives.push (Json.mkObj [
          ("name", toJson n.toString), ("constructors", toJson (info.ctors.map Name.toString))])
  let mut theorems : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity.Roadmap.V16).isPrefixOf ((privateToUserName? n).getD n) ||
        (`_private.Solidity.Roadmap.V16).isPrefixOf n ||
        (`_private.Solidity.Examples.Roadmap.V16).isPrefixOf n then
      if let .thmInfo _ := info then
        let axs ← collectAxioms n
        let ty ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
        let premises ← liftTermElabM do
          Meta.forallBoundedTelescope info.type (some info.type.getNumHeadForalls) fun xs _ => do
            let mut rows : Array Json := #[]
            let mut rawType := info.type
            for x in xs do
              let decl ← x.fvarId!.getDecl
              let ty ← Meta.ppExpr decl.type
              let rawDomain := rawType.consumeMData.bindingDomain!
              rawType := rawType.consumeMData.bindingBody!
              rows := rows.push (Json.mkObj [
                ("name", toJson decl.userName.toString), ("type", toJson ty.pretty),
                ("isProp", toJson (← Meta.isProp decl.type)),
                ("closedExpr", toJson (reprStr rawDomain)),
                ("constants", toJson (decl.type.getUsedConstants.toList.map Name.toString))])
            return rows
        theorems := theorems.push (Json.mkObj [
          ("name", toJson n.toString), ("ownerName", toJson ((privateToUserName? n).getD n).toString),
          ("type", toJson ty), ("premises", .arr premises),
          ("typeConstants", toJson (info.type.getUsedConstants.toList.map Name.toString)),
          ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
          ("axioms", toJson (axs.toList.map Name.toString))])
  let mut definitions : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity.Roadmap.V16).isPrefixOf ((privateToUserName? n).getD n) ||
        (`_private.Solidity.Roadmap.V16).isPrefixOf n ||
        (`_private.Solidity.Examples.Roadmap.V16).isPrefixOf n then
      if let .defnInfo _ := info then
        let axs ← collectAxioms n
        let ty ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
        definitions := definitions.push (Json.mkObj [
          ("name", toJson n.toString), ("ownerName", toJson ((privateToUserName? n).getD n).toString),
          ("type", toJson ty),
          ("typeConstants", toJson (info.type.getUsedConstants.toList.map Name.toString)),
          ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
          ("axioms", toJson (axs.toList.map Name.toString))])
  logInfo m!"V16-INVENTORY {(Json.mkObj [("definitions", .arr definitions), ("modules", toJson (env.header.moduleNames.toList.map Name.toString)), ("inductives", .arr inductives), ("theorems", .arr theorems)]).compress}"

/- Actual producer obligations, printed for exchange; not constructed instances. -/
#check @Solidity.Roadmap.Admission.frontend
#check @Solidity.Roadmap.Admission.sound
#check @Solidity.Roadmap.Admission.complete
#check @Solidity.Roadmap.CheckedFrontend.checked
#check @Solidity.Roadmap.CheckedFrontend.complete
#check @Solidity.Roadmap.Lowering.lower
#check @Solidity.Roadmap.Lowering.pass
#check @Solidity.Roadmap.Lowering.dom
#check @Solidity.Roadmap.Lowering.agrees
#check @Solidity.Roadmap.Lowering.cert
#check @Solidity.Roadmap.Cert.need
#check @Solidity.Roadmap.Cert.need_ok
#check @Solidity.Roadmap.StateExport.decode
#check @Solidity.Roadmap.PublicCorrectness.decode_reach
