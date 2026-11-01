import Solidity.Roadmap.V16.FiniteHeapConsumer
import Solidity.Roadmap.V16.CompilerConsumer
import Solidity.Roadmap.V16.SpecificationControls
import Solidity.Evm.MemoryCompileExamples
import Solidity.Evm.MemoryLoopExamples
import Lean

/-! Actual public core compilation and populated caller state. Failure controls
use the existing intrinsic constructors, not replacement execution semantics. -/
namespace Solidity.Roadmap.V16.CoreConsumerControls
open Solidity.Evm
open Memory.CompileExamples

def machine : Machine := { Memory.CompileExamples.machine with stack := [w[77]] }
abbrev compiled := checkedCore
abbrev P := coreAssignment
abbrev initial := σ

theorem input : compiled.Input 1 4 base initial machine :=
  ⟨fixture_repr.core.stack [w[77]],fixture_repr.core.bound⟩
theorem positive : (P.run initial).toOption.isSome = true := by decide +kernel

def output : Solidity.Out C H Γ := (P.run initial).toOption.get positive
attribute [irreducible] output
theorem source : P.run initial = .ok output := by
  have get_source {α : Type} {r : TRes α} (h : r.toOption.isSome = true) :
      r = .ok (r.toOption.get h) := by
    cases r with
    | error e => cases h
    | ok o => rfl
  simpa only [output] using get_source positive

def post : Spec C Γ := .eq (.pvV .here) (.app0 (.lit ⟨8,by decide⟩))
theorem output_post : Spec.sat output.st post := ⟨⟨8,by decide⟩,by decide +kernel,rfl⟩
theorem diamond : Spec.sat initial (.diamond P post) := by
  simpa only [Spec.sat,source] using output_post
theorem box : Spec.sat initial (.box P post) := by
  simpa only [Spec.sat,source] using output_post

theorem represented : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ compiled.Rep (1 + Evm.Prog.pushes P) 4 base initial machine o.st m' ∧
    Spec.sat o.st post :=
  compiler_nonpaying_diamond compiled input (by decide +kernel) diamond

theorem machine_value : ∃ m', run compiled.code machine = .ok m' 0 ∧ m'.stack = [w[77]] ∧ m'.mem 3 = w[8] := by
  obtain ⟨o,m',hs,ht,stack,rep,hpost⟩ := represented
  have eq : o = output := Except.ok.inj (hs.symm.trans source)
  subst o
  change Sim C (1 + Evm.Prog.pushes P) 0 compiled.frag output.st m' at rep
  have cell := rep.vals (.here : Idx Γ (.val .uint))
  change ∃ a : Fin W, m'.mem 3 = .val a ∧ (TEnv.get (.here : Idx Γ (.val .uint)) output.st.env).val = a.val at cell
  obtain ⟨a,ha,value⟩ := cell
  have eight : (TEnv.get (.here : Idx Γ (.val .uint)) output.st.env).val = 8 := by decide +kernel
  have aeq : a = ⟨8,by decide⟩ := Fin.ext (by change a.val = 8; omega)
  exact ⟨m',ht,stack,by rw [aeq] at ha; exact ha⟩

theorem wrong_output : ¬ ∃ m', run compiled.code machine = .ok m' 0 ∧ m'.mem 3 = w[9] := by
  rintro ⟨m',ht,wrong⟩
  obtain ⟨n,hn,stack,value⟩ := machine_value
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  exact (by decide +kernel : w[8] ≠ w[9]) (value.symm.trans wrong)

theorem box_target : ∃ m' o, run compiled.code machine = .ok m' 0 ∧ P.run initial = .ok o ∧
    m'.stack = [w[77]] ∧ compiled.Rep (1 + Evm.Prog.pushes P) 4 base initial machine o.st m' ∧ Spec.sat o.st post := by
  obtain ⟨m',ht,_,_⟩ := machine_value
  obtain ⟨o,hs,stack,rep,hpost⟩ := compiler_box_target compiled input box ht
  exact ⟨m',o,ht,hs,stack,rep,hpost⟩

/-- Core Input does not pretend to impose the finite-memory frame premise. -/
theorem frame_zero_admitted : compiled.Input 1 0 base initial machine := input

theorem wrong_layout : ¬ compiled.Input (Lmax + 1) 4 base initial machine := by
  intro h
  have bound : Lmax + 1 + Evm.Prog.pushes P ≤ Lmax := h.2
  omega

namespace panic
/-- Ordinary intrinsic assertion failure; no semantics or profile change. -/
def P : Prog C Γ Γ := .cons (.assert (.simple (.bool false))) .nil
def compiled : Compiler.Compilation 0 (Frag.init Γ) P :=
  (Compiler.compile 0 (Frag.init Γ) P).get (by decide +kernel)
attribute [irreducible] compiled
theorem input : compiled.Input 1 4 base initial machine := by
  unfold compiled
  exact ⟨fixture_repr.core.stack [w[77]],fixture_repr.core.bound⟩
theorem source : P.run initial = .error .panic := by rfl
theorem preserved : P.asserts = true ∧ P.run initial = .error .panic ∧ run compiled.code machine = .revert := by
  have result := compiler_source_error compiled input source
  rcases result with ⟨h,ht⟩ | ⟨h,_⟩
  · rcases h with h | ⟨guard,he⟩
    · cases h
    · exact ⟨guard,source,ht⟩
  · cases h

theorem no_box : ¬ Spec.sat initial (.box P .tt) := by simp only [Spec.sat,source,ne_eq,not_true_eq_false,not_false_eq_true]
theorem no_diamond : ¬ Spec.sat initial (.diamond P .tt) := by simp only [Spec.sat,source,reduceCtorEq,not_false_eq_true]
end panic

namespace payment
/-- Real funding and the unchanged default oracle agree through Sim.init. -/
abbrev balances : Fin W → Nat := fun a => if a.val = 0 then 10 else 0
abbrev initial : State C [] := freshT C 10 (by decide) ⟨0,by decide⟩
def machine : Machine := { Machine.init balances ⟨0,by decide⟩ with stack := [w[77]] }
def P : Prog C [] [] := .cons (.transfer (.simple (.lit 1 rfl)) (.simple (.lit 3 rfl))) .nil
def compiled : Compiler.Compilation 0 (Frag.init []) P :=
  (Compiler.compile 0 (Frag.init []) P).get (by decide +kernel)
attribute [irreducible] compiled
abbrev bases : Nat → Fin W := fun _ => wmod 0
theorem input : compiled.Input 1 0 bases initial machine := by
  unfold compiled
  exact ⟨(Sim.init C 10 (by decide) balances ⟨0,by decide⟩ rfl).stack [w[77]],by decide +kernel⟩

theorem positive : (P.run initial).toOption.isSome = true := by decide +kernel
def output : Solidity.Out C [] [] := (P.run initial).toOption.get positive
attribute [irreducible] output
theorem source : P.run initial = .ok output := by
  cases hs : P.run initial with
  | error e =>
    have hp := positive
    simp only [hs,Except.toOption,Option.isSome_none] at hp
    cases hp
  | ok o => simp only [output,hs,Except.toOption,Option.get_some]
def post : Spec C [] := .eq (.app0 (.env .selfBalance)) (.app0 (.lit ⟨7,by decide⟩))
theorem output_post : Spec.sat output.st post := ⟨⟨7,by decide⟩,by decide +kernel,rfl⟩
theorem box : Spec.sat initial (.box P post) := by simpa only [Spec.sat,source] using output_post
theorem diamond : Spec.sat initial (.diamond P post) := by simpa only [Spec.sat,source] using output_post

def target : Machine := { machine with bal := pay machine.bal machine.self (wmod 1) 3 }
theorem target_run : run compiled.code machine = .ok target 0 := by unfold compiled; rfl

theorem represented : ∃ o, P.run initial = .ok o ∧ target.stack = [w[77]] ∧
    compiled.Rep (1 + Evm.Prog.pushes P) 0 bases initial machine o.st target ∧ Spec.sat o.st post :=
  compiler_box_target compiled input box target_run

theorem balances_observed : target.bal ⟨0,by decide⟩ = 7 ∧ target.bal ⟨1,by decide⟩ = 3 ∧ target.stack = [w[77]] := by
  decide +kernel

def refused : Prog C [] [] := .cons (.transfer (.simple (.lit 1 rfl)) (.simple (.lit 11 rfl))) .nil
def refusedCompiled : Compiler.Compilation 0 (Frag.init []) refused :=
  (Compiler.compile 0 (Frag.init []) refused).get (by decide +kernel)
attribute [irreducible] refusedCompiled
theorem refused_input : refusedCompiled.Input 1 0 bases initial machine := by
  unfold refusedCompiled
  exact ⟨(Sim.init C 10 (by decide) balances ⟨0,by decide⟩ rfl).stack [w[77]],by decide +kernel⟩
theorem refused_source : refused.run initial = .error .revert := by rfl
theorem refusal_preserved : Evm.Prog.pays refused = true ∧ refused.run initial = .error .revert ∧
    run refusedCompiled.code machine = .revert := by
  have result := compiler_source_error refusedCompiled refused_input refused_source
  rcases result with ⟨_,ht⟩ | ⟨h,_⟩
  · exact ⟨rfl,refused_source,ht⟩
  · cases h

theorem refused_not_diamond : ¬ Spec.sat initial (.diamond refused .tt) := by
  intro h
  obtain ⟨o,hs,_,_⟩ := compiler_diamond refusedCompiled refused_input h
  rw [refused_source] at hs; cases hs
/-- A source-success/machine-refusal pair with a mismatched oracle is NOT an
inhabited Input or a witness of the guarded agreement alternative. -/
def corrupt : Machine := {machine with accepts := fun _ _ => false}
theorem corrupt_input_refused : ¬ compiled.Input 1 0 bases initial corrupt := by
  intro h
  unfold compiled at h
  have oracle := h.1.oracle (⟨1,by decide⟩ : PrimTy.uint.Denote)
    (⟨3,by decide⟩ : PrimTy.uint.Denote) (wmod 1) (wmod 3) rfl rfl
  change true = false at oracle
  cases oracle

theorem corrupt_target_reverts : run compiled.code corrupt = .revert := by
  unfold compiled
  rfl

theorem mismatched_source_target : P.run initial = .ok output ∧
    run compiled.code corrupt = .revert ∧ ¬ compiled.Input 1 0 bases initial corrupt :=
  ⟨source,corrupt_target_reverts,corrupt_input_refused⟩

end payment

open Lean Elab Term in
elab "publishedSpin%" n:ident : term => do
  let name := mkPrivateNameCore `Solidity.Evm.MemoryLoopExamples
    (`Solidity.Evm.Memory.LoopExamples ++ n.getId)
  unless (← getEnv).contains name do throwError "missing published spin fixture {name}"
  return mkConst name

namespace divergence
abbrev P : Prog C Γ Γ := publishedSpin% spin
def out : Memory.Loops.CompiledProg 0 (Frag.init Γ) P := publishedSpin% spinCompiled
def compiled : Compiler.Compilation 0 (Frag.init Γ) P := .memoryLoops out

theorem accepted : Compiler.compile 0 (Frag.init Γ) P = some compiled := by
  unfold compiled out P
  rfl

theorem input : compiled.Input 1 4 base initial machine := by
  change Memory.StateRepr 1 0 4 (Frag.init Γ) initial base machine ∧
    0 + out.cert.need ≤ 4 ∧ Memory.Loops.Room out.cert 4 initial base machine
  exact ⟨fixture_repr.stack [w[77]],by decide +kernel,
    Memory.Loops.room_nonallocating out.cert (by decide +kernel) initial base machine⟩

theorem source : P.run initial = .error .diverge := Memory.LoopExamples.source_diverges

theorem fault : run compiled.code machine = .fault := by
  have result := compiler_source_error compiled input source
  rcases result with ⟨h,_⟩ | ⟨_,ht⟩
  · rcases h with h | ⟨_,h⟩ <;> cases h
  · rcases ht with ht | ⟨pays,_⟩
    · exact ht
    · have nonpaying : Evm.Prog.pays P = false := by decide +kernel
      rw [nonpaying] at pays; cases pays

theorem box_without_success : Spec.sat initial (.box P .tt) ∧
    ¬ ∃ o, P.run initial = .ok o := by
  constructor
  · simp only [Spec.sat,source,ne_eq,reduceCtorEq,not_false_eq_true]
  · rintro ⟨o,hs⟩; rw [source] at hs; cases hs

theorem no_diamond : ¬ Spec.sat initial (.diamond P .tt) := by
  intro h
  obtain ⟨o,hs,_,_⟩ := compiler_diamond compiled input h
  rw [source] at hs; cases hs

theorem not_finite_path : ¬ (compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true) := by
  decide +kernel

theorem no_target_success : ¬ ∃ m' pc, run compiled.code machine = .ok m' pc := by
  rintro ⟨m',pc,h⟩; rw [fault] at h; cases h
end divergence

namespace exhausted
open SpecificationControls
theorem genuine_diamond_without_success :
    Spec.sat entryState (.diamond (Prog.recBase : Prog TransactionControls.contract [] []) .tt) ∧
    ∀ o, (Prog.recBase : Prog TransactionControls.contract [] []).run entryState ≠ .ok o :=
  ⟨exhausted_diamond,exhausted_has_no_success⟩

theorem refused : Compiler.compile 0 (Frag.init [])
    (Prog.recBase : Prog TransactionControls.contract [] []) = none := rfl
end exhausted
end Solidity.Roadmap.V16.CoreConsumerControls

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
        (`_private.Solidity.Roadmap.V16).isPrefixOf n then
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
        (`_private.Solidity.Roadmap.V16).isPrefixOf n then
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
