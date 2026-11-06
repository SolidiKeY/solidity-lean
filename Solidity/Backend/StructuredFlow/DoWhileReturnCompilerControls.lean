import Solidity.Backend.StructuredFlow.DoWhileReturnCompiler
import Solidity.Lowering.G19.AssignmentDoWhileReturnControls
import Solidity.Backend.StructuredFlow.ReturnTailCompilerControls

namespace Solidity.Backend.StructuredFlow.DoWhileReturnCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open Source.SemanticsExamples (G0 F0 E0)
open MappedCondition.Controls (C)
open ConditionalSourceCompiler.Controls (SourceCtx TargetCtx mapping Rel sci sca tci tca)
open ReturnTailCompiler.Controls (source caller machine initial entry snapshot)
open AssignmentDoWhileReturn (code reached body)

def core : Prog C TargetCtx (.val .bool :: TargetCtx) := code mapping sci sca rfl rfl
def emitted : List Instr := emit (C := C) 0 mapping sci sca rfl rfl

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag checked : Bool)
    (condition : Source.RExpr E0 SourceCtx .bool) :
    (Source.execS (G0 pipeline) {F0 with checked := checked} (fuel+6) 0 none (M := false)
      (.doWhile (l := false) (u := false) (body sci sca) condition) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (Source.Out.ret ((source flag).1.set sci (.bool flag))),(.nil,(source flag).2)) ∧
    StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      (core.run (caller flag)) (run emitted (machine flag)) (machine flag) := by
  rcases correct (G0 pipeline) {F0 with checked := checked} fuel 0 none
    (M := false) (l := false) (u := false) (source flag) (caller flag) mapping Rel
    (initial flag) (fun _ _ h => h) sci sca rfl rfl rfl rfl condition
    (entry flag) rfl (by decide) with ⟨src,_,_,_,_,compiled⟩
  exact ⟨src,compiled⟩

theorem observed (flag : Bool) : snapshot (run emitted (machine flag)) =
    some [.val (bword flag),.val (bword flag),.val (bword (!flag)),w[1],w[99],w[77]] := by
  have typed : core.run (caller flag) =
      .ok ⟨reached mapping sci sca rfl rfl (caller flag),List.prefix_refl _⟩ :=
    AssignmentDoWhileReturn.target_run mapping sci sca rfl rfl (caller flag)
  have noCanary : codeStoresCell 5 emitted = false := by decide
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      (core.run (caller flag)) (run emitted (machine flag)) (machine flag) :=
    (joined .legacy 0 flag false (.bool true)).2
  rw [typed] at compiled
  rcases ReturnTailCompiler.normal_of_ok compiled with ⟨final,hr,stack,repr⟩
  have m0 : final.mem 0 = .val (bword flag) := by
    cases flag <;> exact repr.vals (.there (.there (.there .here)))
  have m1 : final.mem 1 = .val (bword flag) := by
    cases flag <;> exact repr.vals (.there (.there .here))
  have m2 : final.mem 2 = .val (bword (!flag)) := by
    cases flag <;> exact repr.vals (.there .here)
  have m3 : final.mem 3 = w[1] := repr.vals .here
  have m5 : final.mem 5 = w[99] := exec_mem noCanary hr
  rw [hr]
  change some ([final.mem 0,final.mem 1,final.mem 2,final.mem 3,final.mem 5] ++ final.stack) = _
  rw [m0,m1,m2,m3,m5,stack]
  rfl

theorem wrong_return_flag_refused :
    snapshot (run (compileProg 0 (AssignmentReturnFlag.code (C := C) mapping sci sca rfl rfl))
      (machine false)) ≠ snapshot (run emitted (machine false)) := by
  have typed : (AssignmentReturnFlag.code (C := C) mapping sci sca rfl rfl).run (caller false) =
      .ok ⟨AssignmentReturnFlag.reached mapping sci sca rfl rfl (caller false),List.prefix_refl _⟩ :=
    assigned_condition_prefix_run (caller false) tci tca
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      ((AssignmentReturnFlag.code (C := C) mapping sci sca rfl rfl).run (caller false))
      (run (compileProg 0 (AssignmentReturnFlag.code (C := C) mapping sci sca rfl rfl))
        (machine false)) (machine false) :=
    prog_sim (AssignmentReturnFlag.code (C := C) mapping sci sca rfl rfl) (entry false) rfl (by decide)
  rw [typed] at compiled
  rcases ReturnTailCompiler.normal_of_ok compiled with ⟨bad,hr,_,repr⟩
  intro same
  rw [hr,observed] at same
  have selected : some (bad.mem 3) = some w[1] :=
    congrArg (fun out : Option (List Word) => match out with | some (_ :: _ :: _ :: x :: _) => some x | _ => none) same
  have one : bad.mem 3 = w[1] := Option.some.inj selected
  have zero : bad.mem 3 = w[0] := repr.vals .here
  exact (by decide : (w[0] : Word) ≠ w[1]) (zero.symm.trans one)

def eagerCondition : Prog C TargetCtx (.val .bool :: TargetCtx) :=
  core.join (.cons (.assignLocal (.there tci) (.simple (.bool false))) .nil)

theorem eager_condition_refused :
    snapshot (run (compileProg 0 eagerCondition) (machine true)) ≠
      snapshot (run emitted (machine true)) := by
  have typed : eagerCondition.run (caller true) =
      .ok ⟨(reached mapping sci sca rfl rfl (caller true)).setLocal (.there tci) false,
        List.prefix_refl _⟩ := by rfl
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      (eagerCondition.run (caller true)) (run (compileProg 0 eagerCondition) (machine true))
      (machine true) := prog_sim eagerCondition (entry true) rfl (by decide)
  rw [typed] at compiled
  rcases ReturnTailCompiler.normal_of_ok compiled with ⟨bad,hr,_,repr⟩
  intro same
  rw [hr,observed] at same
  have selected : some (bad.mem 1) = some w[1] :=
    congrArg (fun out : Option (List Word) => match out with | some (_ :: x :: _) => some x | _ => none) same
  have one : bad.mem 1 = w[1] := Option.some.inj selected
  have zero : bad.mem 1 = w[0] := repr.vals (.there (.there .here))
  exact (by decide : (w[0] : Word) ≠ w[1]) (zero.symm.trans one)

end Solidity.Backend.StructuredFlow.DoWhileReturnCompiler.Controls
