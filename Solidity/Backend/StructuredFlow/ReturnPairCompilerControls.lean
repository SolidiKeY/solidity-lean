import Solidity.Backend.StructuredFlow.ReturnPairCompiler
import Solidity.Lowering.G19.ReturnPairControls
import Solidity.Backend.StructuredFlow.ReturnTailCompilerControls

namespace Solidity.Backend.StructuredFlow.ReturnPairCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open Source.SemanticsExamples (G0 F0)
open MappedCondition.Controls (C)
open ConditionalSourceCompiler.Controls (SourceCtx TargetCtx mapping Rel sci sca tci tca)

open ReturnTailCompiler.Controls (source caller machine initial entry snapshot)

def core : Prog C TargetCtx (.val .bool :: TargetCtx) := ReturnPair.code tci tca tci .here tca tci
def emitted : List Instr := emit (C := C) 0 tci tca tci .here tca tci
theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+8) 0 none (M := false)
      (ReturnPair.statement (k := ⟨false,false⟩) sci sca sci .here sca sci) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (if flag then Source.Out.ret (ReturnPair.sourceAfter (source flag) sci flag sci .here sca sci).1
        else Source.Out.normal (ReturnPair.sourceAfter (source flag) sci flag sci .here sca sci).1),
        (.nil,(source flag).2)) ∧
    StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      (core.run (caller flag)) (run emitted (machine flag)) (machine flag) := by
  rcases correct (G0 pipeline) F0 fuel 0 none (M := false) (k := ⟨false,false⟩)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h)
    sci sca sci .here sca sci tci tca tci .here tca tci rfl rfl rfl rfl rfl rfl (entry flag) rfl (by decide) with
    ⟨src,_,_,_,_,compiled⟩
  exact ⟨src,compiled⟩

theorem observed (flag : Bool) : snapshot (run emitted (machine flag)) =
    some [w[1],w[1],.val (bword (!flag)),.val (bword flag),w[99],w[77]] := by
  have typed : core.run (caller flag) =
      .ok ⟨ReturnPair.reached (caller flag) tci flag tci .here tca tci,List.prefix_refl _⟩ :=
    ReturnPair.target_run (caller flag) tci tca flag tci .here tca tci rfl
  have noCanary : codeStoresCell 5 emitted = false := by decide
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      (core.run (caller flag)) (run emitted (machine flag)) (machine flag) := (joined .legacy 0 flag).2
  rw [typed] at compiled
  rcases ReturnTailCompiler.normal_of_ok compiled with ⟨final,hr,stack,repr⟩
  have m0 : final.mem 0 = w[1] := by
    cases flag <;> exact repr.vals (.there (.there (.there .here)))
  have m1 : final.mem 1 = w[1] := by
    cases flag <;> exact repr.vals (.there (.there .here))
  have m2 : final.mem 2 = .val (bword (!flag)) := by
    cases flag <;> exact repr.vals (.there .here)
  have m3 : final.mem 3 = .val (bword flag) := by
    cases flag <;> exact repr.vals .here
  have m5 : final.mem 5 = w[99] := exec_mem noCanary hr
  rw [hr]
  change some ([final.mem 0,final.mem 1,final.mem 2,final.mem 3,final.mem 5] ++ final.stack) = _
  rw [m0,m1,m2,m3,m5,stack]
  rfl

theorem stale_second_donor_refused :
    ReturnPair.Controls.observe (ReturnPair.code (C := C) tci tca tci .here tca tca) false ≠
      ReturnPair.Controls.observe core false := by
  exact ReturnPair.Controls.stale_second_donor_refused

theorem omitted_second_refused :
    ReturnPair.Controls.observe (ReturnTail.code (C := C) tci tca tci .here) false ≠
      ReturnPair.Controls.observe core false := by
  exact ReturnPair.Controls.omitted_second_refused

theorem omitted_second_native_refused :
    snapshot (run (compileProg 0 (ReturnTail.code (C := C) tci tca tci .here)) (machine false)) ≠
      snapshot (run emitted (machine false)) := by
  have typed : (ReturnTail.code (C := C) tci tca tci .here).run (caller false) =
      .ok ⟨ReturnTail.reached (caller false) tci false tci .here,List.prefix_refl _⟩ :=
    ReturnTail.target_run (caller false) tci tca false tci .here rfl
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      ((ReturnTail.code (C := C) tci tca tci .here).run (caller false))
      (run (compileProg 0 (ReturnTail.code (C := C) tci tca tci .here)) (machine false)) (machine false) :=
    prog_sim (ReturnTail.code (C := C) tci tca tci .here) (entry false) rfl (by decide)
  rw [typed] at compiled
  rcases ReturnTailCompiler.normal_of_ok compiled with ⟨bad,hr,_,repr⟩
  intro same
  rw [hr,observed] at same
  have selected : some (bad.mem 0) = some w[1] :=
    congrArg (fun out : Option (List Word) => match out with | some (x :: _) => some x | _ => none) same
  have one : bad.mem 0 = w[1] := Option.some.inj selected
  have zero : bad.mem 0 = w[0] := repr.vals (.there (.there (.there .here)))
  exact (by decide : (w[0] : Word) ≠ w[1]) (zero.symm.trans one)

theorem stale_second_native_refused :
    snapshot (run (compileProg 0 (ReturnPair.code (C := C) tci tca tci .here tca tca)) (machine false)) ≠
      snapshot (run emitted (machine false)) := by
  have typed : (ReturnPair.code (C := C) tci tca tci .here tca tca).run (caller false) =
      .ok ⟨ReturnPair.reached (caller false) tci false tci .here tca tca,List.prefix_refl _⟩ :=
    ReturnPair.target_run (caller false) tci tca false tci .here tca tca rfl
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      ((ReturnPair.code (C := C) tci tca tci .here tca tca).run (caller false))
      (run (compileProg 0 (ReturnPair.code (C := C) tci tca tci .here tca tca)) (machine false)) (machine false) :=
    prog_sim (ReturnPair.code (C := C) tci tca tci .here tca tca) (entry false) rfl (by decide)
  rw [typed] at compiled
  rcases ReturnTailCompiler.normal_of_ok compiled with ⟨bad,hr,_,repr⟩
  intro same
  rw [hr,observed] at same
  have selected : some (bad.mem 0) = some w[1] :=
    congrArg (fun out : Option (List Word) => match out with | some (x :: _) => some x | _ => none) same
  have one : bad.mem 0 = w[1] := Option.some.inj selected
  have zero : bad.mem 0 = w[0] := repr.vals (.there (.there (.there .here)))
  exact (by decide : (w[0] : Word) ≠ w[1]) (zero.symm.trans one)

end Solidity.Backend.StructuredFlow.ReturnPairCompiler.Controls
