import Solidity.Backend.StructuredFlow.ReturnTailCompiler
import Solidity.Backend.StructuredFlow.ConditionalSourceCompilerControls

namespace Solidity.Backend.StructuredFlow.ReturnTailCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open Source.SemanticsExamples (G0 F0)
open MappedCondition.Controls (C)
open ConditionalSourceCompiler.Controls (SourceCtx TargetCtx mapping Rel sci sca tci tca)

def source (flag : Bool) : Source.EMState Source.SemanticsExamples.E0 SourceCtx :=
  ((ConditionalSourceCompiler.Controls.source flag).1.set .here (.bool (!flag)),
    (ConditionalSourceCompiler.Controls.source flag).2)
def caller (flag : Bool) : State C TargetCtx :=
  (ConditionalSourceCompiler.Controls.caller flag).setLocal .here (!flag)
def machine (flag : Bool) : Machine :=
  {ConditionalSourceCompiler.Controls.machine flag with
    mem := upd (ConditionalSourceCompiler.Controls.machine flag).mem 2 (.val (bword (!flag)))}

theorem initial (flag : Bool) : mapping.Related Rel (source flag).1 (caller flag).env := by
  intro τ i
  exact (ContextMap.related_write mapping Rel
    (ConditionalSourceCompiler.Controls.source flag).1 (ConditionalSourceCompiler.Controls.caller flag).env
    (ConditionalSourceCompiler.Controls.initial flag) .here .here rfl (.bool (!flag)) (!flag) rfl) i

theorem entry (flag : Bool) : Sim C 1 0 (Frag.init TargetCtx) (caller flag) (machine flag) := by
  exact Sim.setLocalVal (ConditionalSourceCompiler.Controls.entry flag) .here
    (v := !flag) (w := .val (bword (!flag))) rfl

def core : Prog C TargetCtx (.val .bool :: TargetCtx) := ReturnTail.code tci tca .here tci
def emitted : List Instr := emit (C := C) 0 tci tca .here tci
def snapshot (out : Evm.Out) : Option (List Word) :=
  match out with
  | .ok post 0 => some ([post.mem 0,post.mem 1,post.mem 2,post.mem 3,post.mem 5] ++ post.stack)
  | _ => none

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+6) 0 none (M := false)
      (ReturnTail.statement (k := ⟨false,false⟩) sci sca .here sci) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (if flag then Source.Out.ret (ReturnTail.sourceAfter (source flag) sci flag .here sci).1
        else Source.Out.normal (ReturnTail.sourceAfter (source flag) sci flag .here sci).1),
        (.nil,(source flag).2)) ∧
    StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      (core.run (caller flag)) (run emitted (machine flag)) (machine flag) := by
  rcases correct (G0 pipeline) F0 fuel 0 none (M := false) (k := ⟨false,false⟩)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h)
    sci sca .here sci tci tca .here tci rfl rfl rfl rfl (entry flag) rfl (by decide) with
    ⟨src,_,_,_,_,compiled⟩
  exact ⟨src,compiled⟩

theorem observed (flag : Bool) : snapshot (run emitted (machine flag)) =
    some [.val (bword flag),.val (bword flag),w[0],.val (bword flag),w[99],w[77]] := by
  have typed : core.run (caller flag) =
      .ok ⟨ReturnTail.reached (caller flag) tci flag .here tci,List.prefix_refl _⟩ :=
    ReturnTail.target_run (caller flag) tci tca flag .here tci rfl
  have noCanary : codeStoresCell 5 emitted = false := by decide
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      (core.run (caller flag)) (run emitted (machine flag)) (machine flag) := (joined .legacy 0 flag).2
  rw [typed] at compiled
  rcases normal_of_ok compiled with ⟨final,hr,stack,repr⟩
  have m0 : final.mem 0 = .val (bword flag) := by
    cases flag <;> exact repr.vals (.there (.there (.there .here)))
  have m1 : final.mem 1 = .val (bword flag) := by
    cases flag <;> exact repr.vals (.there (.there .here))
  have m2 : final.mem 2 = w[0] := by
    cases flag <;> exact repr.vals (.there .here)
  have m3 : final.mem 3 = .val (bword flag) := by
    cases flag <;> exact repr.vals .here
  have m5 : final.mem 5 = w[99] := exec_mem noCanary hr
  rw [hr]
  change some ([final.mem 0,final.mem 1,final.mem 2,final.mem 3,final.mem 5] ++ final.stack) = _
  rw [m0,m1,m2,m3,m5,stack]
  rfl

def eager : Prog C TargetCtx (.val .bool :: TargetCtx) :=
  (assignLocalOperand (C := C) tci tca).code.join
    (.cons (.assignLocal (.there .here) (.simple (.local (.there tci)))) .nil)

theorem eager_tail_refused :
    snapshot (run (compileProg 0 eager) (machine true)) ≠ snapshot (run emitted (machine true)) := by
  have typed : eager.run (caller true) =
      .ok ⟨((caller true).setLocal tci true).push (t := .val .bool) true |>.setLocal (.there .here) true,
        List.prefix_refl _⟩ := by rfl
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      (eager.run (caller true)) (run (compileProg 0 eager) (machine true)) (machine true) :=
    prog_sim eager (entry true) rfl (by decide)
  rw [typed] at compiled
  rcases normal_of_ok compiled with ⟨bad,hr,_,repr⟩
  intro same
  rw [hr,observed] at same
  have selected : some (bad.mem 2) = some w[0] := congrArg (fun out : Option (List Word) => match out with | some (_ :: _ :: x :: _) => some x | _ => none) same
  change some (bad.mem 2) = some w[0] at selected
  have zero : bad.mem 2 = w[0] := Option.some.inj selected
  have one : bad.mem 2 = w[1] := repr.vals (.there .here)
  exact (by decide : (w[1] : Word) ≠ w[0]) (one.symm.trans zero)

theorem omitted_tail_refused :
    snapshot (run (compileProg 0 (assignLocalOperand (C := C) tci tca).code) (machine false)) ≠
      snapshot (run emitted (machine false)) := by
  have typed : (assignLocalOperand (C := C) tci tca).code.run (caller false) =
      .ok ⟨((caller false).setLocal tci false).push (t := .val .bool) false,List.prefix_refl _⟩ :=
    assigned_condition_prefix_run (caller false) tci tca
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      ((assignLocalOperand (C := C) tci tca).code.run (caller false))
      (run (compileProg 0 (assignLocalOperand (C := C) tci tca).code) (machine false)) (machine false) :=
    prog_sim (assignLocalOperand (C := C) tci tca).code (entry false) rfl (by decide)
  rw [typed] at compiled
  rcases normal_of_ok compiled with ⟨bad,hr,_,repr⟩
  intro same
  rw [hr,observed] at same
  have selected : some (bad.mem 2) = some w[0] := congrArg (fun out : Option (List Word) => match out with | some (_ :: _ :: x :: _) => some x | _ => none) same
  change some (bad.mem 2) = some w[0] at selected
  have zero : bad.mem 2 = w[0] := Option.some.inj selected
  have one : bad.mem 2 = w[1] := repr.vals (.there .here)
  exact (by decide : (w[1] : Word) ≠ w[0]) (one.symm.trans zero)

/-- False fallthrough may overwrite the caller condition true; the private
selector remains false, preserving the actual Source outcome classification. -/
theorem alias_observed :
    snapshot (run (emit (C := C) 0 tci tca tci .here) (machine false)) =
      some [w[0],w[1],w[1],w[0],w[99],w[77]] := by
  have typed : (ReturnTail.code (C := C) tci tca tci .here).run (caller false) =
      .ok ⟨ReturnTail.reached (caller false) tci false tci .here,List.prefix_refl _⟩ :=
    ReturnTail.target_run (caller false) tci tca false tci .here rfl
  have noCanary : codeStoresCell 5 (emit (C := C) 0 tci tca tci .here) = false := by decide
  have compiled : StmtOut C 1 0 (Frag.init (.val .bool :: TargetCtx)) false false false
      ((ReturnTail.code (C := C) tci tca tci .here).run (caller false))
      (run (emit (C := C) 0 tci tca tci .here) (machine false)) (machine false) :=
    prog_sim (ReturnTail.code (C := C) tci tca tci .here) (entry false) rfl (by decide)
  rw [typed] at compiled
  rcases normal_of_ok compiled with ⟨final,hr,stack,repr⟩
  have m0 : final.mem 0 = w[0] := repr.vals (.there (.there (.there .here)))
  have m1 : final.mem 1 = w[1] := repr.vals (.there (.there .here))
  have m2 : final.mem 2 = w[1] := repr.vals (.there .here)
  have m3 : final.mem 3 = w[0] := repr.vals .here
  have m5 : final.mem 5 = w[99] := exec_mem noCanary hr
  rw [hr]
  change some ([final.mem 0,final.mem 1,final.mem 2,final.mem 3,final.mem 5] ++ final.stack) = _
  rw [m0,m1,m2,m3,m5,stack]
  rfl

end Solidity.Backend.StructuredFlow.ReturnTailCompiler.Controls
