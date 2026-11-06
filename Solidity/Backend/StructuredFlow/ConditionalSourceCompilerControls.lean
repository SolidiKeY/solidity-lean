import Solidity.Backend.StructuredFlow.ConditionalSourceCompiler
import Solidity.Backend.StructuredFlow.MappedConditionControls
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open Source.SemanticsExamples (E0 G0 F0 s0)
open MappedCondition.Controls (C)

abbrev SourceCtx : Source.RCtx := [.bool,.bool,.bool]
abbrev TargetCtx : Ctx := [.val .bool,.val .bool,.val .bool]
def source (flag : Bool) : Source.EMState E0 SourceCtx :=
  (.cons (.bool false) (.cons (.bool (!flag)) (.cons (.bool flag) .nil)),s0)
def caller (flag : Bool) : State C TargetCtx := (MappedCondition.Controls.caller flag).push (t := .val .bool) false
def mapping : ContextMap SourceCtx TargetCtx := MappedCondition.Controls.mapping.cons .bool (.val .bool)
def Rel : (τ : Source.STy) → (u : LTy) → Source.Val E0.layout τ → u.TDenote C (caller false).H → Prop
  | .bool,.val .bool,v,b => v = .bool b
  | _,_,_,_ => False

def sci : Source.Idx SourceCtx .bool := .there .here
def sca : Source.Idx SourceCtx .bool := .there (.there .here)
def tci : Idx TargetCtx (.val .bool) := .there .here
def tca : Idx TargetCtx (.val .bool) := .there (.there .here)
def core : Prog C TargetCtx TargetCtx := ConditionalStatement.code tci tca tci .here tca tci
def emitted : List Instr := emit (C := C) 0 tci tca tci .here tca tci
def machine (flag : Bool) : Machine :=
  let post := upd (MappedCondition.Controls.loaded flag).mem 2 (.val (bword false))
  {MappedCondition.Controls.loaded flag with mem := upd post 5 w[99]}
def post (flag : Bool) : State C TargetCtx :=
  ConditionalAssignments.targetAfter (caller flag) tci flag tci .here tca tci


theorem initial (flag : Bool) : mapping.Related Rel (source flag).1 (caller flag).env := by
  intro τ i
  cases i with
  | here => rfl
  | there i => cases i with
    | here => rfl
    | there i => cases i with
      | here => rfl
      | there i => nomatch i

theorem entry (flag : Bool) : Sim C 1 0 (Frag.init TargetCtx) (caller flag) (machine flag) := by
  apply SimL.congrMem (Sim.pushVal (MappedCondition.Controls.represented flag)
    (p := .bool) (v := false) (w := .val (bword false)) rfl)
  intro level low high
  apply upd_other
  change level ≠ 5
  change level < 3 at high
  omega

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+4) 0 none (R := []) (M := false)
      (ConditionalStatement.statement (k := ⟨false,false⟩) sci sca sci .here sca sci)
      (source flag).1).run (.nil,(source flag).2) =
      (.ok (Source.Out.normal (ConditionalAssignments.sourceAfter (source flag) sci flag sci .here sca sci).1),
        (.nil,(source flag).2)) ∧
    core.run (caller flag) = .ok ⟨post flag,List.prefix_refl _⟩ ∧
    mapping.Related Rel (ConditionalAssignments.sourceAfter (source flag) sci flag sci .here sca sci).1
      (post flag).env ∧
    (post flag).glob = (caller flag).glob ∧
    StmtOut C 1 0 (Frag.init TargetCtx) false false false
      (core.run (caller flag)) (run emitted (machine flag)) (machine flag) := by
  exact correct (G0 pipeline) F0 fuel 0 none (returns := []) (M := false) (k := ⟨false,false⟩)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h)
    sci sca sci .here sca sci tci tca tci .here tca tci rfl rfl rfl rfl rfl rfl
    (entry flag) rfl (by decide)

theorem typed_run (flag : Bool) : core.run (caller flag) = .ok ⟨post flag,List.prefix_refl _⟩ :=
  (joined .legacy 0 flag).2.1

theorem checked (flag : Bool) :
    StmtOut C 1 0 (Frag.init TargetCtx) false false false
      (core.run (caller flag)) (run emitted (machine flag)) (machine flag) :=
  (joined .legacy 0 flag).2.2.2.2

theorem no_canary_store : codeStoresCell 5 emitted = false := by decide

theorem observed (flag : Bool) :
    ∃ final, run emitted (machine flag) = .ok final 0 ∧
      final.mem 0 = .val (bword flag) ∧ final.mem 1 = .val (bword false) ∧
      final.mem 2 = .val (bword false) ∧ final.mem 5 = w[99] ∧ final.stack = [w[77]] := by
  rcases checked flag with ⟨o,final,sourceRun,targetRun,stack,_,repr⟩ |
    ⟨sourceRun,_⟩ | ⟨assertion,_⟩ | ⟨payment,_⟩ | ⟨sourceRun,_⟩
  · rw [typed_run flag] at sourceRun
    cases sourceRun
    refine ⟨final,targetRun,?_,?_,?_,?_,stack⟩
    · cases flag <;> exact repr.vals (.there (.there .here))
    · cases flag <;> exact repr.vals (.there .here)
    · cases flag <;> exact repr.vals .here
    · exact exec_mem no_canary_store targetRun
  · rw [typed_run flag] at sourceRun
    cases sourceRun
  · cases assertion
  · cases payment
  · rw [typed_run flag] at sourceRun
    cases sourceRun

def badCore : Prog C TargetCtx TargetCtx := ConditionalStatement.code tci tci tci .here tca tci
def badEmitted : List Instr := emit (C := C) 0 tci tci tci .here tca tci

theorem checked_bad : StmtOut C 1 0 (Frag.init TargetCtx) false false false
    (badCore.run (caller true)) (run badEmitted (machine true)) (machine true) := by
  exact prog_sim badCore (entry true) rfl (by decide)

theorem typed_bad : badCore.run (caller true) =
    .ok ⟨ConditionalAssignments.targetAfter (caller true) tci false tci .here tca tci,List.prefix_refl _⟩ :=
  ConditionalStatement.target_run (caller true) tci tci false tci .here tca tci rfl

theorem observed_bad : ∃ final, run badEmitted (machine true) = .ok final 0 ∧
    final.mem 0 = .val (bword false) := by
  rcases checked_bad with ⟨o,final,sourceRun,targetRun,_,_,repr⟩ |
    ⟨sourceRun,_⟩ | ⟨assertion,_⟩ | ⟨payment,_⟩ | ⟨sourceRun,_⟩
  · rw [typed_bad] at sourceRun
    cases sourceRun
    exact ⟨final,targetRun,repr.vals (.there (.there .here))⟩
  · rw [typed_bad] at sourceRun
    cases sourceRun
  · cases assertion
  · cases payment
  · rw [typed_bad] at sourceRun
    cases sourceRun

theorem stale_condition_refused : run badEmitted (machine true) ≠ run emitted (machine true) := by
  rcases observed true with ⟨good,goodRun,goodValue,_⟩
  rcases observed_bad with ⟨bad,badRun,badValue⟩
  intro same
  rw [badRun,goodRun] at same
  have wordSame : bad.mem 0 = good.mem 0 := congrArg (fun out : Solidity.Evm.Out =>
    match out with | .ok post _ => post.mem 0 | _ => w[0]) same
  rw [badValue,goodValue] at wordSame
  have different : Word.val (bword false) ≠ Word.val (bword true) := by decide
  exact different wordSame

theorem source_zero (pipeline : Roadmap.Pipeline) (flag : Bool) :
    Source.execS (G0 pipeline) F0 0 0 none (R := []) (M := false)
      (ConditionalStatement.statement (k := ⟨false,false⟩) sci sca sci .here sca sci)
      (source flag).1 = Source.EM.halt .timeout := by rfl

end Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls
