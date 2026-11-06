import Solidity.Lowering.G19.AssignmentBlocks
import Solidity.Lowering.G19.ConditionalReturnControls

namespace Solidity.Lowering.G19.AssignmentBlocks.Controls
open Solidity.Lowering.V07
open Source.SemanticsExamples (E0 G0 F0)
open Solidity.Backend.StructuredFlow.MappedCondition.Controls (C)
open Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls (SourceCtx TargetCtx)

def source (flag : Bool) : Source.EMState E0 (.int .u8 :: SourceCtx) :=
  (.cons (.int 77 (by decide)) (Solidity.Backend.StructuredFlow.ReturnTailCompiler.Controls.source flag).1,
    (Solidity.Backend.StructuredFlow.ReturnTailCompiler.Controls.source flag).2)
def target (flag : Bool) : State C (.val .uint :: TargetCtx) :=
  (Solidity.Backend.StructuredFlow.ReturnTailCompiler.Controls.caller flag).push
    (integerValue .u8 77 (by decide))
def mapping : ContextMap (.int .u8 :: SourceCtx) (.val .uint :: TargetCtx) :=
  Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls.mapping.cons (.int .u8) (.val .uint)
def Rel : (τ : Source.STy) → (u : LTy) → Source.Val E0.layout τ → u.TDenote C (target false).H → Prop
  | .bool,.val .bool,v,b => v = .bool b
  | .int t,.val .uint,v,n => t.signed = false ∧ v.key = PrimTy.num? n
  | _,_,_,_ => False

def index : Source.Idx (.int .u8 :: SourceCtx) .bool → Idx (.val .uint :: TargetCtx) (.val .bool)
  | .there .here => .there .here
  | .there (.there .here) => .there (.there .here)
  | .there (.there (.there .here)) => .there (.there (.there .here))

theorem maps : ∀ i, mapping.slot i = ⟨.val .bool,index i⟩ := by
  intro i
  cases i with
  | there i => cases i with
    | here => rfl
    | there i => cases i with
      | here => rfl
      | there i => cases i with
        | here => rfl
        | there i => nomatch i

theorem initial (flag : Bool) : mapping.Related Rel (source flag).1 (target flag).env := by
  intro τ i
  cases i with
  | here => exact ⟨rfl,rfl⟩
  | there i => cases i with
    | here => rfl
    | there i => cases i with
      | here => rfl
      | there i => cases i with
        | here => rfl
        | there i => nomatch i

def steps : List (Source.Idx (.int .u8 :: SourceCtx) .bool × Source.Idx (.int .u8 :: SourceCtx) .bool) :=
  [(.there .here,.there (.there (.there .here))),(.there (.there (.there .here)),.there .here)]

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag checked : Bool)
    (writes : List (Source.Idx (.int .u8 :: SourceCtx) .bool × Source.Idx (.int .u8 :: SourceCtx) .bool)) :
    (Source.execS (G0 pipeline) {F0 with checked := checked} (fuel+writes.length+4) 0 none
      (R := []) (M := false) (k := ⟨false,false⟩) (statement writes) (source flag).1).run (.nil,(source flag).2) =
      (.ok (Source.Out.normal (sourceAfter writes (source flag).1)),(.nil,(source flag).2)) ∧
    (code index writes).run (target flag) = .ok ⟨targetAfter index writes (target flag),List.prefix_refl _⟩ ∧
    mapping.Related Rel (sourceAfter writes (source flag).1) (targetAfter index writes (target flag)).env ∧
    (targetAfter index writes (target flag)).glob = (target flag).glob := by
  exact correct (G0 pipeline) {F0 with checked := checked} fuel 0 none (returns := []) (M := false)
    (k := ⟨false,false⟩) writes (source flag) (target flag) mapping Rel index maps (initial flag)

def observe (writes : List (Source.Idx (.int .u8 :: SourceCtx) .bool × Source.Idx (.int .u8 :: SourceCtx) .bool))
    (flag : Bool) : Option (List (Option Int)) :=
  match (code index writes).run (target flag) with
  | .ok out => some [PrimTy.num? (TEnv.get .here out.st.env),
      some (if TEnv.get (.there .here) out.st.env = true then 1 else 0),
      some (if TEnv.get (.there (.there .here)) out.st.env = true then 1 else 0),
      some (if TEnv.get (.there (.there (.there .here))) out.st.env = true then 1 else 0)]
  | _ => none

theorem observed (flag : Bool) : observe steps flag =
    some [some 77,some (if flag then 1 else 0),some (if flag then 0 else 1),some (if flag then 1 else 0)] := by
  unfold observe
  rw [target_run]
  cases flag <;> rfl

theorem repeated_observed (flag : Bool) : observe (steps ++ steps) flag = observe steps flag := by
  rw [observed]
  unfold observe
  rw [target_run]
  cases flag <;> rfl

theorem reversed_observed (flag : Bool) : observe steps.reverse flag =
    some [some 77,some (if flag then 0 else 1),some (if flag then 0 else 1),some (if flag then 0 else 1)] := by
  unfold observe
  rw [target_run]
  cases flag <;> rfl

theorem reverse_refused (flag : Bool) : observe steps.reverse flag ≠ observe steps flag := by
  rw [reversed_observed,observed]
  cases flag <;> decide

theorem untouched (flag : Bool) :
    (sourceAfter steps (source flag).1).get .here = .int 77 (by decide) ∧
    TEnv.get .here (targetAfter index steps (target flag)).env = integerValue .u8 77 (by decide) ∧
    (targetAfter index steps (target flag)).heap = (target flag).heap ∧
    (targetAfter index steps (target flag)).glob = (target flag).glob := by
  cases flag <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem self_alias_observed (flag : Bool) :
    observe [(.there .here,.there .here)] flag =
      some [some 77,some (if flag then 0 else 1),some (if flag then 0 else 1),some (if flag then 1 else 0)] := by
  unfold observe
  rw [target_run]
  cases flag <;> rfl

end Solidity.Lowering.G19.AssignmentBlocks.Controls
