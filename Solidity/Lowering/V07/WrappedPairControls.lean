import Solidity.Lowering.V07.WrappedAssignmentPair
import Solidity.Lowering.V07.UnsignedNarrowingControls

namespace Solidity.Lowering.V07.WrappedPairControls
open Source.SemanticsExamples
open UnsignedNarrowing
open WrappedAssignmentPair
abbrev U := UnsignedNarrowingControls.source
abbrev T := UnsignedNarrowingControls.target
abbrev SrcCtx := UnsignedNarrowingControls.SrcCtx
abbrev TgtCtx := UnsignedNarrowingControls.TgtCtx

def expression : Source.RExpr MixedAssignmentControls.E SrcCtx (.int .u8) :=
  .binary .sub (.assign (.local .here) (.local .here))
    (.assign (.local .here) (.local (.there .here)))
def result (p : Roadmap.Pipeline) : Int := if p = .legacy then 0 else 255

theorem result_range (p : Roadmap.Pipeline) :
    Source.IntTy.u8.lo ≤ result p ∧ result p ≤ Source.IntTy.u8.hi := by
  cases p <;> decide

def sourceFinal : Source.EMState MixedAssignmentControls.E SrcCtx :=
  (U.1.set .here (.int 1 (by decide)),U.2)
def targetFinal : State MixedAssignmentControls.C TgtCtx :=
  T.setLocal .here (integerValue .u8 1 (by decide))

theorem actual_runs (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4) expression).run U =
      (.ok (.val (.int (result p) (result_range p))),sourceFinal) ∧
    (operand p 8 .here .here (.there .here)).run T =
      .ok (⟨targetFinal,List.prefix_refl _⟩,.prim (integerValue .u8 (result p) (result_range p))) ∧
    IntegerLocalFamily .u8 UnsignedNarrowingControls.si UnsignedNarrowingControls.ti
      sourceFinal.1 targetFinal.env := by
  have h := transport (MixedAssignmentControls.globals p) F0 fuel U T 8 (by decide)
    UnsignedNarrowingControls.si UnsignedNarrowingControls.ti UnsignedNarrowingControls.initial
    (false,false) (false,true) (true,false) 0 1 (by decide) (by decide) rfl rfl
  cases p <;> exact ⟨h.1,h.2.1,h.2.2.2⟩

/-- Every approved width and both pipelines; no public length or width cutoff. -/
theorem all_width_runs (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := false} (fuel+4)
      (.binary .sub (.assign (.local .here) (.local .here))
        (.assign (.local .here) (.local (.there .here))))).run
          (UnsignedNarrowingControls.pureSource bits valid) =
      (.ok (.val (Source.intWrap (ty bits valid) (delta p false 0 1))),
        sourcePost p (UnsignedNarrowingControls.pureSource bits valid) bits valid
          .here .here (.there .here) 0 1 (integer_zero_range _) (UnsignedNarrowingControls.one_range bits valid)) ∧
    (operand p bits .here .here (.there .here)).run (UnsignedNarrowingControls.pureTarget bits valid) =
      .ok (⟨targetPost p (UnsignedNarrowingControls.pureTarget bits valid) bits valid
        .here .here (.there .here) 0 1 (integer_zero_range _) (UnsignedNarrowingControls.one_range bits valid),
        by cases p <;> exact List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap (delta p false 0 1))
          ((ty bits valid).wrap_mem (delta p false 0 1)))) :=
  ⟨source_run (G0 p) F0 fuel _ bits valid .here .here (.there .here) 0 1
      (integer_zero_range _) (UnsignedNarrowingControls.one_range bits valid) rfl rfl,
   operand_run p _ bits valid .here .here (.there .here) 0 1
      (integer_zero_range _) (UnsignedNarrowingControls.one_range bits valid) rfl rfl⟩

theorem actual_pair (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalPair (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+3)
      (.assign (.local .here) (.local .here))
      (.assign (.local .here) (.local (.there .here)))).run U =
      (.ok (.val (.int (if p = .legacy then 1 else 0) (by cases p <;> decide)),
        .val (.int 1 (by decide))),sourceFinal) := by
  have h := source_assign_assign_pair_all_aliases (MixedAssignmentControls.globals p)
    {F0 with checked := false} fuel U .here .here (.there .here)
    (.int 0 (by decide)) (.int 1 (by decide)) rfl rfl
  cases p <;> exact h

theorem actual_prefix (p : Roadmap.Pipeline) :
    (assignAssignPrefix p .here .here (.there .here)).run T =
      .ok (⟨(targetFinal.push (integerValue .u8 (if p = .legacy then 1 else 0) (by cases p <;> decide))).push
        (integerValue .u8 1 (by decide)),List.prefix_refl _⟩) := by
  have h := assign_assign_prefix_all_aliases (p := .uint) p T .here .here (.there .here)
    (integerValue .u8 0 (by decide)) (integerValue .u8 1 (by decide)) rfl rfl
  cases p <;> exact h

theorem mixed_frames :
    sourceFinal.2 = U.2 ∧
    sourceFinal.1.get (.there (.there .here)) = .memRef rfl 0 ∧
    sourceFinal.1.get (.there (.there (.there .here))) = .storRef rfl MixedAssignmentControls.path ∧
    targetFinal.glob = T.glob ∧
    (∃ r : HRef targetFinal.H bytesR, TEnv.get (.there (.there .here)) targetFinal.env = some r ∧
      targetFinal.heap.len r .dyn = 2) ∧
    TEnv.get (.there (.there (.there .here))) targetFinal.env = some MixedAssignmentControls.storageRef :=
  ⟨rfl,rfl,rfl,rfl,MixedAssignmentControls.live_memory,rfl⟩

theorem fresh_context (p : Roadmap.Pipeline) :
    ((operand p 8 .here .here (.there .here)).wk (Thin.drop (t := .val .bool) .refl)).run
      (T.lift (Thin.drop .refl) (true,T.env)) =
      liftedT₂ (Thin.drop (t := .val .bool) .refl) (true,T.env)
        (.ok ((⟨targetFinal,List.prefix_refl _⟩ : Out MixedAssignmentControls.C T.H TgtCtx),
          SVal.prim (integerValue .u8 (result p) (result_range p)))) := by
  have h := extension p T 8 (by decide) .here .here (.there .here) 0 1
    (by decide) (by decide) rfl rfl (Thin.drop (t := .val .bool) .refl) (true,T.env)
  cases p <;> exact h

theorem uncaptured_read_wrong :
    (subValue 8 (.simple (.local .here)) (.simple (.local (.there .here)))).evalT targetFinal =
      .ok (integerValue .u8 0 (by decide)) ∧ result .viaIR = 255 := ⟨rfl,rfl⟩

theorem stale_initial_read_wrong :
    (subValue 8 (.simple (.local .here)) (.simple (.local (.there .here)))).evalT T =
      .ok (integerValue .u8 255 (by decide)) ∧ result .legacy = 0 := ⟨rfl,rfl⟩

theorem reversed_operands_wrong :
    (subValue 8 (.simple (.local (.there .here))) (.simple (.local .here))).evalT T =
      .ok (integerValue .u8 1 (by decide)) ∧ result .viaIR = 255 := ⟨rfl,rfl⟩

theorem pipeline_choice_observable : result .legacy ≠ result .viaIR := by decide

theorem repeated_aliases :
    IntValueRel .u8 (sourceFinal.1.get (UnsignedNarrowingControls.si (false,false)))
      (TEnv.get (UnsignedNarrowingControls.ti (false,true)) targetFinal.env) :=
  (actual_runs .viaIR 0).2.2.values (false,false)

theorem equal_content_distinct_identity :
    TEnv.get .here targetFinal.env = TEnv.get (.there .here) targetFinal.env ∧
    (.here : Idx TgtCtx (.val .uint)).toNat ≠ (.there .here : Idx TgtCtx (.val .uint)).toNat :=
  ⟨rfl,by decide⟩

def rhsSourcePost (p : Roadmap.Pipeline) :=
  if p = .legacy then sourceFinal else UnsignedNarrowingControls.sourcePost
def rhsTargetPost (p : Roadmap.Pipeline) :=
  if p = .legacy then targetFinal else UnsignedNarrowingControls.targetPost

theorem rhs_alias_runs (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      (.binary .sub (.assign (.local (.there .here)) (.local .here))
        (.assign (.local .here) (.local (.there .here))))).run U =
      (.ok (.val (.int 0 (by decide))),rhsSourcePost p) ∧
    (operand p 8 (.there .here) .here (.there .here)).run T =
      .ok (⟨rhsTargetPost p,by cases p <;> exact List.prefix_refl _⟩,
        .prim (integerValue .u8 0 (by decide))) ∧
    IntegerLocalFamily .u8 UnsignedNarrowingControls.si UnsignedNarrowingControls.ti
      (rhsSourcePost p).1 (rhsTargetPost p).env := by
  have h := transport (MixedAssignmentControls.globals p) F0 fuel U T 8 (by decide)
    UnsignedNarrowingControls.si UnsignedNarrowingControls.ti UnsignedNarrowingControls.initial
    (true,false) (false,true) (true,true) 0 1 (by decide) (by decide) rfl rfl
  cases p <;> exact ⟨h.1,h.2.1,h.2.2.2⟩

theorem all_same_runs (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      (.binary .sub (.assign (.local .here) (.local .here))
        (.assign (.local .here) (.local .here)))).run U =
      (.ok (.val (.int 0 (by decide))),U) ∧
    (operand p 8 .here .here .here).run T =
      .ok (⟨T,List.prefix_refl _⟩,.prim (integerValue .u8 0 (by decide))) := by
  have h := transport (MixedAssignmentControls.globals p) F0 fuel U T 8 (by decide)
    UnsignedNarrowingControls.si UnsignedNarrowingControls.ti UnsignedNarrowingControls.initial
    (false,false) (false,true) (false,true) 0 0 (by decide) (by decide) rfl rfl
  cases p <;> exact ⟨h.1,h.2.1⟩

theorem rhs_initial_formula_wrong :
    AssignmentControls.observed ((operand .viaIR 8 (.there .here) .here (.there .here)).run T) = some 0 ∧
    ((Source.IntTy.u8).wrap (0-1)) = 255 := by
  rw [(rhs_alias_runs .viaIR 0).2.1]
  exact ⟨rfl,rfl⟩

abbrev TripleSrcCtx : Source.RCtx := .int .u8 :: SrcCtx
abbrev TripleTgtCtx : Ctx := .val .uint :: TgtCtx
abbrev TripleKeys := Option UnsignedNarrowingControls.Keys

def tripleSource : Source.EMState MixedAssignmentControls.E TripleSrcCtx :=
  (.cons (.int 17 (by decide)) U.1,U.2)
def tripleTarget : State MixedAssignmentControls.C TripleTgtCtx :=
  T.push (integerValue .u8 17 (by decide))
def tsi : TripleKeys → Source.Idx TripleSrcCtx (.int .u8)
  | none => .here
  | some k => .there (UnsignedNarrowingControls.si k)
def tti : TripleKeys → Idx TripleTgtCtx (.val .uint)
  | none => .here
  | some k => .there (UnsignedNarrowingControls.ti k)

theorem triple_initial : IntegerLocalFamily .u8 tsi tti tripleSource.1 tripleTarget.env := by
  constructor
  · intro k; cases k with
    | none => rfl
    | some k => exact UnsignedNarrowingControls.initial.values k
  · intro k l; cases k with
    | none => cases l with
      | none => decide
      | some k => rcases k with ⟨a,b⟩; cases a <;> cases b <;> decide
    | some k => cases l with
      | none => rcases k with ⟨a,b⟩; cases a <;> cases b <;> decide
      | some l =>
        constructor
        · intro h
          exact congrArg Nat.succ ((UnsignedNarrowingControls.initial.aliases k l).mp (Nat.succ.inj h))
        · intro h
          exact congrArg Nat.succ ((UnsignedNarrowingControls.initial.aliases k l).mpr (Nat.succ.inj h))

def tripleSourceFinal (p : Roadmap.Pipeline) :=
  sourcePost p tripleSource 8 (by decide) .here (.there .here) (.there (.there .here))
    0 1 (by decide) (by decide)
def tripleTargetFinal (p : Roadmap.Pipeline) :=
  targetPost p tripleTarget 8 (by decide) .here (.there .here) (.there (.there .here))
    0 1 (by decide) (by decide)
def tripleExpression : Source.RExpr MixedAssignmentControls.E TripleSrcCtx (.int .u8) :=
  .binary .sub (.assign (.local .here) (.local (.there .here)))
    (.assign (.local (.there .here)) (.local (.there (.there .here))))

theorem three_distinct_runs (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      tripleExpression).run tripleSource =
      (.ok (.val (.int (result p) (result_range p))),tripleSourceFinal p) ∧
    (operand p 8 .here (.there .here) (.there (.there .here))).run tripleTarget =
      .ok (⟨tripleTargetFinal p,by cases p <;> exact List.prefix_refl _⟩,
        .prim (integerValue .u8 (result p) (result_range p))) ∧
    IntegerLocalFamily .u8 tsi tti (tripleSourceFinal p).1 (tripleTargetFinal p).env := by
  have h := transport (MixedAssignmentControls.globals p) F0 fuel tripleSource tripleTarget
    8 (by decide) tsi tti triple_initial none (some (false,false)) (some (true,false))
    0 1 (by decide) (by decide) rfl rfl
  cases p <;> exact ⟨h.1,h.2.1,h.2.2.2⟩

theorem triple_caller_and_live_frames (p : Roadmap.Pipeline) :
    ((tripleSourceFinal p).1.get .here).key = some (if p = .legacy then 1 else 0) ∧
    ((tripleSourceFinal p).1.get (.there .here)).key = some 1 ∧
    ((tripleSourceFinal p).1.get (.there (.there .here))).key = some 1 ∧
    (tripleSourceFinal p).2 = tripleSource.2 ∧
    (tripleTargetFinal p).glob = tripleTarget.glob ∧
    (∃ r : HRef (tripleTargetFinal p).H bytesR,
      TEnv.get (.there (.there (.there .here))) (tripleTargetFinal p).env = some r ∧
      (tripleTargetFinal p).heap.len r .dyn = 2) ∧
    TEnv.get (.there (.there (.there (.there .here)))) (tripleTargetFinal p).env =
      some MixedAssignmentControls.storageRef := by
  cases p <;> exact ⟨rfl,rfl,rfl,rfl,rfl,MixedAssignmentControls.live_memory,rfl⟩

end Solidity.Lowering.V07.WrappedPairControls
