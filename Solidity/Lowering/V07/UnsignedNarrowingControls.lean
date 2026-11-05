import Solidity.Lowering.V07.UnsignedNarrowing
import Solidity.Lowering.V07.AliasRhsSubtraction
import Solidity.Lowering.V07.MixedAssignmentControls

namespace Solidity.Lowering.V07.UnsignedNarrowingControls
open Source.SemanticsExamples
namespace U
abbrev ty := UnsignedNarrowing.ty
end U

theorem one_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (U.ty bits valid).lo ≤ 1 ∧ 1 ≤ (U.ty bits valid).hi := by
  have hb : 1 ≤ bits := by have := valid.2.1; omega
  have hp : 2 ≤ 2 ^ bits := Source.two_pow_le hb
  simp only [U.ty,UnsignedNarrowing.ty,Source.IntTy.lo,Source.IntTy.hi,Bool.false_eq_true,if_false]
  constructor <;> omega

def pureSource (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    Source.EMState E0 [.int (U.ty bits valid),.int (U.ty bits valid)] :=
  (.cons (.int 0 (integer_zero_range _)) (.cons (.int 1 (one_range bits valid)) .nil),s0)

def pureTarget (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    State (default : Contract) [.val .uint,.val .uint] :=
  ((State.init default).push (integerValue (U.ty bits valid) 1 (one_range bits valid))).push
    (integerValue (U.ty bits valid) 0 (integer_zero_range _))

theorem all_width_pure_runs (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := false} (fuel+3)
      (.binary .sub (.local .here) (.local (.there .here)))).run (pureSource bits valid) =
      (.ok (.val (Source.intWrap (U.ty bits valid) (-1))),pureSource bits valid) ∧
    (UnsignedNarrowing.subValue bits (.simple (.local .here)) (.simple (.local (.there .here)))).evalT
      (pureTarget bits valid) =
      .ok (integerValue (U.ty bits valid) ((U.ty bits valid).wrap (-1)) ((U.ty bits valid).wrap_mem (-1))) :=
  ⟨UnsignedNarrowing.source_locals_run (G0 p) F0 fuel (pureSource bits valid) bits valid
    .here (.there .here) 0 1 (integer_zero_range _) (one_range bits valid) rfl rfl,
   UnsignedNarrowing.sub_value_run (pureTarget bits valid) bits valid _ _ 0 1
    (integer_zero_range _) (one_range bits valid) rfl rfl⟩

abbrev SrcCtx : Source.RCtx := [.int .u8,.int .u8,.bytes .memory,.bytes .storage]
abbrev TgtCtx : Ctx := [.val .uint,.val .uint,.mem bytesR,.alias bytesR]
abbrev Keys := Bool × Bool

def si (k : Keys) : Source.Idx SrcCtx (.int (U.ty 8 (by decide))) := if k.1 then .there .here else .here
def ti (k : Keys) : Idx TgtCtx (.val .uint) := if k.1 then .there .here else .here

def source : Source.EMState MixedAssignmentControls.E SrcCtx :=
  (((MixedAssignmentControls.source.1.set .here (.int 0 (by decide))).set
    (.there .here) (.int 1 (by decide))),MixedAssignmentControls.source.2)
def target : State MixedAssignmentControls.C TgtCtx :=
  (MixedAssignmentControls.target.setLocal .here (integerValue .u8 0 (by decide))).setLocal
    (.there .here) (integerValue .u8 1 (by decide))
def sourcePost : Source.EMState MixedAssignmentControls.E SrcCtx :=
  (source.1.set (.there .here) (.int 0 (by decide)),source.2)
def targetPost : State MixedAssignmentControls.C TgtCtx :=
  target.setLocal (.there .here) (integerValue .u8 0 (by decide))
def delta (p : Roadmap.Pipeline) : Int := if p = .legacy then 255 else 0

theorem initial : IntegerLocalFamily (U.ty 8 (by decide)) si ti source.1 target.env := by
  constructor
  · intro k; rcases k with ⟨a,b⟩; cases a <;> cases b <;> rfl
  · intro k l; rcases k with ⟨a,b⟩; rcases l with ⟨c,d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem delta_range (p : Roadmap.Pipeline) : Source.IntTy.u8.lo ≤ delta p ∧ delta p ≤ Source.IntTy.u8.hi := by
  cases p <;> decide

theorem actual_effect_runs (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      (.binary .sub (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source =
      (.ok (.val (.int (delta p) (delta_range p))),sourcePost) ∧
    (UnsignedNarrowing.assignReadOperand p 8 (.there .here) .here).run target =
      .ok (⟨targetPost,List.prefix_refl _⟩,.prim (integerValue .u8 (delta p) (delta_range p))) ∧
    IntegerLocalFamily (U.ty 8 (by decide)) si ti sourcePost.1 targetPost.env := by
  have h := UnsignedNarrowing.assignment_transport (MixedAssignmentControls.globals p) F0 fuel
    source target 8 (by decide) si ti initial (true,false) (false,false) 0 1
    (by decide) (by decide) rfl rfl
  cases p <;> exact ⟨h.1,h.2.1,h.2.2.2⟩

theorem mixed_frames :
    sourcePost.2 = source.2 ∧
    sourcePost.1.get (.there (.there .here)) = .memRef rfl 0 ∧
    sourcePost.1.get (.there (.there (.there .here))) = .storRef rfl MixedAssignmentControls.path ∧
    targetPost.glob = target.glob ∧
    (∃ r : HRef targetPost.H bytesR, TEnv.get (.there (.there .here)) targetPost.env = some r ∧
      targetPost.heap.len r .dyn = 2) ∧
    TEnv.get (.there (.there (.there .here))) targetPost.env = some MixedAssignmentControls.storageRef :=
  ⟨rfl,rfl,rfl,rfl,MixedAssignmentControls.live_memory,rfl⟩

theorem fresh_boolean_context (p : Roadmap.Pipeline) :
    ((UnsignedNarrowing.assignReadOperand p 8 (.there .here) .here).wk
      (Thin.drop (t := .val .bool) .refl)).run (target.lift (Thin.drop .refl) (true,target.env)) =
      liftedT₂ (Thin.drop (t := .val .bool) .refl) (true,target.env)
        (.ok ((⟨targetPost,List.prefix_refl _⟩ : Out MixedAssignmentControls.C target.H TgtCtx),
          SVal.prim (integerValue .u8 (delta p) (delta_range p)))) := by
  have h := UnsignedNarrowing.assignment_extension p target 8 (by decide) (.there .here) .here
    0 1 (by decide) (by decide) rfl rfl (Thin.drop (t := .val .bool) .refl) (true,target.env)
  cases p <;> exact h

theorem bare_checked_sub_wrong :
    BinOp.evalT .sub (p := .uint) rfl (integerValue .u8 0 (by decide))
      (integerValue .u8 1 (by decide)) = none ∧ delta .legacy = 255 := by
  exact ⟨rfl,rfl⟩

theorem word_wrap_minus_one : Source.IntTy.u256.wrap (-1) = Semantics.uintBound-1 := by
  have hp : (0 : Int) < Semantics.uintBound := Int.ofNat_lt.mpr (Source.two_pow_pos 256)
  change (-1 : Int) % Semantics.uintBound = Semantics.uintBound-1
  simpa only [Int.zero_emod,Int.sub_zero] using Int.negSucc_emod 0 hp

theorem unmasked_word_wrong :
    PrimTy.num? (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap (-1))
      (Source.IntTy.u256.wrap_mem (-1))) ≠ some 255 := by
  rw [integer_observe,word_wrap_minus_one]
  have hp : (256 : Int) < Semantics.uintBound :=
    Int.ofNat_lt.mpr (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 8 < 256))
  intro h
  have he := Option.some.inj h
  omega

theorem word_width_branch {C : Contract} {Γ : Ctx} (a b : Val C Γ .uint) :
    UnsignedNarrowing.subValue 256 a b = .binop .subW rfl rfl a b := rfl

theorem reversed_operands_wrong :
    (UnsignedNarrowing.subValue 8 (.simple (.local (.there .here))) (.simple (.local .here))).evalT
      (pureTarget 8 (by decide)) = .ok (integerValue .u8 1 (by decide)) ∧
    (1 : Int) ≠ delta .legacy :=
  ⟨UnsignedNarrowing.sub_value_run (pureTarget 8 (by decide)) 8 (by decide) _ _ 1 0
    (one_range 8 (by decide)) (integer_zero_range _) rfl rfl,by decide⟩

theorem dropped_capture_wrong :
    (UnsignedNarrowing.subValue 8 (.simple (.local (.there .here)))
      (.simple (.local (.there .here)))).evalT targetPost = .ok (integerValue .u8 0 (by decide)) ∧
    (UnsignedNarrowing.assignReadOperand .legacy 8 (.there .here) .here).run target =
      .ok (⟨targetPost,List.prefix_refl _⟩,.prim (integerValue .u8 255 (by decide))) :=
  ⟨UnsignedNarrowing.sub_value_run targetPost 8 (by decide) _ _ 0 0
    (integer_zero_range _) (integer_zero_range _) rfl rfl,(actual_effect_runs .legacy 0).2.1⟩

theorem same_index (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      (.binary .sub (.assign (.local .here) (.local .here)) (.local .here))).run source =
      (.ok (.val (.int 0 (by decide))),source) ∧
    (UnsignedNarrowing.assignReadOperand p 8 .here .here).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim (integerValue .u8 0 (by decide))) := by
  have h := UnsignedNarrowing.assignment_transport (MixedAssignmentControls.globals p) F0 fuel
    source target 8 (by decide) si ti initial (false,false) (false,false) 0 0
    (by decide) (by decide) rfl rfl
  cases p <;> exact ⟨h.1,h.2.1⟩

theorem in_range_positive (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := false} (fuel+3)
      (.binary .sub (.local .here) (.local (.there .here)))).run ReadControls.source =
      (.ok (.val (.int 4 (by decide))),ReadControls.source) ∧
    (UnsignedNarrowing.subValue 8 (.simple (.local .here)) (.simple (.local (.there .here)))).evalT
      ReadControls.target = .ok (integerValue .u8 4 (by decide)) :=
  ⟨UnsignedNarrowing.source_locals_run (G0 p) F0 fuel ReadControls.source 8 (by decide)
    .here (.there .here) 7 3 (by decide) (by decide) rfl rfl,
   UnsignedNarrowing.sub_value_run ReadControls.target 8 (by decide) _ _ 7 3 (by decide) (by decide) rfl rfl⟩

theorem word_width_numeric_result :
    (Source.intWrap Source.IntTy.u256 (-1) : Source.Val E0.layout (.int .u256)).key =
      some (Semantics.uintBound-1) ∧
    PrimTy.num? (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap (-1))
      (Source.IntTy.u256.wrap_mem (-1))) = some (Semantics.uintBound-1) := by
  constructor
  · change some (Source.IntTy.u256.wrap (-1)) = _
    rw [word_wrap_minus_one]
  · rw [integer_observe,word_wrap_minus_one]

theorem equal_content_distinct_identity :
    TEnv.get .here targetPost.env = TEnv.get (.there .here) targetPost.env ∧
    (Idx.here : Idx TgtCtx (.val .uint)).toNat ≠ (Idx.there .here : Idx TgtCtx (.val .uint)).toNat :=
  ⟨rfl,by decide⟩

/-- Source-only mode discrimination, not a target panic-payload theorem. -/
theorem checked_underflow_control (p : Roadmap.Pipeline) :
    revertOf ((Source.evalE (G0 p) F0 3
      (.binary .sub (.local .here) (.local (.there .here)))).run (pureSource 8 (by decide))) =
      some (Source.panicData .arithmetic) := by
  cases p <;> decide

end Solidity.Lowering.V07.UnsignedNarrowingControls
