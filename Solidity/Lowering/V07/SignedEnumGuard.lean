import Solidity.Lowering.V07.EnumGuard
import Solidity.Lowering.V07.SignedWidthCasts

/-! Signed enum checks reject negative inputs before unsigned membership checks.
The capacity bound is representation, not Source admission. -/
namespace Solidity.Lowering.V07.SignedEnumGuard
open WordCasts (signed)

theorem uint_range (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi) (nonnegative : 0 ≤ x) :
    Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi := by
  change 0 ≤ x ∧ x ≤ Source.IntTy.u256.hi
  exact ⟨nonnegative,Int.le_trans hx.2 (by decide)⟩

def condition {C : Contract} {Γ : Ctx} (i : Idx Γ (.val .int)) : Val C Γ .bool :=
  .binop .le rfl rfl (.simple (.lit (0 : Int) (by decide))) (.simple (.local i))
def guard {C : Contract} {Γ : Ctx} (i : Idx Γ (.val .int)) : Stmt C Γ Γ :=
  panicStmt 0x21 (condition i)

theorem condition_run {C : Contract} {Γ : Ctx} (target : State C Γ) (i : Idx Γ (.val .int))
    (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : TEnv.get i target.env = integerValue signed x hx) :
    (condition i).evalT target = .ok (decide (0 ≤ x)) := by
  change TRes.ofOpt (BinOp.evalT .le (p := .int) rfl
    (⟨0,by decide⟩ : PrimTy.int.Denote) (TEnv.get i target.env)) = _
  rw [read]
  rfl

theorem guard_success {C : Contract} {Γ : Ctx} (target : State C Γ) (i : Idx Γ (.val .int))
    (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : TEnv.get i target.env = integerValue signed x hx) (nonnegative : 0 ≤ x) :
    (guard i).run target = .ok (⟨target,List.prefix_refl _⟩ : Out C target.H Γ) := by
  have test := condition_run target i x hx read
  simp only [nonnegative,decide_true] at test
  change TRun.ite (condition i) _ _ _ _ target = _
  simp only [TRun.ite,test,boolT,TRun.nil]
  rfl

theorem guard_negative {C : Contract} {Γ : Ctx} (target : State C Γ) (i : Idx Γ (.val .int))
    (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : TEnv.get i target.env = integerValue signed x hx) (negative : ¬ 0 ≤ x) :
    (guard i).run target = .error (THalt.ofData (Source.panicData .enumConv)) := by
  have test := condition_run target i x hx read
  simp only [negative,decide_false] at test
  change TRun.ite (condition i) _ _ _ _ target = _
  have literal := Backend.Failure.revert_bytes_intrinsic target (Semantics.encodePanic 0x21)
  simp only [TRun.ite,test,boolT,ok_bind,Bool.false_eq_true,if_false,TRun.seq,literal]
  rw [V08.panicData_transport .enumConv]
  rfl

theorem cast_run {C : Contract} {Γ : Ctx} (target : State C Γ) (i : Idx Γ (.val .int))
    (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : TEnv.get i target.env = integerValue signed x hx) (nonnegative : 0 ≤ x) :
    (Val.unop .toUint rfl rfl (.simple (.local i))).evalT target =
      .ok (integerValue .u256 x (uint_range x hx nonnegative)) := by
  have cast := WordCasts.to_uint_run target (.simple (.local i)) x hx (congrArg Except.ok read)
  have wrapped : Source.IntTy.u256.wrap x = x := UnsignedNarrowing.wrap_of_range 256 (by decide) x (uint_range x hx nonnegative)
  simpa only [wrapped] using cast

def code {C : Contract} {Γ : Ctx} (count : Nat) (capacity : count ≤ 2^256)
    (i r : Idx Γ (.val .int)) : Prog C Γ (.val .uint :: Γ) :=
  .cons (.assignLocal i (.simple (.local r)))
    (.cons (guard i)
      (.cons (.declLocal .uint (.user "v07_signed_enum") (some (.unop .toUint rfl rfl (.simple (.local i)))))
        (.cons (EnumGuard.guard count capacity .here) .nil)))
def operand {C : Contract} {Γ : Ctx} (count : Nat) (capacity : count ≤ 2^256)
    (i r : Idx Γ (.val .int)) : DeferredSource.Operand C Γ (.prim .uint) :=
  ⟨_,code count capacity i r,.val (.simple (.local .here))⟩

theorem assignment_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (i r : Idx Γ (.val .int)) (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : TEnv.get r target.env = integerValue signed x hx) :
    (Stmt.assignLocal i (.simple (.local r))).run target =
      .ok (⟨target.setLocal i (integerValue signed x hx),List.prefix_refl _⟩ : Out C target.H Γ) := by
  change Except.ok (⟨target.setLocal i (TEnv.get r target.env),List.prefix_refl _⟩ : Out C target.H Γ) = _
  rw [read]

theorem capture_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (i : Idx Γ (.val .int)) (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : TEnv.get i target.env = integerValue signed x hx) (nonnegative : 0 ≤ x) :
    (Stmt.declLocal .uint (.user "v07_signed_enum")
      (some (.unop .toUint rfl rfl (.simple (.local i))))).run target =
      .ok (⟨target.push (integerValue .u256 x (uint_range x hx nonnegative)),List.prefix_refl _⟩ :
        Out C target.H (.val .uint :: Γ)) := by
  change (do
    let v ← (Val.unop .toUint rfl rfl (.simple (.local i))).evalT target
    pure (⟨target.push v,List.prefix_refl _⟩ : Out C target.H (.val .uint :: Γ))) = _
  rw [cast_run target i x hx read nonnegative]
  rfl

theorem code_success {C : Contract} {Γ : Ctx} (target : State C Γ)
    (count : Nat) (capacity : count ≤ 2^256) (i r : Idx Γ (.val .int))
    (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : TEnv.get r target.env = integerValue signed x hx) (valid : 0 ≤ x ∧ x.toNat < count) :
    (code count capacity i r).run target =
      .ok (⟨(target.setLocal i (integerValue signed x hx)).push
        (integerValue .u256 x (uint_range x hx valid.1)),List.prefix_refl _⟩ : Out C target.H (.val .uint :: Γ)) := by
  have assigned := assignment_run target i r x hx read
  have checked := guard_success (target.setLocal i (integerValue signed x hx)) i x hx
    (TEnv.get_set i _ target.env) valid.1
  have captured := capture_run (target.setLocal i (integerValue signed x hx)) i x hx
    (TEnv.get_set i _ target.env) valid.1
  have member := EnumGuard.guard_success ((target.setLocal i (integerValue signed x hx)).push
    (integerValue .u256 x (uint_range x hx valid.1))) count capacity .here (integerValue .u256 x (uint_range x hx valid.1)) rfl valid.2
  unfold code
  rw [Prog.run_cons_ok assigned,Prog.run_cons_ok checked,Prog.run_cons_ok captured,Prog.run_cons_ok member,Prog.run_nil]
  rfl

theorem code_failure {C : Contract} {Γ : Ctx} (target : State C Γ)
    (count : Nat) (capacity : count ≤ 2^256) (i r : Idx Γ (.val .int))
    (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : TEnv.get r target.env = integerValue signed x hx) (invalid : ¬ (0 ≤ x ∧ x.toNat < count)) :
    (code count capacity i r).run target = .error (THalt.ofData (Source.panicData .enumConv)) := by
  have assigned := assignment_run target i r x hx read
  have tailFailed : (Prog.cons (guard i)
      (.cons (.declLocal .uint (.user "v07_signed_enum") (some (.unop .toUint rfl rfl (.simple (.local i)))))
        (.cons (EnumGuard.guard count capacity .here) .nil))).run
      (target.setLocal i (integerValue signed x hx)) = .error (THalt.ofData (Source.panicData .enumConv)) := by
    by_cases nonnegative : 0 ≤ x
    · have checked := guard_success (target.setLocal i (integerValue signed x hx)) i x hx
        (TEnv.get_set i _ target.env) nonnegative
      have captured := capture_run (target.setLocal i (integerValue signed x hx)) i x hx
        (TEnv.get_set i _ target.env) nonnegative
      have outside : ¬ x.toNat < count := by omega
      have rejected := EnumGuard.guard_failure ((target.setLocal i (integerValue signed x hx)).push
        (integerValue .u256 x (uint_range x hx nonnegative))) count capacity .here
        (integerValue .u256 x (uint_range x hx nonnegative)) rfl outside
      have lastFailed : (Prog.cons (EnumGuard.guard count capacity .here) .nil).run
          ((target.setLocal i (integerValue signed x hx)).push
            (integerValue .u256 x (uint_range x hx nonnegative))) =
          .error (THalt.ofData (Source.panicData .enumConv)) := by
        change TRun.seq (EnumGuard.guard count capacity .here).runR _ _ = _
        simp only [TRun.seq,show (EnumGuard.guard count capacity .here).runR _ = _ from rejected]
      rw [Prog.run_cons_ok checked,Prog.run_cons_ok captured,lastFailed]
      rfl
    · have rejected := guard_negative (target.setLocal i (integerValue signed x hx)) i x hx
        (TEnv.get_set i _ target.env) nonnegative
      change TRun.seq (guard i).runR _ _ = _
      simp only [TRun.seq,show (guard i).runR _ = _ from rejected]
  unfold code
  rw [Prog.run_cons_ok assigned,tailFailed]
  rfl

theorem operand_success {C : Contract} {Γ : Ctx} (target : State C Γ)
    (count : Nat) (capacity : count ≤ 2^256) (i r : Idx Γ (.val .int))
    (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : TEnv.get r target.env = integerValue signed x hx) (valid : 0 ≤ x ∧ x.toNat < count) :
    (operand count capacity i r).run target =
      .ok (⟨target.setLocal i (integerValue signed x hx),List.prefix_refl _⟩,
        .prim (integerValue .u256 x (uint_range x hx valid.1))) := by
  unfold operand DeferredSource.Operand.run
  rw [code_success target count capacity i r x hx read valid]
  rfl

theorem operand_failure {C : Contract} {Γ : Ctx} (target : State C Γ)
    (count : Nat) (capacity : count ≤ 2^256) (i r : Idx Γ (.val .int))
    (x : Int) (hx : signed.lo ≤ x ∧ x ≤ signed.hi)
    (read : TEnv.get r target.env = integerValue signed x hx) (invalid : ¬ (0 ≤ x ∧ x.toNat < count)) :
    (operand count capacity i r).run target = .error (THalt.ofData (Source.panicData .enumConv)) := by
  unfold operand DeferredSource.Operand.run
  rw [code_failure target count capacity i r x hx read invalid]
  rfl

/-- info: 'Solidity.Lowering.V07.SignedEnumGuard.uint_range' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumGuard.uint_range

/-- info: 'Solidity.Lowering.V07.SignedEnumGuard.condition_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumGuard.condition_run

/-- info: 'Solidity.Lowering.V07.SignedEnumGuard.guard_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumGuard.guard_success

/-- info: 'Solidity.Lowering.V07.SignedEnumGuard.guard_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumGuard.guard_negative

/-- info: 'Solidity.Lowering.V07.SignedEnumGuard.cast_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumGuard.cast_run

/-- info: 'Solidity.Lowering.V07.SignedEnumGuard.assignment_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumGuard.assignment_run

/-- info: 'Solidity.Lowering.V07.SignedEnumGuard.capture_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumGuard.capture_run

/-- info: 'Solidity.Lowering.V07.SignedEnumGuard.code_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumGuard.code_success

/-- info: 'Solidity.Lowering.V07.SignedEnumGuard.code_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumGuard.code_failure

/-- info: 'Solidity.Lowering.V07.SignedEnumGuard.operand_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumGuard.operand_success

/-- info: 'Solidity.Lowering.V07.SignedEnumGuard.operand_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumGuard.operand_failure

end Solidity.Lowering.V07.SignedEnumGuard
