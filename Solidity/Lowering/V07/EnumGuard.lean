import Solidity.Lowering.V07.EnumConversions
import Solidity.Lowering.V07.UnsignedQuotRemGuard

/-! Native enum membership checks over existing typed values/statements.
Capacity is the existing representation obligation, including zero/full word
capacity. Published panic bytes/emission are reused read-only. No frontend,
admission, session failure projection or transaction rollback is supplied. -/
namespace Solidity.Lowering.V07.EnumGuard

def condition {C : Contract} {Γ : Ctx} (count : Nat) (_capacity : count ≤ 2^256)
    (i : Idx Γ (.val .uint)) : Val C Γ .bool :=
  if small : count < 2^256 then
    Checked.cmpU .lt rfl rfl (.simple (.local i))
      (Checked.litU count (PrimTy.inRange_uint_of_lt small))
  else Checked.tt

def guard {C : Contract} {Γ : Ctx} (count : Nat) (capacity : count ≤ 2^256)
    (i : Idx Γ (.val .uint)) : Stmt C Γ Γ := panicStmt 0x21 (condition count capacity i)

theorem word_range (v : PrimTy.uint.Denote) : 0 ≤ v.val ∧ v.val < Semantics.uintBound := by
  simpa only [PrimTy.inRange,decide_eq_true_eq] using v.property

theorem condition_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (count : Nat) (capacity : count ≤ 2^256) (i : Idx Γ (.val .uint))
    (v : PrimTy.uint.Denote) (read : TEnv.get i target.env = v) :
    (condition count capacity i).evalT target = .ok (decide (v.val.toNat < count)) := by
  have vr := word_range v
  by_cases small : count < 2^256
  · simp only [condition,dif_pos small]
    change TRes.ofOpt (BinOp.evalT .lt rfl (TEnv.get i target.env)
      (⟨(count : Int),PrimTy.inRange_uint_of_lt small⟩ : PrimTy.uint.Denote)) = _
    rw [read]
    change Except.ok (decide (v.val < (count : Int))) = _
    by_cases below : v.val < (count : Int)
    · have natural : v.val.toNat < count := by omega
      simp only [below,natural,decide_true]
    · have natural : ¬ v.val.toNat < count := by omega
      simp only [below,natural,decide_false]
  · simp only [condition,dif_neg small]
    have full : count = 2^256 := by omega
    change 0 ≤ v.val ∧ v.val < ((2^256 : Nat) : Int) at vr
    have valid : v.val.toNat < count := by omega
    simp only [valid,decide_true]
    rfl

theorem guard_success {C : Contract} {Γ : Ctx} (target : State C Γ)
    (count : Nat) (capacity : count ≤ 2^256) (i : Idx Γ (.val .uint))
    (v : PrimTy.uint.Denote) (read : TEnv.get i target.env = v) (valid : v.val.toNat < count) :
    (guard count capacity i).run target = .ok (⟨target,List.prefix_refl _⟩ : Out C target.H Γ) := by
  have test := condition_run target count capacity i v read
  simp only [valid,decide_true] at test
  change TRun.ite (condition count capacity i) _ _ _ _ target = _
  simp only [TRun.ite,test,boolT,TRun.nil]
  rfl

theorem guard_failure {C : Contract} {Γ : Ctx} (target : State C Γ)
    (count : Nat) (capacity : count ≤ 2^256) (i : Idx Γ (.val .uint))
    (v : PrimTy.uint.Denote) (read : TEnv.get i target.env = v) (invalid : ¬ v.val.toNat < count) :
    (guard count capacity i).run target = .error (THalt.ofData (Source.panicData .enumConv)) := by
  have test := condition_run target count capacity i v read
  simp only [invalid,decide_false] at test
  change TRun.ite (condition count capacity i) _ _ _ _ target = _
  have literal := Backend.Failure.revert_bytes_intrinsic target (Semantics.encodePanic 0x21)
  simp only [TRun.ite,test,boolT,ok_bind,Bool.false_eq_true,if_false,TRun.seq,literal]
  rw [V08.panicData_transport .enumConv]
  rfl

def code {C : Contract} {Γ : Ctx} (count : Nat) (capacity : count ≤ 2^256)
    (i r : Idx Γ (.val .uint)) : Prog C Γ (.val .uint :: Γ) :=
  .cons (.assignLocal i (.simple (.local r)))
    (.cons (guard count capacity i)
      (.cons (.declLocal .uint (.user "v07_enum_result") (some (.simple (.local i)))) .nil))
def operand {C : Contract} {Γ : Ctx} (count : Nat) (capacity : count ≤ 2^256)
    (i r : Idx Γ (.val .uint)) : DeferredSource.Operand C Γ (.prim .uint) :=
  ⟨_,code count capacity i r,.val (.simple (.local .here))⟩

theorem assignment_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (i r : Idx Γ (.val .uint)) (v : PrimTy.uint.Denote) (read : TEnv.get r target.env = v) :
    (Stmt.assignLocal i (.simple (.local r))).run target =
      .ok (⟨target.setLocal i v,List.prefix_refl _⟩ : Out C target.H Γ) := by
  change Except.ok (⟨target.setLocal i (TEnv.get r target.env),List.prefix_refl _⟩ : Out C target.H Γ) = _
  rw [read]

theorem code_success {C : Contract} {Γ : Ctx} (target : State C Γ)
    (count : Nat) (capacity : count ≤ 2^256) (i r : Idx Γ (.val .uint))
    (v : PrimTy.uint.Denote) (read : TEnv.get r target.env = v) (valid : v.val.toNat < count) :
    (code count capacity i r).run target =
      .ok (⟨(target.setLocal i v).push v,List.prefix_refl _⟩ : Out C target.H (.val .uint :: Γ)) := by
  have assigned := assignment_run target i r v read
  have checked := guard_success (target.setLocal i v) count capacity i v (TEnv.get_set i v target.env) valid
  have captured : (Stmt.declLocal .uint (.user "v07_enum_result")
      (some (.simple (.local i)))).run (target.setLocal i v) =
      .ok (⟨(target.setLocal i v).push v,List.prefix_refl _⟩) := by
    change Except.ok (⟨(target.setLocal i v).push (TEnv.get i (TEnv.set i v target.env)),List.prefix_refl _⟩ : Out C target.H (.val .uint :: Γ)) = _
    rw [TEnv.get_set]
  unfold code
  rw [Prog.run_cons_ok assigned,Prog.run_cons_ok checked,Prog.run_cons_ok captured,Prog.run_nil]
  rfl

theorem code_failure {C : Contract} {Γ : Ctx} (target : State C Γ)
    (count : Nat) (capacity : count ≤ 2^256) (i r : Idx Γ (.val .uint))
    (v : PrimTy.uint.Denote) (read : TEnv.get r target.env = v) (invalid : ¬ v.val.toNat < count) :
    (code count capacity i r).run target = .error (THalt.ofData (Source.panicData .enumConv)) := by
  have assigned := assignment_run target i r v read
  have rejected := guard_failure (target.setLocal i v) count capacity i v (TEnv.get_set i v target.env) invalid
  have tailFailed : (Prog.cons (guard count capacity i)
      (.cons (.declLocal .uint (.user "v07_enum_result") (some (.simple (.local i)))) .nil)).run
      (target.setLocal i v) = .error (THalt.ofData (Source.panicData .enumConv)) := by
    change TRun.seq (guard count capacity i).runR _ (target.setLocal i v) = _
    simp only [TRun.seq,show (guard count capacity i).runR (target.setLocal i v) = _ from rejected]
  unfold code
  rw [Prog.run_cons_ok assigned,tailFailed]
  rfl

theorem operand_success {C : Contract} {Γ : Ctx} (target : State C Γ)
    (count : Nat) (capacity : count ≤ 2^256) (i r : Idx Γ (.val .uint))
    (v : PrimTy.uint.Denote) (read : TEnv.get r target.env = v) (valid : v.val.toNat < count) :
    (operand count capacity i r).run target =
      .ok (⟨target.setLocal i v,List.prefix_refl _⟩,.prim v) := by
  unfold operand DeferredSource.Operand.run
  rw [code_success target count capacity i r v read valid]
  rfl

theorem operand_failure {C : Contract} {Γ : Ctx} (target : State C Γ)
    (count : Nat) (capacity : count ≤ 2^256) (i r : Idx Γ (.val .uint))
    (v : PrimTy.uint.Denote) (read : TEnv.get r target.env = v) (invalid : ¬ v.val.toNat < count) :
    (operand count capacity i r).run target = .error (THalt.ofData (Source.panicData .enumConv)) := by
  unfold operand DeferredSource.Operand.run
  rw [code_failure target count capacity i r v read invalid]
  rfl

theorem transport_success {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (capacity : E.layout.enumSize d ≤ 2^256)
    (si : ι → Source.Idx srcΓ (.int .u256)) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily .u256 si ti source.1 target.env) (i r : ι) (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (valid : 0 ≤ x ∧ x.toNat < E.layout.enumSize d) (read : source.1.get (si r) = .int x hx) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .enum d)
      (.assign (.local (si i)) (.local (si r))) (EnumConversions.allowed_from E d))).run source =
      (.ok (.val (.enum ⟨x.toNat,valid.2⟩)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (operand (E.layout.enumSize d) capacity (ti i) (ti r)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue .u256 x hx),List.prefix_refl _⟩,.prim (integerValue .u256 x hx)) ∧
    EnumConversions.EnumRel d (.enum ⟨x.toNat,valid.2⟩ : Source.Val E.layout (.enum d)) (integerValue .u256 x hx) ∧
    IntegerLocalFamily .u256 si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue .u256 x hx) target.env) := by
  have raw := EnumConversions.from_assignment_transport G F fuel source target d si ti family i r x hx valid read
  exact ⟨raw.1,operand_success target _ capacity (ti i) (ti r) _ (family.read r x hx read) valid.2,raw.2.2⟩

/-- Exact local panic bytes and explicit reached assignment prefix. Native
errors expose no final state, so this is not a rollback/session projection. -/
theorem transport_failure {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (capacity : E.layout.enumSize d ≤ 2^256)
    (si : ι → Source.Idx srcΓ (.int .u256)) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily .u256 si ti source.1 target.env) (i r : ι) (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (invalid : ¬ (0 ≤ x ∧ x.toNat < E.layout.enumSize d)) (read : source.1.get (si r) = .int x hx) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .enum d)
      (.assign (.local (si i)) (.local (si r))) (EnumConversions.allowed_from E d))).run source =
      (.error (.revert (Source.panicData .enumConv)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (operand (E.layout.enumSize d) capacity (ti i) (ti r)).run target =
      .error (THalt.ofData (Source.panicData .enumConv)) ∧
    (Stmt.assignLocal (ti i) (.simple (.local (ti r)))).run target =
      .ok (⟨target.setLocal (ti i) (integerValue .u256 x hx),List.prefix_refl _⟩ : Out C target.H Γ) ∧
    Backend.Failure.HaltObserves (THalt.ofData (Source.panicData .enumConv)) (.revert (Source.panicData .enumConv)) := by
  have positive : 0 ≤ x := hx.1
  have outside : ¬ x.toNat < E.layout.enumSize d := by omega
  exact ⟨EnumConversions.source_from_refused_assignment G F fuel source d (si i) (si r) x hx invalid read,
    operand_failure target _ capacity (ti i) (ti r) _ (family.read r x hx read) outside,
    assignment_run target (ti i) (ti r) _ (family.read r x hx read),Backend.Failure.ofData_observes _⟩
end Solidity.Lowering.V07.EnumGuard

/-- info: 'Solidity.Lowering.V07.EnumGuard.word_range' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuard.word_range

/-- info: 'Solidity.Lowering.V07.EnumGuard.condition_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuard.condition_run

/-- info: 'Solidity.Lowering.V07.EnumGuard.guard_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuard.guard_success

/-- info: 'Solidity.Lowering.V07.EnumGuard.guard_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuard.guard_failure

/-- info: 'Solidity.Lowering.V07.EnumGuard.assignment_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuard.assignment_run

/-- info: 'Solidity.Lowering.V07.EnumGuard.code_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuard.code_success

/-- info: 'Solidity.Lowering.V07.EnumGuard.code_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuard.code_failure

/-- info: 'Solidity.Lowering.V07.EnumGuard.operand_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuard.operand_success

/-- info: 'Solidity.Lowering.V07.EnumGuard.operand_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuard.operand_failure

/-- info: 'Solidity.Lowering.V07.EnumGuard.transport_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuard.transport_success

/-- info: 'Solidity.Lowering.V07.EnumGuard.transport_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumGuard.transport_failure
