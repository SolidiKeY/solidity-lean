import Solidity.Lowering.V07.UnsignedQuotRem
import Solidity.Syntax.Checked
import Solidity.Lowering.V08.AbiObservations
import Solidity.Backend.Failure.Observe

/-! Actual published division panic guards and fresh result captures. The ABI
transport leaf was published/validated at059eb83d; no encoder, failure emitter,
Source semantics, profile or transaction/session projection is redefined. -/
namespace Solidity.Lowering.V07.UnsignedQuotRemGuard
open UnsignedQuotRem (calculate sourceOp)
open UnsignedNarrowing (ty)

def condition {C : Contract} {Γ : Ctx} (b : Idx Γ (.val .uint)) : Val C Γ .bool :=
  Checked.cmpU .neB rfl rfl (.simple (.local b)) (Checked.litU 0 (by decide))
def guard {C : Contract} {Γ : Ctx} (b : Idx Γ (.val .uint)) : Stmt C Γ Γ :=
  panicStmt 0x12 (condition b)
def code {C : Contract} {Γ : Ctx} (rem : Bool) (a b : Idx Γ (.val .uint)) :
    Prog C Γ (.val .uint :: Γ) :=
  .cons (guard b) (.cons (.declLocal .uint (.user "v07_quotrem_result")
    (some (UnsignedQuotRem.value rem (.simple (.local a)) (.simple (.local b))))) .nil)
def operand {C : Contract} {Γ : Ctx} (rem : Bool) (a b : Idx Γ (.val .uint)) :
    DeferredSource.Operand C Γ (.prim .uint) :=
  ⟨_,code rem a b,.val (.simple (.local .here))⟩

theorem metadata_condition {C : Contract} {Γ : Ctx} (rem : Bool) (b : Idx Γ (.val .uint)) :
    Checked.divPG (if rem then .mod else .div) .uint (.simple (.local b) : Val C Γ .uint) =
      [(0x12,condition b)] := by
  cases rem <;> rfl

theorem condition_run {C : Contract} {Γ : Ctx} (target : State C Γ) (b : Idx Γ (.val .uint))
    (v : PrimTy.uint.Denote) (read : TEnv.get b target.env = v) :
    (condition b).evalT target = .ok (!decide (v.val = 0)) := by
  change TRes.ofOpt (BinOp.evalT .neB rfl (TEnv.get b target.env)
    (⟨0,by decide⟩ : PrimTy.uint.Denote)) = _
  rw [read]
  rfl

theorem guard_success {C : Contract} {Γ : Ctx} (target : State C Γ) (b : Idx Γ (.val .uint))
    (v : PrimTy.uint.Denote) (read : TEnv.get b target.env = v) (nonzero : v.val ≠ 0) :
    (guard b).run target = .ok (⟨target,List.prefix_refl _⟩ : Out C target.H Γ) := by
  have test := condition_run target b v read
  simp only [nonzero,decide_false,Bool.not_false] at test
  change TRun.ite (condition b) _ _ _ _ target = _
  simp only [TRun.ite,test,boolT,TRun.nil]
  rfl

theorem guard_zero {C : Contract} {Γ : Ctx} (target : State C Γ) (b : Idx Γ (.val .uint))
    (v : PrimTy.uint.Denote) (read : TEnv.get b target.env = v) (zero : v.val = 0) :
    (guard b).run target = .error (THalt.ofData (Source.panicData .divZero)) := by
  have test := condition_run target b v read
  simp only [zero,decide_true,Bool.not_true] at test
  change TRun.ite (condition b) _ _ _ _ target = _
  have literal := Backend.Failure.revert_bytes_intrinsic target (Semantics.encodePanic 0x12)
  simp only [TRun.ite,test,boolT,ok_bind,Bool.false_eq_true,if_false,TRun.seq,literal]
  rw [V08.panicData_transport .divZero]
  rfl

theorem code_success (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (rem : Bool) (a b : Idx Γ (.val .uint))
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hn : y ≠ 0)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readB : TEnv.get b target.env = integerValue (ty bits valid) y hy) :
    (code rem a b).run target =
      .ok (⟨target.push (integerValue (ty bits valid) (calculate rem x y)
        (UnsignedQuotRem.result_range bits valid rem x y hx hy hn)),List.prefix_refl _⟩ :
        Out C target.H (.val .uint :: Γ)) := by
  have checked := guard_success target b (integerValue (ty bits valid) y hy) readB hn
  have arithmetic := UnsignedQuotRem.value_run bits valid target rem (.simple (.local a)) (.simple (.local b)) x y hx hy hn
    (congrArg Except.ok readA) (congrArg Except.ok readB)
  have captured : (Stmt.declLocal .uint (.user "v07_quotrem_result")
      (some (UnsignedQuotRem.value rem (.simple (.local a)) (.simple (.local b))))).run target =
      .ok (⟨target.push (integerValue (ty bits valid) (calculate rem x y)
        (UnsignedQuotRem.result_range bits valid rem x y hx hy hn)),List.prefix_refl _⟩) := by
    change (do
      let v ← (UnsignedQuotRem.value rem (.simple (.local a)) (.simple (.local b))).evalT target
      pure (⟨target.push v,List.prefix_refl _⟩ : Out C target.H (.val .uint :: Γ))) = _
    rw [arithmetic]
    rfl
  unfold code
  rw [Prog.run_cons_ok checked,Prog.run_cons_ok captured,Prog.run_nil]
  rfl

theorem code_zero {C : Contract} {Γ : Ctx} (target : State C Γ) (rem : Bool)
    (a b : Idx Γ (.val .uint)) (v : PrimTy.uint.Denote)
    (read : TEnv.get b target.env = v) (zero : v.val = 0) :
    (code rem a b).run target = .error (THalt.ofData (Source.panicData .divZero)) := by
  unfold code
  change TRun.seq (guard b).runR _ target = _
  simp only [TRun.seq,show (guard b).runR target = _ from guard_zero target b v read zero]

theorem operand_success (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (rem : Bool) (a b : Idx Γ (.val .uint))
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hn : y ≠ 0)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readB : TEnv.get b target.env = integerValue (ty bits valid) y hy) :
    (operand rem a b).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim (integerValue (ty bits valid) (calculate rem x y)
        (UnsignedQuotRem.result_range bits valid rem x y hx hy hn))) := by
  unfold operand DeferredSource.Operand.run
  rw [code_success bits valid target rem a b x y hx hy hn readA readB]
  rfl

theorem operand_zero {C : Contract} {Γ : Ctx} (target : State C Γ) (rem : Bool)
    (a b : Idx Γ (.val .uint)) (v : PrimTy.uint.Denote)
    (read : TEnv.get b target.env = v) (zero : v.val = 0) :
    (operand rem a b).run target = .error (THalt.ofData (Source.panicData .divZero)) := by
  unfold operand DeferredSource.Operand.run
  rw [code_zero target rem a b v read zero]
  rfl

theorem locals_success (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (rem : Bool)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env) (a b : ι)
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (hn : y ≠ 0)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy) :
    (Source.evalE G F (fuel+3) (.binary (sourceOp rem) (.local (si a)) (.local (si b)))).run source =
      (.ok (.val (.int (calculate rem x y) (UnsignedQuotRem.result_range bits valid rem x y hx hy hn))),source) ∧
    (operand rem (ti a) (ti b)).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim (integerValue (ty bits valid) (calculate rem x y)
        (UnsignedQuotRem.result_range bits valid rem x y hx hy hn))) ∧
    IntValueRel (ty bits valid)
      (.int (calculate rem x y) (UnsignedQuotRem.result_range bits valid rem x y hx hy hn) : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) (calculate rem x y) (UnsignedQuotRem.result_range bits valid rem x y hx hy hn)) := by
  have raw := UnsignedQuotRem.locals_transport bits valid G F fuel source target rem si ti family a b
    x y hx hy hn readA readB
  exact ⟨raw.1,operand_success bits valid target rem (ti a) (ti b) x y hx hy hn
    (family.read a x hx readA) (family.read b y hy readB),raw.2.2⟩

/-- Exact local Source panic and intrinsic failure outcome with the same bytes.
This does not supply a transaction/session failure projection or rollback law. -/
theorem locals_zero (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (rem : Bool)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env) (a b : ι)
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx)
    (readB : source.1.get (si b) = .int 0 (integer_zero_range (ty bits valid))) :
    (Source.evalE G F (fuel+3) (.binary (sourceOp rem) (.local (si a)) (.local (si b)))).run source =
      (.error (.revert (Source.panicData .divZero)),source) ∧
    (operand rem (ti a) (ti b)).run target = .error (THalt.ofData (Source.panicData .divZero)) ∧
    Backend.Failure.HaltObserves (THalt.ofData (Source.panicData .divZero)) (.revert (Source.panicData .divZero)) := by
  have raw := UnsignedQuotRem.locals_zero bits valid G F fuel source target rem si ti family a b x hx readA readB
  exact ⟨raw.1,operand_zero target rem (ti a) (ti b)
    (integerValue (ty bits valid) 0 (integer_zero_range (ty bits valid)))
    (family.read b 0 (integer_zero_range (ty bits valid)) readB) rfl,
    Backend.Failure.ofData_observes _⟩

end Solidity.Lowering.V07.UnsignedQuotRemGuard

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuard.metadata_condition' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuard.metadata_condition

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuard.condition_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuard.condition_run

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuard.guard_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuard.guard_success

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuard.guard_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuard.guard_zero

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuard.code_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuard.code_success

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuard.code_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuard.code_zero

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuard.operand_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuard.operand_success

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuard.operand_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuard.operand_zero

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuard.locals_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuard.locals_success

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuard.locals_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuard.locals_zero
