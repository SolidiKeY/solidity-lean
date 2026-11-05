import Solidity.Lowering.V07.AssignmentOrder
import Solidity.Lowering.V07.DoubleAssignment

/-! Signed and unsigned less-than on existing Source and intrinsic carriers.
Actual assignment/read order and captures are preserved; no frontend selection
or general comparison completeness is claimed. -/
namespace Solidity.Lowering.V07.LessThan

theorem accepts (t : Source.IntTy) : BinOp.lt.accepts (integerPrim t) = true := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign <;> rfl

def value {C : Contract} {Γ : Ctx} (t : Source.IntTy)
    (a b : Val C Γ (integerPrim t)) : Val C Γ .bool :=
  .binop .lt (accepts t) rfl a b

theorem source_value {D : Source.Layout} (t : Source.IntTy) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    Source.cmpVal .lt (.int x hx : Source.Val D (.int t)) (.int y hy) =
      .ok (decide (x < y)) := rfl

theorem value_run {C : Contract} {Γ : Ctx} (target : State C Γ) (t : Source.IntTy)
    (a b : Val C Γ (integerPrim t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (left : a.evalT target = .ok (integerValue t x hx))
    (right : b.evalT target = .ok (integerValue t y hy)) :
    (value t a b).evalT target = .ok (decide (x < y)) := by
  unfold value
  rw [Val.evalT,left]
  change (do
    let w ← b.evalT target
    TRes.ofOpt (BinOp.evalT .lt (accepts t) (integerValue t x hx) w)) = _
  rw [right]
  obtain ⟨sign,bits,valid⟩ := t
  cases sign <;> rfl

theorem source_from_pair {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source mid : Source.EMState E Γ) (t : Source.IntTy)
    (a b : Source.RExpr E Γ (.int t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (pair : (Source.evalPair G F fuel a b).run source =
      (.ok (.val (.int x hx),.val (.int y hy)),mid)) :
    (Source.evalE G F (fuel+1) (.compare .lt a b)).run source =
      (.ok (.val (.bool (decide (x < y)))),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,pair]
  change (do
    let v ← Source.EM.lift (Source.cmpVal .lt
      (.int x hx : Source.Val E.layout (.int t)) (.int y hy))
    pure (Source.RVal.val (.bool v))).run mid = _
  rw [source_value]
  rfl

def rightAt (p : Roadmap.Pipeline) (assigned old : Int) : Int :=
  if p = .legacy then old else assigned

theorem right_range (p : Roadmap.Pipeline) (t : Source.IntTy) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    t.lo ≤ rightAt p x y ∧ rightAt p x y ≤ t.hi := by
  cases p <;> assumption

theorem source_assignment {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E Γ) (t : Source.IntTy)
    (i a : Source.Idx Γ (.int t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : source.1.get a = .int x hx) (readI : source.1.get i = .int y hy) :
    (Source.evalE G F (fuel+4) (.compare .lt (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (.bool (decide (x < rightAt G.pipeline x y)))),
        (source.1.set i (.int x hx),source.2)) := by
  have pair := source_assign_read_pair G F fuel source i a (.int x hx) (.int y hy) readA readI
  by_cases order : G.pipeline = .legacy
  · simp only [order,if_true] at pair
    simp only [rightAt,order,if_true]
    exact source_from_pair G F (fuel+3) source _ t _ _ x y hx hy pair
  · simp only [order,if_false] at pair
    simp only [rightAt,order,if_false]
    exact source_from_pair G F (fuel+3) source _ t _ _ x x hx hx pair

def tail {C : Contract} {Γ : Ctx} (t : Source.IntTy) (a b : Idx Γ (.val (integerPrim t))) :
    Prog C Γ (.val .bool :: Γ) :=
  .cons (.declLocal .bool (.user "v07_less_result")
    (some (value t (.simple (.local a)) (.simple (.local b))))) .nil

theorem tail_run {C : Contract} {Γ : Ctx} (target : State C Γ) (t : Source.IntTy)
    (a b : Idx Γ (.val (integerPrim t))) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readB : TEnv.get b target.env = integerValue t y hy) :
    (tail t a b).run target =
      .ok (⟨target.push (decide (x < y)),List.prefix_refl _⟩ : Out C target.H (.val .bool :: Γ)) := by
  have run := value_run target t (.simple (.local a)) (.simple (.local b)) x y hx hy
    (congrArg Except.ok readA) (congrArg Except.ok readB)
  have captured : (Stmt.declLocal .bool (.user "v07_less_result")
      (some (value t (.simple (.local a)) (.simple (.local b))))).run target =
      .ok (⟨target.push (decide (x < y)),List.prefix_refl _⟩) := by
    change (do
      let v ← (value t (.simple (.local a)) (.simple (.local b))).evalT target
      pure (⟨target.push v,List.prefix_refl _⟩ : Out C target.H (.val .bool :: Γ))) = _
    rw [run]
    rfl
  unfold tail
  rw [Prog.run_cons_ok captured,Prog.run_nil]
  rfl

def code {C : Contract} {Γ : Ctx} (t : Source.IntTy) (p : Roadmap.Pipeline)
    (i a : Idx Γ (.val (integerPrim t))) :
    Prog C Γ (.val .bool :: .val (integerPrim t) :: .val (integerPrim t) :: Γ) :=
  match p with
  | .legacy => (assignReadPrefix p i a).join (tail t .here (.there .here))
  | .viaIR => (assignReadPrefix p i a).join (tail t (.there .here) .here)

def operand {C : Contract} {Γ : Ctx} (t : Source.IntTy) (p : Roadmap.Pipeline)
    (i a : Idx Γ (.val (integerPrim t))) : DeferredSource.Operand C Γ (.prim .bool) :=
  ⟨_,code t p i a,.val (.simple (.local .here))⟩

theorem code_run {C : Contract} {Γ : Ctx} (target : State C Γ) (t : Source.IntTy)
    (p : Roadmap.Pipeline) (i a : Idx Γ (.val (integerPrim t))) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readI : TEnv.get i target.env = integerValue t y hy) :
    (code t p i a).run target =
      .ok (⟨(((target.setLocal i (integerValue t x hx)).push
        (integerValue t (rightAt p x y) (right_range p t x y hx hy))).push
        (integerValue t x hx)).push (decide (x < rightAt p x y)),List.prefix_refl _⟩) := by
  have pre := assign_read_prefix_run p target i a (integerValue t x hx) (integerValue t y hy) readA readI
  have rightEq : (if p = .legacy then integerValue t y hy else integerValue t x hx) =
      integerValue t (rightAt p x y) (right_range p t x y hx hy) := by cases p <;> rfl
  rw [rightEq] at pre
  cases p
  · unfold code
    rw [DeferredSource.join_run]
    simp only [TRun.seq,pre]
    change ((tail t .here (.there .here)).run
      (((target.setLocal i (integerValue t x hx)).push (integerValue t y hy)).push (integerValue t x hx))).map (fun out => out) = _
    rw [tail_run _ t _ _ x y hx hy rfl rfl]
    rfl
  · unfold code
    rw [DeferredSource.join_run]
    simp only [TRun.seq,pre]
    change ((tail t (.there .here) .here).run
      (((target.setLocal i (integerValue t x hx)).push (integerValue t x hx)).push (integerValue t x hx))).map (fun out => out) = _
    rw [tail_run _ t _ _ x x hx hx rfl rfl]
    rfl

theorem operand_run {C : Contract} {Γ : Ctx} (target : State C Γ) (t : Source.IntTy)
    (p : Roadmap.Pipeline) (i a : Idx Γ (.val (integerPrim t))) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readI : TEnv.get i target.env = integerValue t y hy) :
    (operand t p i a).run target =
      .ok (⟨target.setLocal i (integerValue t x hx),List.prefix_refl _⟩,
        .prim (decide (x < rightAt p x y))) := by
  unfold operand DeferredSource.Operand.run
  rw [code_run target t p i a x y hx hy readA readI]
  cases p <;> rfl

theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (t : Source.IntTy)
    (si : ι → Source.Idx srcΓ (.int t)) (ti : ι → Idx Γ (.val (integerPrim t)))
    (family : IntegerLocalFamily t si ti source.1 target.env) (i a : ι)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : source.1.get (si a) = .int x hx) (readI : source.1.get (si i) = .int y hy) :
    (Source.evalE G F (fuel+4) (.compare .lt (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
      (.ok (.val (.bool (decide (x < rightAt G.pipeline x y)))),
        (source.1.set (si i) (.int x hx),source.2)) ∧
    (operand t G.pipeline (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue t x hx),List.prefix_refl _⟩,
        .prim (decide (x < rightAt G.pipeline x y))) ∧
    IntegerLocalFamily t si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue t x hx) target.env) := by
  refine ⟨source_assignment G F fuel source t (si i) (si a) x y hx hy readA readI,
    operand_run target t G.pipeline (ti i) (ti a) x y hx hy (family.read a x hx readA)
      (family.read i y hy readI),?_⟩
  have post := family.write i a
  rw [readA,family.read a x hx readA] at post
  exact post
end Solidity.Lowering.V07.LessThan

/-- info: 'Solidity.Lowering.V07.LessThan.accepts' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThan.accepts

/-- info: 'Solidity.Lowering.V07.LessThan.source_value' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThan.source_value

/-- info: 'Solidity.Lowering.V07.LessThan.value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThan.value_run

/-- info: 'Solidity.Lowering.V07.LessThan.source_from_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThan.source_from_pair

/-- info: 'Solidity.Lowering.V07.LessThan.right_range' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThan.right_range

/-- info: 'Solidity.Lowering.V07.LessThan.source_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThan.source_assignment

/-- info: 'Solidity.Lowering.V07.LessThan.tail_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThan.tail_run

/-- info: 'Solidity.Lowering.V07.LessThan.code_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThan.code_run

/-- info: 'Solidity.Lowering.V07.LessThan.operand_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThan.operand_run

/-- info: 'Solidity.Lowering.V07.LessThan.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThan.transport
