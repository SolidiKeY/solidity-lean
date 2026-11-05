import Solidity.Lowering.V07.LessThan
/-! All six numeric comparisons over the existing operator judgments.
The scalar relation evaluates independent Source operations and actual typed
Val/Prog/Operand clauses. No frontend selection or graph admission is claimed. -/
namespace Solidity.Lowering.V07.NumericComparisons

/-- Operator-name adapter. `classified` proves that callers satisfying the
existing numeric accepts/returns judgments use exactly the six explicit cases;
no preservation statement is made for the fallback outside that domain. -/
def sourceOp : BinOp → Source.BinOp
  | .lt => .lt | .gt => .gt | .le => .le | .ge => .ge | .eqB => .eq | .neB => .ne
  | _ => .eq

-- These are existing intrinsic operator judgments, not a Source admission guard.
theorem classified (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool) :
    op = .lt ∨ op = .gt ∨ op = .le ∨ op = .ge ∨ op = .eqB ∨ op = .neB := by
  cases op <;> first
    | (simp only [reduceCtorEq,or_true,true_or]; done)
    | (cases hr; done)
    | (cases hu; done)

theorem metadata (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (t : Source.IntTy) : op.accepts (integerPrim t) = true ∧ op.ret (integerPrim t) = .bool := by
  rcases classified op hu hr with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    obtain ⟨sign,bits,valid⟩ := t
    cases sign <;> exact ⟨rfl,rfl⟩

def value {C : Contract} {Γ : Ctx} (t : Source.IntTy) (op : BinOp)
    (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (a b : Val C Γ (integerPrim t)) : Val C Γ .bool :=
  .binop op (metadata op hu hr t).1 (metadata op hu hr t).2 a b

theorem value_run {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (a b : Val C Γ (integerPrim t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (left : a.evalT target = .ok (integerValue t x hx))
    (right : b.evalT target = .ok (integerValue t y hy)) :
    ∃ result : Bool,
      Source.cmpVal (sourceOp op) (.int x hx : Source.Val D (.int t)) (.int y hy) = .ok result ∧
      (value t op hu hr a b).evalT target = .ok result := by
  rcases classified op hu hr with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨_,rfl,?_⟩
    unfold value
    rw [Val.evalT,left,right]
    obtain ⟨sign,bits,valid⟩ := t
    cases sign <;> simp only [decide_not] <;> rfl

theorem source_from_pair {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source mid : Source.EMState E Γ) (t : Source.IntTy) (op : BinOp)
    (a b : Source.RExpr E Γ (.int t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) (result : Bool)
    (computed : Source.cmpVal (sourceOp op) (.int x hx : Source.Val E.layout (.int t)) (.int y hy) = .ok result)
    (pair : (Source.evalPair G F fuel a b).run source =
      (.ok (.val (.int x hx),.val (.int y hy)),mid)) :
    (Source.evalE G F (fuel+1) (.compare (sourceOp op) a b)).run source =
      (.ok (.val (.bool result)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,pair]
  change (do
    let v ← Source.EM.lift (Source.cmpVal (sourceOp op)
      (.int x hx : Source.Val E.layout (.int t)) (.int y hy))
    pure (Source.RVal.val (.bool v))).run mid = _
  rw [computed]
  rfl

theorem source_assignment {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E Γ) (t : Source.IntTy) (op : BinOp)
    (i a : Source.Idx Γ (.int t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) (result : Bool)
    (computed : Source.cmpVal (sourceOp op) (.int x hx : Source.Val E.layout (.int t))
      (.int (LessThan.rightAt G.pipeline x y) (LessThan.right_range G.pipeline t x y hx hy)) = .ok result)
    (readA : source.1.get a = .int x hx) (readI : source.1.get i = .int y hy) :
    (Source.evalE G F (fuel+4) (.compare (sourceOp op) (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (.bool result)),(source.1.set i (.int x hx),source.2)) := by
  have pair := source_assign_read_pair G F fuel source i a (.int x hx) (.int y hy) readA readI
  by_cases order : G.pipeline = .legacy
  · simp only [order,if_true] at pair
    simp only [LessThan.rightAt,order,if_true] at computed
    exact source_from_pair G F (fuel+3) source _ t op _ _ x y hx hy result computed pair
  · simp only [order,if_false] at pair
    simp only [LessThan.rightAt,order,if_false] at computed
    exact source_from_pair G F (fuel+3) source _ t op _ _ x x hx hx result computed pair

def tail {C : Contract} {Γ : Ctx} (t : Source.IntTy) (op : BinOp)
    (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (a b : Idx Γ (.val (integerPrim t))) : Prog C Γ (.val .bool :: Γ) :=
  .cons (.declLocal .bool (.user "v07_compare_result")
    (some (value t op hu hr (.simple (.local a)) (.simple (.local b))))) .nil

theorem tail_run {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (a b : Idx Γ (.val (integerPrim t))) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readB : TEnv.get b target.env = integerValue t y hy) :
    ∃ result : Bool,
      Source.cmpVal (sourceOp op) (.int x hx : Source.Val D (.int t)) (.int y hy) = .ok result ∧
      (tail t op hu hr a b).run target =
        .ok (⟨target.push result,List.prefix_refl _⟩ : Out C target.H (.val .bool :: Γ)) := by
  obtain ⟨result,computed,run⟩ := value_run (D := D) target t op hu hr
    (.simple (.local a)) (.simple (.local b)) x y hx hy (congrArg Except.ok readA) (congrArg Except.ok readB)
  refine ⟨result,computed,?_⟩
  have captured : (Stmt.declLocal .bool (.user "v07_compare_result")
      (some (value t op hu hr (.simple (.local a)) (.simple (.local b))))).run target =
      .ok (⟨target.push result,List.prefix_refl _⟩) := by
    change (do
      let v ← (value t op hu hr (.simple (.local a)) (.simple (.local b))).evalT target
      pure (⟨target.push v,List.prefix_refl _⟩ : Out C target.H (.val .bool :: Γ))) = _
    rw [run]
    rfl
  unfold tail
  rw [Prog.run_cons_ok captured,Prog.run_nil]
  rfl

def code {C : Contract} {Γ : Ctx} (t : Source.IntTy) (op : BinOp)
    (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool) (p : Roadmap.Pipeline)
    (i a : Idx Γ (.val (integerPrim t))) :
    Prog C Γ (.val .bool :: .val (integerPrim t) :: .val (integerPrim t) :: Γ) :=
  match p with
  | .legacy => (assignReadPrefix p i a).join (tail t op hu hr .here (.there .here))
  | .viaIR => (assignReadPrefix p i a).join (tail t op hu hr (.there .here) .here)

def operand {C : Contract} {Γ : Ctx} (t : Source.IntTy) (op : BinOp)
    (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool) (p : Roadmap.Pipeline)
    (i a : Idx Γ (.val (integerPrim t))) : DeferredSource.Operand C Γ (.prim .bool) :=
  ⟨_,code t op hu hr p i a,.val (.simple (.local .here))⟩

theorem pass_exact {C : Contract} {Γ : Ctx} (t : Source.IntTy) (op : BinOp)
    (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool) (p : Roadmap.Pipeline)
    (i a : Idx Γ (.val (integerPrim t))) :
    (code (C := C) t op hu hr p i a).withPanics = code t op hu hr p i a := by
  rcases classified op hu hr with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    obtain ⟨sign,bits,valid⟩ := t
    cases sign <;> cases p <;> rfl

theorem code_run {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (p : Roadmap.Pipeline) (i a : Idx Γ (.val (integerPrim t))) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readI : TEnv.get i target.env = integerValue t y hy) :
    ∃ result : Bool,
      Source.cmpVal (sourceOp op) (.int x hx : Source.Val D (.int t))
        (.int (LessThan.rightAt p x y) (LessThan.right_range p t x y hx hy)) = .ok result ∧
      (code t op hu hr p i a).run target =
        .ok (⟨(((target.setLocal i (integerValue t x hx)).push
          (integerValue t (LessThan.rightAt p x y) (LessThan.right_range p t x y hx hy))).push
          (integerValue t x hx)).push result,List.prefix_refl _⟩) := by
  have pre := assign_read_prefix_run p target i a (integerValue t x hx) (integerValue t y hy) readA readI
  cases p
  · obtain ⟨result,computed,finish⟩ := tail_run (D := D)
      (((target.setLocal i (integerValue t x hx)).push (integerValue t y hy)).push (integerValue t x hx))
      t op hu hr .here (.there .here) x y hx hy rfl rfl
    refine ⟨result,computed,?_⟩
    unfold code
    rw [DeferredSource.join_run]
    simp only [TRun.seq,pre]
    change ((tail t op hu hr .here (.there .here)).run
      (((target.setLocal i (integerValue t x hx)).push (integerValue t y hy)).push (integerValue t x hx))).map (fun out => out) = _
    rw [finish]
    rfl
  · obtain ⟨result,computed,finish⟩ := tail_run (D := D)
      (((target.setLocal i (integerValue t x hx)).push (integerValue t x hx)).push (integerValue t x hx))
      t op hu hr (.there .here) .here x x hx hx rfl rfl
    refine ⟨result,computed,?_⟩
    unfold code
    rw [DeferredSource.join_run]
    simp only [TRun.seq,pre]
    change ((tail t op hu hr (.there .here) .here).run
      (((target.setLocal i (integerValue t x hx)).push (integerValue t x hx)).push (integerValue t x hx))).map (fun out => out) = _
    rw [finish]
    rfl

theorem operand_run {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (p : Roadmap.Pipeline) (i a : Idx Γ (.val (integerPrim t))) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readI : TEnv.get i target.env = integerValue t y hy) :
    ∃ result : Bool,
      Source.cmpVal (sourceOp op) (.int x hx : Source.Val D (.int t))
        (.int (LessThan.rightAt p x y) (LessThan.right_range p t x y hx hy)) = .ok result ∧
      (operand t op hu hr p i a).run target =
        .ok (⟨target.setLocal i (integerValue t x hx),List.prefix_refl _⟩,.prim result) := by
  obtain ⟨result,computed,run⟩ := code_run (D := D) target t op hu hr p i a x y hx hy readA readI
  refine ⟨result,computed,?_⟩
  unfold operand DeferredSource.Operand.run
  rw [run]
  cases p <;> rfl

theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (t : Source.IntTy)
    (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (si : ι → Source.Idx srcΓ (.int t)) (ti : ι → Idx Γ (.val (integerPrim t)))
    (family : IntegerLocalFamily t si ti source.1 target.env) (i a : ι)
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : source.1.get (si a) = .int x hx) (readI : source.1.get (si i) = .int y hy) :
    ∃ result : Bool,
      (Source.evalE G F (fuel+4) (.compare (sourceOp op) (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
        (.ok (.val (.bool result)),(source.1.set (si i) (.int x hx),source.2)) ∧
      (operand t op hu hr G.pipeline (ti i) (ti a)).run target =
        .ok (⟨target.setLocal (ti i) (integerValue t x hx),List.prefix_refl _⟩,.prim result) ∧
      IntegerLocalFamily t si ti (source.1.set (si i) (.int x hx))
        (TEnv.set (ti i) (integerValue t x hx) target.env) := by
  obtain ⟨result,computed,run⟩ := operand_run (D := E.layout) target t op hu hr G.pipeline
    (ti i) (ti a) x y hx hy (family.read a x hx readA) (family.read i y hy readI)
  refine ⟨result,source_assignment G F fuel source t op (si i) (si a) x y hx hy result computed readA readI,run,?_⟩
  have post := family.write i a
  rw [readA,family.read a x hx readA] at post
  exact post
end Solidity.Lowering.V07.NumericComparisons

/-- info: 'Solidity.Lowering.V07.NumericComparisons.classified' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisons.classified

/-- info: 'Solidity.Lowering.V07.NumericComparisons.metadata' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisons.metadata

/-- info: 'Solidity.Lowering.V07.NumericComparisons.value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisons.value_run

/-- info: 'Solidity.Lowering.V07.NumericComparisons.source_from_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisons.source_from_pair

/-- info: 'Solidity.Lowering.V07.NumericComparisons.source_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisons.source_assignment

/-- info: 'Solidity.Lowering.V07.NumericComparisons.tail_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisons.tail_run

/-- info: 'Solidity.Lowering.V07.NumericComparisons.pass_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisons.pass_exact

/-- info: 'Solidity.Lowering.V07.NumericComparisons.code_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisons.code_run

/-- info: 'Solidity.Lowering.V07.NumericComparisons.operand_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisons.operand_run

/-- info: 'Solidity.Lowering.V07.NumericComparisons.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisons.transport
