import Solidity.Lowering.V07.EffectfulCondition

/-! Boolean equality clauses over independent Source operations and actual
intrinsic programs. Context-map alignment is an initial value relation, not
an assumed execution-preservation result. No frontend producer is supplied. -/
namespace Solidity.Lowering.V07.BooleanComparisons

def sourceOp (ne : Bool) : Source.BinOp := if ne then .ne else .eq
def answer (ne x y : Bool) : Bool := if ne then x != y else x == y

theorem answer_commutes (ne x y : Bool) : answer ne x y = answer ne y x := by
  cases ne <;> cases x <;> cases y <;> rfl

theorem source_value {D : Source.Layout} (ne x y : Bool) :
    Source.cmpVal (sourceOp ne) (.bool x : Source.Val D .bool) (.bool y) = .ok (answer ne x y) := by
  cases ne <;> cases x <;> cases y <;> rfl

def value {C : Contract} {Γ : Ctx} (ne : Bool) (a b : Val C Γ .bool) : Val C Γ .bool :=
  if ne then .binop .neB rfl rfl a b else .binop .eqB rfl rfl a b

theorem value_run {C : Contract} {Γ : Ctx} (target : State C Γ) (ne : Bool)
    (a b : Val C Γ .bool) (x y : Bool)
    (left : a.evalT target = .ok x) (right : b.evalT target = .ok y) :
    (value ne a b).evalT target = .ok (answer ne x y) := by
  cases ne <;> simp only [value,Bool.false_eq_true,if_false,if_true] <;>
    rw [Val.evalT,left,right] <;> cases x <;> cases y <;> rfl

theorem source_from_pair {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (ne : Bool) (a b : Source.RExpr E Γ .bool) (x y : Bool)
    (pair : (Source.evalPair G F fuel a b).run source = (.ok (.val (.bool x),.val (.bool y)),mid)) :
    (Source.evalE G F (fuel+1) (.compare (sourceOp ne) a b)).run source =
      (.ok (.val (.bool (answer ne x y))),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,pair]
  change (do
    let v ← Source.EM.lift (Source.cmpVal (sourceOp ne) (.bool x : Source.Val E.layout .bool) (.bool y))
    pure (Source.RVal.val (.bool v))).run mid = _
  rw [source_value]
  rfl

theorem source_assignment {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (ne : Bool) (i a : Source.Idx Γ .bool) (x y : Bool)
    (readA : source.1.get a = .bool x) (readI : source.1.get i = .bool y) :
    (Source.evalE G F (fuel+4) (.compare (sourceOp ne) (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (.bool (answer ne x (if G.pipeline = .legacy then y else x)))),
        (source.1.set i (.bool x),source.2)) := by
  have pair := source_assign_read_pair G F fuel source i a (.bool x) (.bool y) readA readI
  by_cases order : G.pipeline = .legacy
  · simp only [order,if_true] at pair ⊢
    exact source_from_pair G F (fuel+3) source _ ne _ _ x y pair
  · simp only [order,if_false] at pair ⊢
    exact source_from_pair G F (fuel+3) source _ ne _ _ x x pair

def tail {C : Contract} {Γ : Ctx} (ne : Bool) (a b : Idx Γ (.val .bool)) :
    Prog C Γ (.val .bool :: Γ) :=
  .cons (.declLocal .bool (.user "v07_bool_compare")
    (some (value ne (.simple (.local a)) (.simple (.local b))))) .nil

theorem tail_run {C : Contract} {Γ : Ctx} (target : State C Γ) (ne : Bool)
    (a b : Idx Γ (.val .bool)) (x y : Bool)
    (readA : TEnv.get a target.env = x) (readB : TEnv.get b target.env = y) :
    (tail ne a b).run target =
      .ok (⟨target.push (t := .val .bool) (answer ne x y),List.prefix_refl _⟩) := by
  have run := value_run target ne (.simple (.local a)) (.simple (.local b)) x y
    (congrArg Except.ok readA) (congrArg Except.ok readB)
  have captured : (Stmt.declLocal .bool (.user "v07_bool_compare")
      (some (value ne (.simple (.local a)) (.simple (.local b))))).run target =
      .ok (⟨target.push (t := .val .bool) (answer ne x y),List.prefix_refl _⟩) := by
    change (do
      let v ← (value ne (.simple (.local a)) (.simple (.local b))).evalT target
      pure (⟨target.push (t := .val .bool) v,List.prefix_refl _⟩ : Out C target.H (.val .bool :: Γ))) = _
    rw [run]
    rfl
  unfold tail
  rw [Prog.run_cons_ok captured,Prog.run_nil]
  rfl

/-- Only already-captured total local reads commute; this does not commute
Source operand executions or potentially failing general values. -/
theorem tail_swap_run {C : Contract} {Γ : Ctx} (target : State C Γ) (ne : Bool)
    (a b : Idx Γ (.val .bool)) :
    (tail ne a b).run target = (tail ne b a).run target := by
  rw [tail_run target ne a b _ _ rfl rfl,tail_run target ne b a _ _ rfl rfl,
    answer_commutes ne (TEnv.get a target.env) (TEnv.get b target.env)]

def code {C : Contract} {Γ : Ctx} (ne : Bool) (p : Roadmap.Pipeline)
    (i a : Idx Γ (.val .bool)) : Prog C Γ (.val .bool :: .val .bool :: .val .bool :: Γ) :=
  match p with
  | .legacy => (assignReadPrefix p i a).join (tail ne .here (.there .here))
  | .viaIR => (assignReadPrefix p i a).join (tail ne (.there .here) .here)

def operand {C : Contract} {Γ : Ctx} (ne : Bool) (p : Roadmap.Pipeline)
    (i a : Idx Γ (.val .bool)) : DeferredSource.Operand C Γ (.prim .bool) :=
  ⟨_,code ne p i a,.val (.simple (.local .here))⟩

theorem pass_exact {C : Contract} {Γ : Ctx} (ne : Bool) (p : Roadmap.Pipeline)
    (i a : Idx Γ (.val .bool)) : (code (C := C) ne p i a).withPanics = code ne p i a := by
  cases ne <;> cases p <;> rfl

theorem code_run {C : Contract} {Γ : Ctx} (target : State C Γ) (ne : Bool)
    (p : Roadmap.Pipeline) (i a : Idx Γ (.val .bool)) (x y : Bool)
    (readA : TEnv.get a target.env = x) (readI : TEnv.get i target.env = y) :
    (code ne p i a).run target =
      .ok (⟨(((target.setLocal i x).push (t := .val .bool) (if p = .legacy then y else x)).push
        (t := .val .bool) x).push (t := .val .bool) (answer ne x (if p = .legacy then y else x)),
        List.prefix_refl _⟩) := by
  have pre := assign_read_prefix_run p target i a x y readA readI
  cases p
  · unfold code
    rw [DeferredSource.join_run]
    simp only [TRun.seq,pre]
    change ((tail ne .here (.there .here)).run
      (((target.setLocal i x).push (t := .val .bool) y).push (t := .val .bool) x)).map (fun out => out) = _
    rw [tail_run _ ne _ _ x y rfl rfl]
    rfl
  · unfold code
    rw [DeferredSource.join_run]
    simp only [TRun.seq,pre]
    change ((tail ne (.there .here) .here).run
      (((target.setLocal i x).push (t := .val .bool) x).push (t := .val .bool) x)).map (fun out => out) = _
    rw [tail_run _ ne _ _ x x rfl rfl]
    rfl

theorem operand_run {C : Contract} {Γ : Ctx} (target : State C Γ) (ne : Bool)
    (p : Roadmap.Pipeline) (i a : Idx Γ (.val .bool)) (x y : Bool)
    (readA : TEnv.get a target.env = x) (readI : TEnv.get i target.env = y) :
    (operand ne p i a).run target =
      .ok (⟨target.setLocal i x,List.prefix_refl _⟩,.prim (answer ne x (if p = .legacy then y else x))) := by
  unfold operand DeferredSource.Operand.run
  rw [code_run target ne p i a x y readA readI]
  cases p <;> rfl

/-- Context extension over existing references, with no heap change. -/
theorem capture_relation {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (caller : State C Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C caller.H → Prop)
    (source : Source.Locals D srcΓ) (old : m.Related R source caller.env) (right left result : Bool) :
    (m.wk (Thin.drop (Thin.drop (Thin.drop Thin.refl)))).Related R source
      (((caller.push (t := .val .bool) right).push (t := .val .bool) left).push
        (t := .val .bool) result).env := by
  intro τ i
  exact old i

theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool), R .bool (.val .bool) v b → v = .bool b)
    (ne : Bool) (i a : Source.Idx srcΓ .bool) (j b : Idx Γ (.val .bool))
    (writeMap : m.slot i = ⟨.val .bool,j⟩) (readMap : m.slot a = ⟨.val .bool,b⟩) :
    (Source.evalE G F (fuel+4) (.compare (sourceOp ne) (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (.bool (answer ne (TEnv.get b target.env)
        (if G.pipeline = .legacy then TEnv.get j target.env else TEnv.get b target.env)))),
        (source.1.set i (.bool (TEnv.get b target.env)),source.2)) ∧
    (operand ne G.pipeline j b).run target =
      .ok (⟨target.setLocal j (TEnv.get b target.env),List.prefix_refl _⟩,
        .prim (answer ne (TEnv.get b target.env)
          (if G.pipeline = .legacy then TEnv.get j target.env else TEnv.get b target.env))) ∧
    m.Related R (source.1.set i (.bool (TEnv.get b target.env)))
      (TEnv.set j (TEnv.get b target.env) target.env) ∧
    (m.wk (Thin.drop (Thin.drop (Thin.drop Thin.refl)))).Related R
      (source.1.set i (.bool (TEnv.get b target.env)))
      ((((target.setLocal j (TEnv.get b target.env)).push (t := .val .bool)
        (if G.pipeline = .legacy then TEnv.get j target.env else TEnv.get b target.env)).push
        (t := .val .bool) (TEnv.get b target.env)).push (t := .val .bool)
        (answer ne (TEnv.get b target.env)
          (if G.pipeline = .legacy then TEnv.get j target.env else TEnv.get b target.env))).env := by
  have readA := boolReflect _ _ (ContextMap.value_at m R source.1 target.env aligned a b readMap)
  have readI := boolReflect _ _ (ContextMap.value_at m R source.1 target.env aligned i j writeMap)
  have post : m.Related R (source.1.set i (source.1.get a))
      (TEnv.set j (TEnv.get b target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i a j b writeMap readMap
  rw [readA] at post
  exact ⟨source_assignment G F fuel source ne i a _ _ readA readI,
    operand_run target ne G.pipeline j b _ _ rfl rfl,post,
    capture_relation m (target.setLocal j (TEnv.get b target.env)) R _ post _ _ _⟩
end Solidity.Lowering.V07.BooleanComparisons

/-- info: 'Solidity.Lowering.V07.BooleanComparisons.answer_commutes' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisons.answer_commutes

/-- info: 'Solidity.Lowering.V07.BooleanComparisons.source_value' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisons.source_value

/-- info: 'Solidity.Lowering.V07.BooleanComparisons.value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisons.value_run

/-- info: 'Solidity.Lowering.V07.BooleanComparisons.source_from_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisons.source_from_pair

/-- info: 'Solidity.Lowering.V07.BooleanComparisons.source_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisons.source_assignment

/-- info: 'Solidity.Lowering.V07.BooleanComparisons.tail_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisons.tail_run

/-- info: 'Solidity.Lowering.V07.BooleanComparisons.tail_swap_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisons.tail_swap_run

/-- info: 'Solidity.Lowering.V07.BooleanComparisons.pass_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisons.pass_exact

/-- info: 'Solidity.Lowering.V07.BooleanComparisons.code_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisons.code_run

/-- info: 'Solidity.Lowering.V07.BooleanComparisons.operand_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisons.operand_run

/-- info: 'Solidity.Lowering.V07.BooleanComparisons.capture_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisons.capture_relation

/-- info: 'Solidity.Lowering.V07.BooleanComparisons.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisons.transport
