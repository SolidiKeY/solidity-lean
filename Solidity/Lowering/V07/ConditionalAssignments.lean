import Solidity.Lowering.V07.ShortCircuit

/-! G17 conditional EXPRESSION transport over published typed operations.
No block/loop/modifier compiler, new evaluator or admission certificate. -/
namespace Solidity.Lowering.V07.ConditionalAssignments

def sourceAfter {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (s : Source.EMState E Γ) (ci : Source.Idx Γ .bool) (choice : Bool)
    (i a j b : Source.Idx Γ τ) : Source.EMState E Γ :=
  let reached := s.1.set ci (.bool choice)
  (reached.set (if choice then i else j) (reached.get (if choice then a else b)),s.2)

def targetAfter {C : Contract} {Γ : Ctx} {p : PrimTy}
    (s : State C Γ) (ci : Idx Γ (.val .bool)) (choice : Bool)
    (i a j b : Idx Γ (.val p)) : State C Γ :=
  let reached := s.setLocal ci choice
  reached.setLocal (if choice then i else j) (TEnv.get (if choice then a else b) reached.env)

theorem source_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (ci ca : Source.Idx Γ .bool) (choice : Bool) (i a j b : Source.Idx Γ τ)
    (read : s.1.get ca = .bool choice) :
    (Source.evalE G F (fuel+3) (.cond (.assign (.local ci) (.local ca))
      (.assign (.local i) (.local a)) (.assign (.local j) (.local b)))).run s =
      (.ok (.val ((s.1.set ci (.bool choice)).get (if choice then a else b))),
        sourceAfter s ci choice i a j b) := by
  rw [Source.evalE,Source.Hoare.run_bind,
    source_assign_local_run G F fuel s ci ca _ read]
  dsimp only
  rw [Source.Hoare.run_bind,source_getV_run]
  cases choice
  · exact source_assign_local_run G F fuel (s.1.set ci (.bool false),s.2) j b _ rfl
  · exact source_assign_local_run G F fuel (s.1.set ci (.bool true),s.2) i a _ rfl

/-- Both input temporaries are fresh; write the caller before snapshotting the
selected assignment's result. The captured condition cannot be overwritten by
an original caller alias. -/
def branch {C : Contract} {Γ : Ctx} {p : PrimTy} (i a : Idx Γ (.val p)) :
    Prog C (.val p :: .val .bool :: Γ) (.val p :: .val .bool :: Γ) :=
  .cons (.assignLocal (.there (.there i)) (.simple (.local (.there (.there a)))))
    (.cons (.assignLocal .here (.simple (.local (.there (.there i))))) .nil)

theorem branch_run {C : Contract} {Γ : Ctx} {p : PrimTy}
    (s : State C Γ) (i a : Idx Γ (.val p)) (choice : Bool) (placeholder : p.Denote) :
    (branch i a).run ((s.push (t := .val .bool) choice).push placeholder) =
      .ok (⟨((s.setLocal i (TEnv.get a s.env)).push (t := .val .bool) choice).push
        (TEnv.get a s.env),List.prefix_refl _⟩) := by
  change (do
    let value ← (Except.ok (TEnv.get a s.env) : TRes p.Denote)
    let captured ← (Except.ok (TEnv.get i (TEnv.set i value s.env)) : TRes p.Denote)
    pure (⟨((s.setLocal i value).push (t := .val .bool) choice).push captured,
      List.prefix_refl _⟩ : Out C s.H (.val p :: .val .bool :: Γ))) = _
  simp only [TEnv.get_set]
  rfl

def code {C : Contract} {Γ : Ctx} {p : PrimTy} (ci ca : Idx Γ (.val .bool))
    (i a j b : Idx Γ (.val p)) : Prog C Γ (.val p :: .val .bool :: Γ) :=
  .cons (.assignLocal ci (.simple (.local ca)))
    (.cons (.declLocal .bool (.user "v07_choice") (some (.simple (.local ci))))
      (.cons (.declLocal p (.user "v07_selected") none)
        (.cons (.ite (.simple (.local (.there .here))) (branch i a) (branch j b)) .nil)))

theorem prefix_run {C : Contract} {Γ : Ctx} {p : PrimTy}
    (s : State C Γ) (ci ca : Idx Γ (.val .bool)) (choice : Bool)
    (i a j b : Idx Γ (.val p)) (read : TEnv.get ca s.env = choice) :
    (code ci ca i a j b).run s =
      .ok (⟨((targetAfter s ci choice i a j b).push (t := .val .bool) choice).push
        (TEnv.get (if choice then a else b) (TEnv.set ci choice s.env)),List.prefix_refl _⟩) := by
  have first : (Stmt.assignLocal ci (.simple (.local ca))).run s =
      .ok (⟨s.setLocal ci choice,List.prefix_refl _⟩) := by
    change Except.ok (⟨s.setLocal ci (TEnv.get ca s.env),List.prefix_refl _⟩ : Out C s.H Γ) = _
    rw [read]
  have capture : (Stmt.declLocal .bool (.user "v07_choice") (some (.simple (.local ci)))).run
      (s.setLocal ci choice) =
      .ok (⟨(s.setLocal ci choice).push (t := .val .bool) choice,List.prefix_refl _⟩) := by
    change Except.ok (⟨(s.setLocal ci choice).push (t := .val .bool)
      (TEnv.get ci (TEnv.set ci choice s.env)),List.prefix_refl _⟩ : Out C s.H (.val .bool :: Γ)) = _
    rw [TEnv.get_set]
  have reserve : (Stmt.declLocal p (.user "v07_selected") none).run
      ((s.setLocal ci choice).push (t := .val .bool) choice) =
      .ok (⟨((s.setLocal ci choice).push (t := .val .bool) choice).push
        (PrimTy.dflt p),List.prefix_refl _⟩) := rfl
  have selection : (Stmt.ite (.simple (.local (.there .here))) (branch i a) (branch j b)).run
      (((s.setLocal ci choice).push (t := .val .bool) choice).push (PrimTy.dflt p)) =
      .ok (⟨((targetAfter s ci choice i a j b).push (t := .val .bool) choice).push
        (TEnv.get (if choice then a else b) (TEnv.set ci choice s.env)),List.prefix_refl _⟩) := by
    cases choice
    · change ((branch j b).run (((s.setLocal ci false).push (t := .val .bool) false).push
        (PrimTy.dflt p))).map (fun o => (⟨o.st.drop .refl,o.ext⟩ : Out C s.H (.val p :: .val .bool :: Γ))) = _
      rw [branch_run]
      rfl
    · change ((branch i a).run (((s.setLocal ci true).push (t := .val .bool) true).push
        (PrimTy.dflt p))).map (fun o => (⟨o.st.drop .refl,o.ext⟩ : Out C s.H (.val p :: .val .bool :: Γ))) = _
      rw [branch_run]
      rfl
  unfold code
  rw [Prog.run_cons_ok first,Prog.run_cons_ok capture,Prog.run_cons_ok reserve,
    Prog.run_cons_ok selection,Prog.run_nil]
  rfl

def operand {C : Contract} {Γ : Ctx} {p : PrimTy} (ci ca : Idx Γ (.val .bool))
    (i a j b : Idx Γ (.val p)) : DeferredSource.Operand C Γ (.prim p) :=
  ⟨_,code ci ca i a j b,.val (.simple (.local .here))⟩

theorem operand_run {C : Contract} {Γ : Ctx} {p : PrimTy}
    (s : State C Γ) (ci ca : Idx Γ (.val .bool)) (choice : Bool)
    (i a j b : Idx Γ (.val p)) (read : TEnv.get ca s.env = choice) :
    (operand ci ca i a j b).run s =
      .ok (⟨targetAfter s ci choice i a j b,List.prefix_refl _⟩,
        .prim (TEnv.get (if choice then a else b) (TEnv.set ci choice s.env))) := by
  unfold operand DeferredSource.Operand.run
  rw [prefix_run s ci ca choice i a j b read]
  rfl


/-- Initial, compiler-independent value/identity alignment supplies both
reached reads and the entire post-context relation. No desired execution,
branch purity, alias separation or final relation is assumed. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {τ : Source.STy}
    {C : Contract} {Γ : Ctx} {p : PrimTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (σ : Source.STy) → (u : LTy) → Source.Val E.layout σ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (c : Bool), R .bool (.val .bool) v c → v = .bool c)
    (ci ca : Source.Idx srcΓ .bool) (i a j b : Source.Idx srcΓ τ)
    (tci tca : Idx Γ (.val .bool)) (ti ta tj tb : Idx Γ (.val p))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapI : m.slot i = ⟨.val p,ti⟩) (mapA : m.slot a = ⟨.val p,ta⟩)
    (mapJ : m.slot j = ⟨.val p,tj⟩) (mapB : m.slot b = ⟨.val p,tb⟩) :
    let choice : Bool := TEnv.get tca target.env
    let sv := (source.1.set ci (.bool choice)).get (if choice then a else b)
    let tv := TEnv.get (if choice then ta else tb) (TEnv.set tci choice target.env)
    (Source.evalE G F (fuel+3) (.cond (.assign (.local ci) (.local ca))
      (.assign (.local i) (.local a)) (.assign (.local j) (.local b)))).run source =
      (.ok (.val sv),sourceAfter source ci choice i a j b) ∧
    (operand tci tca ti ta tj tb).run target =
      .ok (⟨targetAfter target tci choice ti ta tj tb,List.prefix_refl _⟩,.prim tv) ∧
    R τ (.val p) sv tv ∧
    m.Related R (sourceAfter source ci choice i a j b).1
      (targetAfter target tci choice ti ta tj tb).env := by
  dsimp only
  have read := boolReflect _ _ (ContextMap.value_at m R source.1 target.env aligned ca tca mapCA)
  have reached : m.Related R (source.1.set ci (.bool (TEnv.get tca target.env)))
      (TEnv.set tci (TEnv.get tca target.env) target.env) := by
    have first : m.Related R (source.1.set ci (source.1.get ca))
        (TEnv.set tci (TEnv.get tca target.env) target.env) :=
      ContextMap.related_assign m R source.1 target.env aligned ci ca tci tca mapCI mapCA
    intro σ k
    simpa only [read] using first k
  have selectedWrite : m.slot (if (TEnv.get tca target.env : Bool) = true then i else j) =
      ⟨.val p,if (TEnv.get tca target.env : Bool) = true then ti else tj⟩ := by
    cases c : (TEnv.get tca target.env : Bool)
    · simpa only [c,Bool.false_eq_true,if_false] using mapJ
    · simpa only [c,if_true] using mapI
  have selectedRead : m.slot (if (TEnv.get tca target.env : Bool) = true then a else b) =
      ⟨.val p,if (TEnv.get tca target.env : Bool) = true then ta else tb⟩ := by
    cases c : (TEnv.get tca target.env : Bool)
    · simpa only [c,Bool.false_eq_true,if_false] using mapB
    · simpa only [c,if_true] using mapA
  refine ⟨source_run G F fuel source ci ca _ i a j b read,
    operand_run target tci tca _ ti ta tj tb rfl,
    ContextMap.value_at m R _ _ reached _ _ selectedRead,?_⟩
  exact ContextMap.related_assign m R _ _ reached _ _ _ _ selectedWrite selectedRead

theorem extension {C : Contract} {Γ Δ : Ctx} {p : PrimTy}
    (target : State C Γ) (ci ca : Idx Γ (.val .bool)) (choice : Bool)
    (i a j b : Idx Γ (.val p)) (read : TEnv.get ca target.env = choice)
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((operand ci ca i a j b).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨targetAfter target ci choice i a j b,List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (TEnv.get (if choice then a else b) (TEnv.set ci choice target.env)))) := by
  rw [DeferredSource.Operand.run_wk,operand_run target ci ca choice i a j b read]

theorem untouched {E : Source.Env} {srcΓ : Source.RCtx} {τ : Source.STy}
    {C : Contract} {Γ : Ctx} {p : PrimTy}
    (source : Source.EMState E srcΓ) (target : State C Γ) (choice : Bool)
    (ci : Source.Idx srcΓ .bool) (i a j b : Source.Idx srcΓ τ)
    (tci : Idx Γ (.val .bool)) (ti ta tj tb : Idx Γ (.val p)) :
    (sourceAfter source ci choice i a j b).2 = source.2 ∧
    (targetAfter target tci choice ti ta tj tb).storage = target.storage ∧
    (targetAfter target tci choice ti ta tj tb).heap = target.heap ∧
    (targetAfter target tci choice ti ta tj tb).net = target.net ∧
    (targetAfter target tci choice ti ta tj tb).selfBalance = target.selfBalance ∧
    (targetAfter target tci choice ti ta tj tb).tx = target.tx := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end Solidity.Lowering.V07.ConditionalAssignments
