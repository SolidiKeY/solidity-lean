import Solidity.Semantics.Panic.Run

namespace Solidity.Semantics.Panic.Run

variable {C : Contract} {Γ Δ Ξ : Ctx}

/-- Empty programs retain the complete input state. -/
theorem program_nil (σ : State C Γ) : program .nil σ = .ok ⟨σ, List.prefix_refl _⟩ := rfl

/-- Every halt, including exhaustion and divergence, stops the remaining program. -/
theorem program_cons_error (s : Stmt C Γ Δ) (tail : Prog C Δ Ξ)
    (σ : State C Γ) (halt : Halt Raised) (h : stmt s σ = .error halt) :
    program (.cons s tail) σ = .error halt := seq_error _ _ σ halt h

theorem program_cons_ok (s : Stmt C Γ Δ) (tail : Prog C Δ Ξ)
    (σ : State C Γ) (o : Out C σ.H Δ) (h : stmt s σ = .ok o) :
    program (.cons s tail) σ = (program tail o.st).map (fun o' => ⟨o'.st, o.ext.trans o'.ext⟩) := by
  simp only [program, seq, h]

theorem stmt_block_error (body : Prog C Γ Δ) (σ : State C Γ)
    (halt : Halt Raised) (h : program body σ = .error halt) :
    stmt (.block body) σ = .error halt := by
  simp only [stmt, block, h]
  rfl

/-- An entered loop propagates the actual body's complete halt. -/
theorem stmt_loop_error (ann : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (σ : State C Γ) (halt : Halt Raised) (hc : value σ c = .ok true)
    (hb : program body σ = .error halt) : stmt (.loop ann c body) σ = .error halt := by
  change loop c body.ext (program body) σ = .error halt
  unfold loop
  apply Loop.run_body_error
  · exact hc
  · simp only [hb]
    rfl

theorem stmt_call_error {ps rs : Ctx} (name : Name) (as : Args C Γ ps)
    (ret : CallRet Γ rs Δ) (body : Prog C (rs ++ ps) Ξ) (σ : State C Γ)
    (a : TEnv C σ.H ps) (halt : Halt Raised) (ha : args σ as = .ok a)
    (hb : program body (ret.enterT (σ.withEnv a)).st = .error halt) :
    stmt (.call name as ret body) σ = .error halt := call_error _ _ _ _ σ a halt ha hb

theorem stmt_callRec_error {ps rs : Ctx} (name : Name) (depth : Nat) (as : Args C Γ ps)
    (ret : CallRet Γ rs Δ) (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) (σ : State C Γ)
    (a : TEnv C σ.H ps) (halt : Halt Raised) (ha : args σ as = .ok a)
    (hb : program (body ()) (ret.enterT (σ.withEnv a)).st = .error halt) :
    stmt (.callRec name depth as ret body) σ = .error halt := call_error _ _ _ _ σ a halt ha hb

/-- The full statement entry point retains the actual assertion producer witness. -/
theorem stmt_assert_false (c : Val C Γ .bool) (σ : State C Γ) (h : value σ c = .ok false) :
    stmt (.assert c) σ = .error (.intrinsic .assert
      (Raised.ofOrigin (.assertion false) .assertion rfl)) := assert_false c σ h

/-- A callee's false assertion cannot be replaced by the caller's oracle code. -/
theorem call_assert_false {ps rs : Ctx} (as : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (σ : State C Γ) (a : TEnv C σ.H ps) (ha : args σ as = .ok a) :
    call as ret .refl (program (.cons (.assert (.simple (.bool false))) .nil)) σ =
      .error (.intrinsic .assert (Raised.ofOrigin (.assertion false) .assertion rfl)) := by
  apply call_error _ _ _ _ σ a _ ha
  rfl

/-- Self-catch binds the executed callee's code, without consulting an oracle. -/
theorem stmt_tryCall_self_panic {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx}
    (ext : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁)
    (err : Prog C Γ Γ₂) (binder : CodeBinder κ) (pnc : Prog C (κ ++ Γ) Γ₃)
    (other : Prog C Γ Γ₄) (as : Args C Γ ps) (body : Prog C (ρ ++ ps) Γf)
    (σ : State C Γ) (code : Code) (origin : Raised)
    (nonzero : (ext.addr.evalT σ).1 ≠ 0) (self : (ext.addr.evalT σ).1 = σ.tx.selfAddress.1)
    (failed : call as (.rets rets.toRet) body.ext (program body) σ = .error (.intrinsic code origin)) :
    stmt (.tryCall ext rets ok err binder pnc other as body true) σ =
      (program pnc (σ.withEnv (TEnv.append κ (binder.decodeT (H := σ.H) (codeWord code)) σ.env))).map
        (fun o => ⟨o.st.drop ((Ext.append Γ κ).trans pnc.ext), o.ext⟩) :=
  tryCall_self_failure ext rets ok.ext (program ok) err.ext (program err) binder
    pnc.ext (program pnc) other.ext (program other) as body.ext (program body) σ
    (.intrinsic code origin) nonzero self failed

/-- Assertion code 1 reaches the self-call handler regardless of oracle entries. -/
theorem stmt_tryCall_assert_false {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps : Ctx}
    (ext : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁)
    (err : Prog C Γ Γ₂) (binder : CodeBinder κ) (pnc : Prog C (κ ++ Γ) Γ₃)
    (other : Prog C Γ Γ₄) (as : Args C Γ ps) (σ : State C Γ) (a : TEnv C σ.H ps)
    (nonzero : (ext.addr.evalT σ).1 ≠ 0) (self : (ext.addr.evalT σ).1 = σ.tx.selfAddress.1)
    (ha : args σ as = .ok a) :
    stmt (.tryCall ext rets ok err binder pnc other as
      (.cons (.assert (.simple (.bool false))) .nil) true) σ =
      (program pnc (σ.withEnv (TEnv.append κ (binder.decodeT (H := σ.H) (codeWord .assert)) σ.env))).map
        (fun o => ⟨o.st.drop ((Ext.append Γ κ).trans pnc.ext), o.ext⟩) :=
  stmt_tryCall_self_panic ext rets ok err binder pnc other as _ σ .assert _ nonzero self
    (call_assert_false as (.rets rets.toRet) σ a ha)

/-- Exhaustion and divergence escape self-catch; no handler runs. -/
theorem stmt_tryCall_self_resource {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx}
    (ext : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁)
    (err : Prog C Γ Γ₂) (binder : CodeBinder κ) (pnc : Prog C (κ ++ Γ) Γ₃)
    (other : Prog C Γ Γ₄) (as : Args C Γ ps) (body : Prog C (ρ ++ ps) Γf)
    (σ : State C Γ) (halt : Halt Raised) (resource : halt = .exhausted ∨ halt = .diverge)
    (nonzero : (ext.addr.evalT σ).1 ≠ 0) (self : (ext.addr.evalT σ).1 = σ.tx.selfAddress.1)
    (failed : call as (.rets rets.toRet) body.ext (program body) σ = .error halt) :
    stmt (.tryCall ext rets ok err binder pnc other as body true) σ = .error halt := by
  change tryCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
  rw [tryCall_self_failure ext rets ok.ext (program ok) err.ext (program err) binder
    pnc.ext (program pnc) other.ext (program other) as body.ext (program body) σ halt nonzero self failed]
  rcases resource with rfl | rfl <;> rfl

/-- Errors while constructing explicit revert bytes retain their full payload. -/
theorem revertData_error (parts : List (RevPart C Γ)) (σ : State C Γ) (halt : Halt Raised)
    (failed : parts.mapM (revPart σ) = .error halt) : revertData parts σ = .error halt := by
  simp only [revertData, failed]
  rfl

/-- Catch-data cannot convert resource failure into catchable bytes. -/
theorem catchData_error {ρ ps Γf Γ₁ : Ctx} (ext : ExtCall C Γ) (rets : Binders ρ)
    (as : Args C Γ ps) (callee : Prog C (ρ ++ ps) Γf) (self : Bool) (kind : CatchKind)
    (handler : Prog C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ) (halt : Halt Raised)
    (failed : catchBytes ext rets as callee.ext (program callee) self σ = .error halt) :
    catchData ext rets as callee.ext (program callee) self kind handler.ext (program handler) σ =
      .error halt := by
  simp only [catchData, failed]
  rfl

end Solidity.Semantics.Panic.Run
