import Solidity.Semantics.Panic.Run.Contracts

namespace Solidity.Semantics.Panic.RunTests

private def C : Contract := { vars := [] }
private abbrev Γ : Ctx := [.val .uint]
private def ext : ExtCall C Γ :=
  ⟨.lit 1 (by decide), "callee", [], .call, .unknown⟩
private def initial : State C Γ :=
  let base := (State.init C).push (t := .val .uint) ⟨0, by decide⟩
  { base with tx := {
      selfAddress := ⟨1, by decide⟩
      ext := [(ext.keyT base, .panic ⟨17, by decide⟩)] } }
private def handler : Prog C (.val .uint :: Γ) (.val .uint :: Γ) :=
  .cons (.assignLocal (.there .here) (.simple (.local .here))) .nil
private def caught (body : Prog C [] []) (self : Bool := true) : Stmt C Γ Γ :=
  .tryCall ext .nil .nil .nil (.some (.user "code")) handler .nil .nil body self
private def assertion : Prog C [] [] := .cons (.assert (.simple (.bool false))) .nil

/- Actual self assertion binds 1; unchanged V1 binds the oracle's 17. -/
#guard (match Run.stmt (caught assertion) initial with
  | .ok o => (TEnv.get .here o.st.env).val == 1
  | _ => false)
#guard (match (caught assertion).runR initial with
  | .ok o => (TEnv.get .here o.st.env).val == 17
  | _ => false)

/- Resource failure is not consumed by the available self-call handlers. -/
#guard (match Run.stmt (caught (.cons .assumeFalse .nil)) initial with
  | .error .exhausted => true
  | _ => false)

/- External calls retain oracle outcomes rather than running the self body. -/
#guard (match Run.stmt (caught assertion false) initial with
  | .ok o => (TEnv.get .here o.st.env).val == 17
  | _ => false)

/- Full loop execution retains exhaustion from its entered body. -/
#guard (match Run.stmt (.loop .auto (.simple (.bool true)) (.cons .assumeFalse .nil)) initial with
  | .error .exhausted => true
  | _ => false)
#guard (match Run.stmt (.loop .auto (.simple (.bool false)) (.cons .assumeFalse .nil)) initial with
  | .ok _ => true
  | _ => false)

/- Catch-data uses the actual assertion bytes and allocates its bound literal. -/
#guard (match Run.catchBytes ext .nil .nil .refl (Run.program assertion) true initial with
  | .ok bs => bs == Semantics.encodePanic 1
  | _ => false)
#guard (match Run.stmt (.catchData ext .nil .nil assertion true .raw (.user "data") .nil) initial with
  | .ok _ => true
  | _ => false)

/-- Complete programs preserve a leading halt and skip their continuation. -/
example {C : Contract} {Γ Δ : Ctx} (σ : State C Γ) (tail : Prog C Γ Δ) :
    Run.program (.cons .assumeFalse tail) σ = .error .exhausted := rfl

/-- A block propagates an assertion's intrinsic code through the statement entry point. -/
example {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    Run.stmt (.block (.cons (.assert (.simple (.bool false))) .nil)) σ =
      .error (.intrinsic .assert (Raised.ofOrigin (.assertion false) .assertion rfl)) := rfl

/-- Explicit local revert bytes remain local, not an invented intrinsic panic. -/
example {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    Run.program (.cons (.revertData [.bytes [1, 2, 3]]) .nil) σ =
      .error (.revertWith [1, 2, 3]) := rfl

/-- A panic while evaluating revert data precedes the explicit revert. -/
example {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    (Run.stmt (.revertData [.word (.binop (p := .uint) .div rfl rfl
      (.simple (.lit 1 (by decide))) (.simple (.lit 0 (by decide))))]) σ).mapError
      (fun h => match h with | .intrinsic c _ => some c.code | _ => none) =
      .error (some 0x12) := rfl

/- Exported proof contracts are checked for availability separately from behavior. -/
#check Run.program_nil
#check Run.program_cons_error
#check Run.program_cons_ok
#check Run.stmt_block_error
#check Run.stmt_loop_error
#check Run.stmt_call_error
#check Run.stmt_callRec_error
#check Run.stmt_assert_false
#check Run.call_assert_false
#check Run.stmt_tryCall_self_panic
#check Run.stmt_tryCall_assert_false
#check Run.stmt_tryCall_self_resource
#check Run.revertData_error
#check Run.catchData_error
#check Run.callReceiver_error
#check Run.pushAfterPrefix_error
#check Run.afterReceiverPrefix_error

end Solidity.Semantics.Panic.RunTests
