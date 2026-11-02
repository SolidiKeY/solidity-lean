import Solidity.Backend.InternalFlow.MemoryCallTransport
/-! Argument-prefix failure over the published typed evaluator. These are source
frame laws, not a target simulation, rollback or allocation-state observation. -/
namespace Solidity.Backend.InternalFlow.CallArgumentPrefix
variable {C : Contract} {Γ ps : Ctx}

theorem scalar_tail {σ : State C Γ} (args : Args C Γ ps) (halt : THalt)
    (failed : args.evalT σ = .error halt) (p : PrimTy) (name : Var) (value : Val C Γ p) :
    (Args.snoc args p name value).evalT σ = .error halt := by
  simp only [Args.evalT,failed,error_bind]

theorem storage_tail {σ : State C Γ} (args : Args C Γ ps) (halt : THalt)
    (failed : args.evalT σ = .error halt) (R : RefTy) (name : Var) (path : SPath C Γ (.ref R)) :
    (Args.snocStorage args R name path).evalT σ = .error halt := by
  simp only [Args.evalT,failed,error_bind]

theorem memory_tail {σ : State C Γ} (args : Args C Γ ps) (halt : THalt)
    (failed : args.evalT σ = .error halt) (R : RefTy) (name : Var) (path : MPath C Γ (.ref R)) :
    (Args.snocMemory args R name path).evalT σ = .error halt := by
  simp only [Args.evalT,failed,error_bind]

/-- Neither default result entry nor an arbitrary private body is reached.
The premise is actual argument evaluation, not the desired call conclusion. -/
theorem call_failure {Δ rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (scope : Ext (rs ++ ps) Γf) (body : TStep C (rs ++ ps) Γf)
    (σ : State C Γ) (halt : THalt) (failed : args.evalT σ = .error halt) :
    TRun.call args ret scope body σ = .error halt := by
  simp only [TRun.call,failed,error_bind]

namespace Checks
open Controls (contract arrayType first nine eleven)
abbrev Caller := MemoryCallTransport.CallerCtx
abbrev Params : Ctx := [.val .uint,.val .uint,.mem arrayType]
def caller : State contract Caller := MemoryCallTransport.caller

def readArgs : Args contract Caller [.val .uint,.mem arrayType] :=
  .snoc (.snocMemory .nil arrayType (.user "old") (.var .here rfl))
    .uint (.user "scalar") (.simple (.local (.there .here)))
def bad : Val contract Caller .uint :=
  .readMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
def failedArgs : Args contract Caller Params := .snoc readArgs .uint (.user "last") bad
def goodArgs : Args contract Caller Params :=
  .snoc readArgs .uint (.user "last") (.simple (.local (.there (.there .here))))
def goodEnv : TEnv contract caller.H Params := (eleven,nine,some first.val,())

theorem evaluated_prefix : readArgs.evalT caller = .ok (nine,some first.val,()) := rfl
private theorem reflectError {α : Type} (r : TRes α) (halt : THalt)
    (h : r.halt? = some halt) : r = .error halt := by
  cases r with
  | ok value => cases h
  | error other => exact congrArg Except.error (Option.some.inj h)
theorem failed_arguments : failedArgs.evalT caller = .error .revert :=
  reflectError _ _ (by decide +kernel)
theorem good_arguments : goodArgs.evalT caller = .ok goodEnv := rfl

def ret : CallRet Caller [.mem arrayType] (.mem arrayType :: Caller) :=
  .mem arrayType (.user "result") rfl rfl
abbrev Enter := [.mem arrayType] ++ Params
abbrev Private := .mem arrayType :: Enter
def body : Prog contract Enter Private :=
  .cons (.declMem arrayType (.user "private") none rfl rfl) .nil

def entry : Out contract caller.H Enter := ret.enterT (caller.withEnv goodEnv)
def grown : Grew contract Enter entry.st.H (MVal · (.ref arrayType)) :=
  entry.st.allocDefaultG arrayType rfl
def bodyOut : Out contract entry.st.H Private := ⟨grown.st.push (some grown.val),grown.ext⟩
def exported : Out contract caller.H (.mem arrayType :: Caller) :=
  ⟨bodyOut.st.withEnv (ret.leaveT
    (TEnv.wk (entry.ext.trans bodyOut.ext) Caller caller.env)
    (TEnv.take [.mem arrayType] (TEnv.drop body.ext bodyOut.st.env))),
    entry.ext.trans bodyOut.ext⟩

theorem body_executes : body.runR entry.st = .ok bodyOut := rfl
theorem successful_call : TRun.call goodArgs ret body.ext body.runR caller = .ok exported :=
  InternalFlow.call_return goodArgs ret body.ext body.runR caller goodEnv good_arguments bodyOut body_executes

theorem failed_call : TRun.call failedArgs ret body.ext body.runR caller = .error .revert :=
  call_failure failedArgs ret body.ext body.runR caller .revert failed_arguments

/-- Actual baseline has both entry and private allocations and ordered exports.
The failing call returns no State; this tuple is ONLY the successful baseline. -/
theorem successful_observations :
    (caller.H.length,entry.st.H.length,bodyOut.st.H.length,
      exported.st.env.1.map HRef.id,exported.st.env.2.1.map HRef.id,
      exported.st.env.2.2.1.1,exported.st.env.2.2.2.1.1) =
    (1,2,3,some 1,some 0,9,11) := by decide +kernel

theorem failed_not_success : TRun.call failedArgs ret body.ext body.runR caller ≠ .ok exported := by
  rw [failed_call]; intro h; cases h

theorem failed_not_panic : TRun.call failedArgs ret body.ext body.runR caller ≠ .error .panic := by
  rw [failed_call]; intro h; cases h

theorem wrong_scalar_order : (goodEnv.1.1,goodEnv.2.1.1) ≠ (9,11) := by decide +kernel

theorem wrong_result_alias : exported.st.env.1.map HRef.id ≠ some 0 := by decide +kernel

/-- A later memory argument is not read after the actual prefix failure. -/
theorem failed_memory_suffix :
    (Args.snocMemory failedArgs arrayType (.user "later") (.var .here rfl)).evalT caller = .error .revert :=
  memory_tail failedArgs .revert failed_arguments arrayType (.user "later") (.var .here rfl)
theorem wrong_private_escape : exported.st.env.1.map HRef.id ≠ some 2 := by decide +kernel

end Checks
end Solidity.Backend.InternalFlow.CallArgumentPrefix
