import Solidity.Backend.InternalFlow.FrameLaws
import Solidity.Backend.InternalFlow.Controls

/-!
# Memory-result calls with entry allocation and body growth

All execution below is the published TRun.call and intrinsic Prog.runR.
Only local/reference transport is claimed; the body may mutate heap contents.
There is no new call evaluator or target-frame simulation.
-/
namespace Solidity.Backend.InternalFlow

/-- Memory result export preserves every typed caller local, weakened along
both the result-entry allocation and the body's actual heap extension. -/
theorem memory_call_caller_reads {C : Contract} {Γ ps Γf : Ctx}
    (R : RefTy) (name : Var) (hd : (Ty.ref R).defaultOkS = true)
    (hm : (Ty.ref R).mapFree = true) (args : Args C Γ ps)
    (scope : Ext ([.mem R] ++ ps) Γf) (body : TStep C ([.mem R] ++ ps) Γf)
    (caller : State C Γ) (arguments : TEnv C caller.H ps)
    (ha : args.evalT caller = .ok arguments)
    (out : Out C ((CallRet.mem (Γ := Γ) R name hd hm).enterT
      (caller.withEnv arguments)).st.H Γf)
    (hb : body ((CallRet.mem (Γ := Γ) R name hd hm).enterT
      (caller.withEnv arguments)).st = .ok out) :
    ∃ final : Out C caller.H (.mem R :: Γ),
      TRun.call args (.mem R name hd hm) scope body caller = .ok final ∧
      TEnv.drop (.push .refl) final.st.env = TEnv.wk final.ext Γ caller.env ∧
      ∀ (t : LTy) (i : Idx Γ t), TEnv.get (.there i) final.st.env =
        LTy.TDenote.wk final.ext t (TEnv.get i caller.env) := by
  refine ⟨_, call_return args (.mem R name hd hm) scope body caller arguments ha out hb, rfl, ?_⟩
  intro t i
  exact TEnv.get_wk _ i caller.env

namespace MemoryCallTransport

open Controls (contract arrayType first seven nine eleven)

abbrev CallerCtx : Ctx := [.mem arrayType, .val .uint, .val .uint]
abbrev Params : Ctx := [.mem arrayType]
abbrev ReturnedCtx : Ctx := [.mem arrayType, .mem arrayType, .val .uint, .val .uint]

def caller : State contract CallerCtx := first.st.withEnv (some first.val, nine, eleven, ())
def args : Args contract CallerCtx Params :=
  .snocMemory .nil arrayType (.user "oldArgument") (.var .here rfl)
def argumentEnv : TEnv contract caller.H Params := (some first.val, ())
def ret : CallRet CallerCtx [.mem arrayType] ReturnedCtx :=
  .mem arrayType (.user "result") rfl rfl

def entry : Out contract caller.H [.mem arrayType, .mem arrayType] :=
  ret.enterT (caller.withEnv argumentEnv)

def body : Prog contract [.mem arrayType, .mem arrayType]
    [.mem arrayType, .mem arrayType, .mem arrayType] :=
  .cons (.declMem arrayType (.user "temporary") none rfl rfl)
    (.cons (.rebindMem (.there .here) (.alias (.var .here rfl))) .nil)

def growth : Grew contract [.mem arrayType, .mem arrayType] entry.st.H
    (MVal · (.ref arrayType)) := entry.st.allocDefaultG arrayType rfl

def bodyOut : Out contract entry.st.H [.mem arrayType, .mem arrayType, .mem arrayType] :=
  ⟨(growth.st.push (t := .mem arrayType) (some growth.val)).setLocal
    (.there .here) (some growth.val), growth.ext⟩

theorem arguments_evaluate : args.evalT caller = .ok argumentEnv := rfl

theorem body_evaluates : body.runR entry.st = .ok bodyOut := rfl

/-- Expected output is typed over the real body heap, with the exact composed
entry/body extension. The temporary is dropped before result extraction. -/
def returned : Out contract caller.H ReturnedCtx :=
  ⟨bodyOut.st.withEnv (ret.leaveT
    (TEnv.wk (entry.ext.trans bodyOut.ext) CallerCtx caller.env)
    (TEnv.take [.mem arrayType] (TEnv.drop (.push .refl) bodyOut.st.env))),
    entry.ext.trans bodyOut.ext⟩

theorem actual_call : TRun.call args ret (.push .refl) body.runR caller = .ok returned :=
  call_return args ret (.push .refl) body.runR caller argumentEnv arguments_evaluate
    bodyOut body_evaluates

/-- The returned body allocation and old caller reference are different and
remain at their exact dependent heap typing. Caller scalar slots are untouched. -/
theorem returned_environment : returned.st.env =
    (some growth.val, some (HRef.wk (entry.ext.trans bodyOut.ext)
      (first.val : HRef caller.H arrayType)), nine, eleven, ()) := rfl

theorem exported_tail : TEnv.drop (.push .refl) returned.st.env =
    TEnv.wk (entry.ext.trans bodyOut.ext) CallerCtx caller.env := rfl

/-- Successively weakening the older reference is identical to transport
along the composed extension. The body argument read is pinned separately. -/
theorem old_reference_composition :
    HRef.wk bodyOut.ext (HRef.wk entry.ext (first.val : HRef caller.H arrayType)) =
      HRef.wk returned.ext (first.val : HRef caller.H arrayType) := rfl

theorem body_old_argument :
    TEnv.get (.there (.there .here)) bodyOut.st.env =
      some (HRef.wk (entry.ext.trans bodyOut.ext) (first.val : HRef caller.H arrayType)) := rfl

theorem entry_and_body_identities :
    (entry.st.env.1.map HRef.id, (growth.val : HRef bodyOut.st.H arrayType).id) = (some 1, 2) := by
  decide +kernel

theorem growth_phases : (caller.H.length, entry.st.H.length, bodyOut.st.H.length) = (1, 2, 3) := by
  decide +kernel

def observe (out : Out contract caller.H ReturnedCtx) : Option Nat × Option Nat × Int × Int × Nat :=
  (out.st.env.1.map HRef.id, out.st.env.2.1.map HRef.id,
    out.st.env.2.2.1.1, out.st.env.2.2.2.1.1, out.st.H.length)

theorem call_observation :
    (TRun.call args ret (.push .refl) body.runR caller).map observe =
      .ok (some 2, some 0, 9, 11, 3) := by
  rw [actual_call]
  apply congrArg Except.ok
  decide +kernel

theorem swapped_fresh_old_rejected :
    (TRun.call args ret (.push .refl) body.runR caller).map observe ≠
      .ok (some 0, some 2, 9, 11, 3) := by
  rw [call_observation]
  intro h
  have impossible : (2 : Nat) = 0 := Option.some.inj (congrArg Prod.fst (Except.ok.inj h))
  cases impossible

/-- Same-typed scalar slots are distinguished in a second actual call with
body allocation and the same older memory local. -/
def scalarRet : CallRet CallerCtx [.val .uint] CallerCtx :=
  .val .uint (.user "scalarResult") (some (.there .here))
def scalarEntry : Out contract caller.H [.val .uint, .mem arrayType] := scalarRet.enterT (caller.withEnv argumentEnv)
def scalarBody : Prog contract [.val .uint, .mem arrayType]
    [.mem arrayType, .val .uint, .mem arrayType] :=
  .cons (.declMem arrayType (.user "temporary") none rfl rfl)
    (.cons (.assignLocal (.there .here) (.simple (.lit 7 rfl))) .nil)
def scalarGrowth : Grew contract [.val .uint, .mem arrayType] scalarEntry.st.H
    (MVal · (.ref arrayType)) := scalarEntry.st.allocDefaultG arrayType rfl
def scalarOut : Out contract scalarEntry.st.H [.mem arrayType, .val .uint, .mem arrayType] :=
  ⟨(scalarGrowth.st.push (t := .mem arrayType) (some scalarGrowth.val)).setLocal
      (.there .here) seven, scalarGrowth.ext⟩
def scalarObserve (out : Out contract caller.H CallerCtx) : Option Nat × Int × Int × Nat :=
  (out.st.env.1.map HRef.id, out.st.env.2.1.1, out.st.env.2.2.1.1, out.st.H.length)

theorem scalar_call_observation :
    (TRun.call args scalarRet (.push .refl) scalarBody.runR caller).map scalarObserve =
      .ok (some 0, 7, 11, 2) := by
  rw [call_return args scalarRet (.push .refl) scalarBody.runR caller
    argumentEnv arguments_evaluate scalarOut (by rfl)]
  apply congrArg Except.ok
  decide +kernel

theorem wrong_same_typed_destination :
    (TRun.call args scalarRet (.push .refl) scalarBody.runR caller).map scalarObserve ≠
      .ok (some 0, 9, 7, 2) := by
  rw [scalar_call_observation]
  intro h
  have impossible : (7 : Int) = 9 := congrArg (fun x => x.2.1) (Except.ok.inj h)
  cases impossible



/-- info: 'Solidity.Backend.InternalFlow.memory_call_caller_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms memory_call_caller_reads
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.arguments_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms arguments_evaluate
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.body_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_evaluates
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.actual_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_call
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.returned_environment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms returned_environment
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.exported_tail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms exported_tail
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.old_reference_composition' depends on axioms: [propext] -/
#guard_msgs in
#print axioms old_reference_composition
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.body_old_argument' depends on axioms: [propext] -/
#guard_msgs in
#print axioms body_old_argument
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.entry_and_body_identities' depends on axioms: [propext] -/
#guard_msgs in
#print axioms entry_and_body_identities
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.growth_phases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms growth_phases
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.call_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms call_observation
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.swapped_fresh_old_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms swapped_fresh_old_rejected
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.scalar_call_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scalar_call_observation
/-- info: 'Solidity.Backend.InternalFlow.MemoryCallTransport.wrong_same_typed_destination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_same_typed_destination

end MemoryCallTransport
end Solidity.Backend.InternalFlow
