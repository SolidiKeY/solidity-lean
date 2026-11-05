import Solidity.Backend.InternalFlow.RuntimeFrameV3OrderedArgumentFailure

/-! Successful heap-reading arguments followed by failure of the actual
callee write. Every exposed machine is a successful ENTRY endpoint, never a
state returned by revert. No recursive continuation capacity is required. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.OrderedCalleeFailure
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev A : RefTy := OrderedEffectfulScalar.A

theorem transport {C : Contract} {Γ : Ctx} {L b c frame : Nat} {F : Frag Γ}
 (caller : State C Γ) (reference : Idx Γ (.mem A)) (ref : HRef caller.H A)
 (alias : TEnv.get reference caller.env=some ref) (count : Val C Γ .uint) (value : CompiledVal b F count)
 (n : Nat) (bound : n<W) (evaluated : count.evalT caller=.ok (countValue n bound))
 (failed : caller.heap.writeAddr (.index ref .dyn (countValue 0 W_pos)) EffectfulScalarSource.replacement=none)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F caller base before)
 (disjoint : b+Γ.length≤c) (space : c+3≤frame) :
 (DisjointScalarEntry.args rfl reference count).evalT caller=.ok (countValue n bound,(some ref,())) ∧
 ∃ entered,
 run (DisjointScalarEntry.code b c reference value) before=.ok entered 0 ∧
 StateRepr L c frame (Frag.init (Frame A))
   ((caller.withEnv (Δ:=Parameters A) (countValue n bound,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)) base entered ∧
 StateRepr L b frame F caller base entered ∧ entered.stack=before.stack ∧
 entered.mem c=before.mem (cellOf b reference) ∧ entered.mem (c+1)=.val (⟨n,bound⟩ : Fin W) ∧ entered.mem (c+2)=w[0] ∧
 (∀ x,x≠c → x≠c+1 → x≠c+2 → entered.mem x=before.mem x) ∧
 GrowsAllocator b frame 0 caller base before
   ((caller.withEnv (Δ:=Parameters A) (countValue n bound,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)) base entered ∧
 (∀ suffix,run (OrderedEffectfulScalar.calleeCode (C:=C) c++suffix) entered=.revert) ∧
 (∀ (function : Name) (depth : Nat) (destination : Idx Γ (.val .uint)),
   (OrderedEffectfulScalar.call reference count destination function depth).run caller=.error .revert) ∧
 (∀ (destination : Idx Γ (.val .uint)) (pointer bottom : Nat) (suffix : List Instr),
   run (OrderedEffectfulScalar.code b c reference value destination pointer bottom++suffix) before=.revert) := by
 have expected : (DisjointScalarEntry.args rfl reference count).evalT caller=.ok (countValue n bound,(some ref,())) := by
   simp only [DisjointScalarEntry.args,Args.evalT,MPath.mvalT,alias,evaluated,ok_bind]
   rfl
 obtain ⟨actualRef,entered,arguments,entryRun,childRepr,callerRepr,entryStack,entryRef,entryOutside,entryGrowth⟩ :=
   DisjointScalarEntry.entered rfl caller reference count value n bound evaluated base before repr disjoint space
 have identical : actualRef=ref := Option.some.inj (congrArg (fun env : TEnv C caller.H (Parameters A) => env.2.1)
   (Except.ok.inj (arguments.symm.trans expected)))
 subst actualRef
 let child := (caller.withEnv (Δ:=Parameters A) (countValue n bound,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)
 have counter : entered.mem (c+1)=.val (⟨n,bound⟩ : Fin W) :=
   Restored.value_unique (childRepr.core.vals (.there .here)) (ReprV.uint_of rfl)
 have result : entered.mem (c+2)=w[0] :=
   Restored.value_unique (childRepr.core.vals .here) (ReprV.dflt_zero .uint)
 have bodyRoom : c+frameNeedStmt (EffectfulScalarFailure.statement (C:=C) (.there (.there .here) : Idx (Frame A) (.mem A)))≤frame := by
   change c+3≤frame
   exact space
 have bodyFailure : ∀ suffix,run (OrderedEffectfulScalar.calleeCode (C:=C) c++suffix) entered=.revert := by
   intro suffix
   exact EffectfulScalarFailure.target_suffix child (.there (.there .here)) ref rfl failed base entered childRepr bodyRoom suffix
 refine ⟨expected,entered,entryRun,childRepr,callerRepr,entryStack,entryRef,counter,result,entryOutside,entryGrowth,bodyFailure,?_,?_⟩
 · intro function depth destination
   exact EffectfulScalarFailure.call_failure function (DisjointScalarEntry.args rfl reference count)
     destination depth caller n bound ref expected failed
 · intro destination pointer bottom suffix
   have failedBody := bodyFailure ((ScalarReturn.image (C:=C) c (Frag.init (Parameters A)) pointer bottom ++
     [.mload (c+2),.mstore (cellOf b destination)])++suffix)
   have combined := (run_append_ok entryRun).trans failedBody
   simpa only [OrderedEffectfulScalar.code,List.append_assoc] using combined

namespace Client
open DisjointScalarReturn.Client (Γ F reference)
abbrev C := SameCallInputs.C

def other : Idx Γ (.mem A) := .there (.there (.there .here))
def count : Val C Γ .uint := .readMem (.index .dyn (.var other rfl) (.simple (.lit 0 rfl)))
def value : CompiledVal 1 F count := (Memory.compileVal 1 F count).get (by rfl)
def args := DisjointScalarEntry.args rfl reference count

theorem public_value_root : Memory.compileVal 1 F count=some value := rfl

theorem evaluated : count.evalT SameCallInputs.caller=.ok (countValue 3 (by decide)) := by
 with_unfolding_all rfl

def child : State C (Frame A) :=
 (SameCallInputs.caller.withEnv (Δ:=Parameters A) (countValue 3 (by decide),(some SameCallInputs.fresh,()))).push
   (t:=.val .uint) (PrimTy.dflt .uint)
def entryCode := DisjointScalarEntry.code 1 5 reference value

theorem checked : args.evalT SameCallInputs.caller=.ok (countValue 3 (by decide),(some SameCallInputs.fresh,())) ∧
 ∃ entered,
 run entryCode SameCallInputs.machine=.ok entered 0 ∧
 StateRepr 1 5 16 (Frag.init (Frame A)) child SameCallInputs.addresses entered ∧
 StateRepr 1 1 16 F SameCallInputs.caller SameCallInputs.addresses entered ∧
 entered.stack=SameCallInputs.machine.stack ∧ entered.mem 5=SameCallInputs.machine.mem 2 ∧
 entered.mem 6=w[3] ∧ entered.mem 7=w[0] ∧
 (∀ x,x≠5 → x≠6 → x≠7 → entered.mem x=SameCallInputs.machine.mem x) ∧
 GrowsAllocator 1 16 0 SameCallInputs.caller SameCallInputs.addresses SameCallInputs.machine child SameCallInputs.addresses entered ∧
 (∀ suffix,run (OrderedEffectfulScalar.calleeCode (C:=C) 5++suffix) entered=.revert) ∧
 (∀ (function : Name) (depth : Nat) (destination : Idx Γ (.val .uint)),
   (OrderedEffectfulScalar.call reference count destination function depth).run SameCallInputs.caller=.error .revert) ∧
 (∀ (destination : Idx Γ (.val .uint)) (pointer bottom : Nat) (suffix : List Instr),
   run (OrderedEffectfulScalar.code 1 5 reference value destination pointer bottom++suffix) SameCallInputs.machine=.revert) :=
 transport (c:=5) SameCallInputs.caller reference SameCallInputs.fresh rfl count value 3 (by decide) evaluated
   EffectfulScalarFailure.Client.actual_write_failure SameCallInputs.addresses SameCallInputs.machine
   SameCallInputs.reached.2.2.1 (by decide) (by decide)

noncomputable def entered : Machine := checked.2.choose

theorem entry_specification :
 run entryCode SameCallInputs.machine=.ok entered 0 ∧
 StateRepr 1 5 16 (Frag.init (Frame A)) child SameCallInputs.addresses entered ∧
 StateRepr 1 1 16 F SameCallInputs.caller SameCallInputs.addresses entered ∧
 entered.stack=SameCallInputs.machine.stack ∧ entered.mem 5=SameCallInputs.machine.mem 2 ∧
 entered.mem 6=w[3] ∧ entered.mem 7=w[0] ∧
 (∀ x,x≠5 → x≠6 → x≠7 → entered.mem x=SameCallInputs.machine.mem x) ∧
 GrowsAllocator 1 16 0 SameCallInputs.caller SameCallInputs.addresses SameCallInputs.machine child SameCallInputs.addresses entered ∧
 (∀ suffix,run (OrderedEffectfulScalar.calleeCode (C:=C) 5++suffix) entered=.revert) ∧
 (∀ (function : Name) (depth : Nat) (destination : Idx Γ (.val .uint)),
   (OrderedEffectfulScalar.call reference count destination function depth).run SameCallInputs.caller=.error .revert) ∧
 (∀ (destination : Idx Γ (.val .uint)) (pointer bottom : Nat) (suffix : List Instr),
   run (OrderedEffectfulScalar.code 1 5 reference value destination pointer bottom++suffix) SameCallInputs.machine=.revert) := checked.2.choose_spec


theorem arguments : args.evalT SameCallInputs.caller=.ok (countValue 3 (by decide),(some SameCallInputs.fresh,())) := checked.1

theorem source (depth : Nat) :
 (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalarDistinct" depth).run SameCallInputs.caller=.error .revert :=
 entry_specification.2.2.2.2.2.2.2.2.2.2.1 "orderedScalarDistinct" depth .here

def image : List Instr := OrderedEffectfulScalar.code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8

theorem target_suffix (suffix : List Instr) : run (image++suffix) SameCallInputs.machine=.revert :=
 entry_specification.2.2.2.2.2.2.2.2.2.2.2 .here 9 8 suffix

theorem target : run image SameCallInputs.machine=.revert := by
 simpa only [List.append_nil] using target_suffix []

def program (depth : Nat) : Prog C Γ Γ :=
 .cons SameCallInputs.preparation
   (.cons (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalarDistinct" depth) .nil)

theorem whole_source (depth : Nat) : (program depth).run SameCallInputs.origin=.error .revert := by
 rw [program,Prog.run_cons_ok SameCallInputs.reached.1]
 change (TRun.seq (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalarDistinct" depth).runR
   TRun.nil SameCallInputs.caller).map _=_
 simp only [TRun.seq,show (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalarDistinct" depth).runR
   SameCallInputs.caller=.error .revert from source depth,Except.map]

theorem whole_target : run (SameCallInputs.checked.code++image) SameCallInputs.before=.revert :=
 (run_append_ok SameCallInputs.reached.2.1).trans target

/-- The same reached caller distinguishes failure before entry from failure
    after successful arguments through a different alias. -/
theorem failure_stages :
 (DisjointScalarEntry.args rfl reference OrderedEffectfulScalar.Client.count).evalT SameCallInputs.caller=.error .revert ∧
 args.evalT SameCallInputs.caller=.ok (countValue 3 (by decide),(some SameCallInputs.fresh,())) ∧
 (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalarDistinct" 0).run SameCallInputs.caller=.error .revert :=
 ⟨OrderedArgumentFailure.Client.checked_failure.1,arguments,source 0⟩

theorem not_exhausted :
 (OrderedEffectfulScalar.call reference count (.here : Idx Γ (.val .uint)) "orderedScalarDistinct" 0).run SameCallInputs.caller ≠ .error .exhausted := by
 rw [source]
 intro h
 cases h

theorem not_success (machine : Machine) (cost : Nat) : run image SameCallInputs.machine ≠ .ok machine cost := by
 rw [target]
 intro h
 cases h

/-- Complete successful entry snapshot; the subsequent revert supplies no state. -/
theorem entry_snapshot :
 (entered.stack,(List.range 27).map (fun index => entered.mem index))=
 ([w[77]],[w[27],w[16],w[26],w[2],w[3],w[26],w[3],w[0],w[10],w[10],w[16],w[3],w[16],w[2],w[16],w[1],w[2],w[3],w[9],w[0],w[1],w[4],w[3],w[0],w[0],w[0],w[0]]) := by
 have stack : SameCallInputs.machine.stack=[w[77]] := congrArg Prod.fst SameCallControls.snapshot
 have old0 : SameCallInputs.machine.mem 0=w[27] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[0]?) SameCallControls.snapshot)
 have old1 : SameCallInputs.machine.mem 1=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[1]?) SameCallControls.snapshot)
 have old2 : SameCallInputs.machine.mem 2=w[26] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[2]?) SameCallControls.snapshot)
 have old3 : SameCallInputs.machine.mem 3=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[3]?) SameCallControls.snapshot)
 have old4 : SameCallInputs.machine.mem 4=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[4]?) SameCallControls.snapshot)
 have old8 : SameCallInputs.machine.mem 8=w[10] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[8]?) SameCallControls.snapshot)
 have old9 : SameCallInputs.machine.mem 9=w[10] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[9]?) SameCallControls.snapshot)
 have old10 : SameCallInputs.machine.mem 10=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[10]?) SameCallControls.snapshot)
 have old11 : SameCallInputs.machine.mem 11=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[11]?) SameCallControls.snapshot)
 have old12 : SameCallInputs.machine.mem 12=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[12]?) SameCallControls.snapshot)
 have old13 : SameCallInputs.machine.mem 13=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[13]?) SameCallControls.snapshot)
 have old14 : SameCallInputs.machine.mem 14=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[14]?) SameCallControls.snapshot)
 have old15 : SameCallInputs.machine.mem 15=w[1] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[15]?) SameCallControls.snapshot)
 have old16 : SameCallInputs.machine.mem 16=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[16]?) SameCallControls.snapshot)
 have old17 : SameCallInputs.machine.mem 17=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[17]?) SameCallControls.snapshot)
 have old18 : SameCallInputs.machine.mem 18=w[9] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[18]?) SameCallControls.snapshot)
 have old19 : SameCallInputs.machine.mem 19=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[19]?) SameCallControls.snapshot)
 have old20 : SameCallInputs.machine.mem 20=w[1] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[20]?) SameCallControls.snapshot)
 have old21 : SameCallInputs.machine.mem 21=w[4] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[21]?) SameCallControls.snapshot)
 have old22 : SameCallInputs.machine.mem 22=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[22]?) SameCallControls.snapshot)
 have old23 : SameCallInputs.machine.mem 23=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[23]?) SameCallControls.snapshot)
 have old24 : SameCallInputs.machine.mem 24=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[24]?) SameCallControls.snapshot)
 have old25 : SameCallInputs.machine.mem 25=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[25]?) SameCallControls.snapshot)
 have old26 : SameCallInputs.machine.mem 26=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[26]?) SameCallControls.snapshot)
 have cells : ∀ x,x≠5 → x≠6 → x≠7 → entered.mem x=SameCallInputs.machine.mem x := entry_specification.2.2.2.2.2.2.2.1
 change (entered.stack,[entered.mem 0,entered.mem 1,entered.mem 2,entered.mem 3,entered.mem 4,entered.mem 5,entered.mem 6,entered.mem 7,entered.mem 8,entered.mem 9,entered.mem 10,entered.mem 11,entered.mem 12,entered.mem 13,entered.mem 14,entered.mem 15,entered.mem 16,entered.mem 17,entered.mem 18,entered.mem 19,entered.mem 20,entered.mem 21,entered.mem 22,entered.mem 23,entered.mem 24,entered.mem 25,entered.mem 26])=_
 rw [entry_specification.2.2.2.1,stack,entry_specification.2.2.2.2.1,entry_specification.2.2.2.2.2.1,entry_specification.2.2.2.2.2.2.1]
 rw [cells 0 (by decide) (by decide) (by decide),cells 1 (by decide) (by decide) (by decide),cells 2 (by decide) (by decide) (by decide),cells 3 (by decide) (by decide) (by decide),cells 4 (by decide) (by decide) (by decide),cells 8 (by decide) (by decide) (by decide),cells 9 (by decide) (by decide) (by decide),cells 10 (by decide) (by decide) (by decide),cells 11 (by decide) (by decide) (by decide),cells 12 (by decide) (by decide) (by decide),cells 13 (by decide) (by decide) (by decide),cells 14 (by decide) (by decide) (by decide),cells 15 (by decide) (by decide) (by decide),cells 16 (by decide) (by decide) (by decide),cells 17 (by decide) (by decide) (by decide),cells 18 (by decide) (by decide) (by decide),cells 19 (by decide) (by decide) (by decide),cells 20 (by decide) (by decide) (by decide),cells 21 (by decide) (by decide) (by decide),cells 22 (by decide) (by decide) (by decide),cells 23 (by decide) (by decide) (by decide),cells 24 (by decide) (by decide) (by decide),cells 25 (by decide) (by decide) (by decide),cells 26 (by decide) (by decide) (by decide)]
 rw [old0,old1,old2,old3,old4,old8,old9,old10,old11,old12,old13,old14,old15,old16,old17,old18,old19,old20,old21,old22,old23,old24,old25,old26]

end Client
end Solidity.Backend.InternalFlow.RuntimeFrame.OrderedCalleeFailure
