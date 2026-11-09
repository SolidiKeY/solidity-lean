import Solidity.Backend.InternalFlow.RuntimeFrameV3EmissionUnwind
import Solidity.Backend.InternalFlow.RuntimeFrameCallAgreement
/-! Native export recovery for reached allocating parents. Only successful
source outputs provide environments; failed outcomes have no State. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes AllocatingEmission
abbrev A : RefTy := CountdownWitness.A
theorem recover_export {C : Contract} (σ parent : State C (Parameters A)) (e : σ.H <+: parent.H)
 (k : Nat) (bound : k<W)
 (counter : parent.env.1=countValue k bound)
 (tail : parent.env.2=(TEnv.wk e (Parameters A) σ.env).2)
 (out : Solidity.Out C parent.H (Parameters A))
 (locals : out.st.env=TEnv.wk out.ext (Parameters A) parent.env) :
 ParentPrefixes.sourceAt (AllocatingResume.reexport σ e out).st k bound=out.st := by
 have parentEnv : parent.env=(countValue k bound,(TEnv.wk e (Parameters A) σ.env).2) :=
   Prod.ext counter tail
 have outEnv : out.st.env=(countValue k bound,(TEnv.wk (e.trans out.ext) (Parameters A) σ.env).2) := by
   rw [locals,parentEnv,←TEnv.wk_trans e out.ext (Parameters A) σ.env]
   rfl
 change out.st.withEnv (Δ:=Parameters A)
   (countValue k bound,(TEnv.wk (e.trans out.ext) (Parameters A) σ.env).2)=out.st
 rw [←outEnv]
 rfl
/-- Actual earlier activation, native child call and matching paired return.
Both source witnesses come from genuine prefixes of the same initial Entry.
The full-state equality is derived from native continuation equations, never
from target determinism or merely equal heap lengths. -/
theorem parent {C : Contract} {b lo L frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (base : Nat → Fin W) (before : Machine) (start : Nat)
 (entry : InterfaceV1.Entry (plan b lo F) L b frame F σ base before start)
 (reads : (counter σ).val≤length σ) (n : Nat) (small : n+1≤(counter σ).val) :
 ∃ (ref : HRef σ.H A) (η τ : State C (Parameters A)) (ep : σ.H <+: η.H) (ef : σ.H <+: τ.H)
   (entered mid down last : Machine) (prefixAddresses addresses : Nat → Fin W)
   (out : Solidity.Out C (AllocatingActivation.allocated η).H (Parameters A)),
 TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref ∧
 run (RecursiveIngress.code lo (lo-1)) before=.ok entered 0 ∧
 loopIterN (run (guardCompiled (C:=C) b F).code) (run (AllocatingActivation.code (C:=C) b F lo))
   ((counter σ).val-(n+1)) entered=.inl mid ∧
 StateRepr L b frame F η prefixAddresses mid ∧
 η.env=(countValue (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt),(some (ref.wk ep),())) ∧
 η.H.length=σ.H.length+((counter σ).val-(n+1)) ∧ Heap.Keeps ep σ.heap η.heap ∧
 BaseExtends σ.H base prefixAddresses ∧
 GrowsAllocator b frame (4*((counter σ).val-(n+1))) σ base before η prefixAddresses mid ∧
 loopIterN (run (guardCompiled (C:=C) b F).code) (run (AllocatingActivation.code (C:=C) b F lo))
   (counter σ).val entered=.inl down ∧
 (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body (n+1)) :
   Stmt C (Parameters A) (Parameters A)).run (AllocatingActivation.allocated η)=.ok out ∧
 out.st=ParentPrefixes.sourceAt τ (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt) ∧
 loopIterN (run (PairedUnwind.condition lo (lo-1)))
   (run (Restore.restoreCells lo (Restore.contextCells b (Parameters A)))) (n+1) down=.inl last ∧
 StateRepr L b frame F out.st addresses last ∧
 τ.env=(countValue 0 W_pos,(some (ref.wk ef),())) ∧
 τ.H.length=σ.H.length+(counter σ).val ∧ Heap.Keeps ef σ.heap τ.heap ∧
 last.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (4*(counter σ).val) σ base before out.st addresses last ∧
 last.mem lo=.val (wmod (start+2*((counter σ).val-(n+1)))) ∧
 last.mem b=.val (base ref.id) := by
 obtain ⟨ref,entered,τ,ef,down,addresses,alias,setup,descent,repr,env,size,kept,stack,extended,growth,current,resume,saved,words,bottom,exterior⟩ :=
   EmissionPrefixes.running "allocatingCountdown" σ base before start entry reads (counter σ).val (Nat.le_refl _)
 have callerEnv : σ.env=(countValue (counter σ).val (counter σ).isLt,(some ref,())) :=
   Prod.ext (counter_value σ) (Prod.ext alias (by cases σ.env.2.2;rfl))
 have zeroEnv : τ.env=(countValue 0 W_pos,(some (ref.wk ef),())) := by simpa only [Nat.sub_self] using env
 have zeroCounter : τ.env.1=countValue 0 W_pos := by rw [zeroEnv]
 have zeroAt : ParentPrefixes.sourceAt τ 0 W_pos=τ := by
   change τ.withEnv (Δ:=Parameters A) (countValue 0 W_pos,τ.env.2)=τ
   have data : (countValue 0 W_pos,τ.env.2)=τ.env := by rw [zeroEnv];rfl
   exact (congrArg (fun locals => τ.withEnv (Δ:=Parameters A) locals) data).trans rfl
 let full : Solidity.Out C σ.H (Parameters A) := AllocatingResume.reexport σ ef ⟨τ,List.prefix_refl _⟩
 have fullRun : (InterfaceV1.recursiveSource "allocatingCountdown" AllocatingEmission.args .none AllocatingActivation.step
     ((counter σ).val+1)).run σ=.ok full := by
   have actual := resume 1
   rw [AllocatingActivation.source_zero τ 0 zeroCounter] at actual
   simpa only [Nat.add_comm 1 (counter σ).val,Except.map] using actual
 have fullTail : τ.env.2=(TEnv.wk ef (Parameters A) σ.env).2 := by rw [zeroEnv,callerEnv];rfl
 have recoveredZero : ParentPrefixes.sourceAt full.st 0 W_pos=τ :=
   recover_export σ τ ef 0 W_pos zeroCounter fullTail ⟨τ,List.prefix_refl _⟩
     (TEnv.wk_self (List.prefix_refl τ.H) (Parameters A) τ.env).symm
 have fullView : ParentPrefixes.sourceAt full.st (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt)=
     ParentPrefixes.sourceAt τ (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt) :=
   by
     have recoveredAll := congrArg (fun state => ParentPrefixes.sourceAt state (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt)) recoveredZero
     exact recoveredAll
 obtain ⟨prefixRef,prefixEntry,η,ep,mid,prefixAddresses,prefixAlias,prefixSetup,prefixRun,prefixRepr,prefixEnv,prefixSize,prefixKept,prefixStack,prefixExtended,prefixGrowth,prefixCurrent,prefixResume,prefixSaved,prefixWords,prefixBottom,prefixExterior⟩ :=
   EmissionPrefixes.running "allocatingCountdown" σ base before start entry reads ((counter σ).val-(n+1)) (Nat.sub_le _ _)
 have sameRef : prefixRef=ref := Option.some.inj (prefixAlias.symm.trans alias)
 subst prefixRef
 have sameEntry : prefixEntry=entered := (Evm.Out.ok.inj (prefixSetup.symm.trans setup)).1
 subst prefixEntry
 have arithmetic : (counter σ).val-((counter σ).val-(n+1))=n+1 := by omega
 have ancestorEnv : η.env=(countValue (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt),(some (ref.wk ep),())) := by
   simpa only [arithmetic] using prefixEnv
 have ancestorCounter : η.env.1=countValue (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt) := by rw [ancestorEnv]
 have ancestorAlias : η.env.2.1=some (ref.wk ep) := by rw [ancestorEnv]
 have ancestorReads : n+1≤η.heap.len (ref.wk ep) .dyn := by
   rw [prefixKept.len ref .dyn,←length_of_alias σ ref alias]
   omega
 obtain ⟨output,sourceOutput,grown,locals,contents⟩ := AllocatingSource.success (n+2) η (n+1)
   (Nat.lt_of_le_of_lt small (counter σ).isLt) (ref.wk ep) ancestorCounter ancestorAlias ancestorReads (by omega)
 have ancestorTail : η.env.2=(TEnv.wk ep (Parameters A) σ.env).2 := by rw [ancestorEnv,callerEnv];rfl
 have recovered := recover_export σ η ep (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt)
   ancestorCounter ancestorTail output locals
 have fromAncestor : (InterfaceV1.recursiveSource "allocatingCountdown" AllocatingEmission.args .none AllocatingActivation.step
     ((counter σ).val+1)).run σ=.ok (AllocatingResume.reexport σ ep output) := by
   have actual := prefixResume (n+2)
   rw [sourceOutput] at actual
   have index : n+2+((counter σ).val-(n+1))=(counter σ).val+1 := by omega
   simpa only [index,Except.map] using actual
 have sameExport : AllocatingResume.reexport σ ep output=full :=
   Except.ok.inj (fromAncestor.symm.trans fullRun)
 rw [sameExport] at recovered
 have sourceView : output.st=ParentPrefixes.sourceAt τ (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt) :=
   recovered.symm.trans fullView
 have positive := AllocatingActivation.source_positive η (n+1) n (Nat.lt_of_le_of_lt small (counter σ).isLt)
   (ref.wk ep) ancestorCounter ancestorAlias (by omega)
 rw [positive] at sourceOutput
 cases native : (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body (n+1)) :
     Stmt C (Parameters A) (Parameters A)).run (AllocatingActivation.allocated η) with
 | error halt => rw [native] at sourceOutput;cases sourceOutput
 | ok out =>
   rw [native] at sourceOutput
   have same : output=(⟨out.st,(AllocatingActivation.extension η).trans out.ext⟩ : Solidity.Out C η.H (Parameters A)) :=
     (Except.ok.inj sourceOutput).symm
   have outputView : out.st=ParentPrefixes.sourceAt τ (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt) :=
     (congrArg (fun value : Solidity.Out C η.H (Parameters A) => value.st) same).symm.trans sourceView
   obtain ⟨reachedRef,reachedAlias,reachedWord⟩ := repr.pointers (.there .here)
   have reachedAlias' : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) τ.env=some (ref.wk ef) := by rw [zeroEnv];rfl
   have sameReached : reachedRef=ref.wk ef := Option.some.inj (reachedAlias.symm.trans reachedAlias')
   subst reachedRef
   have reference : down.mem b=.val (base ref.id) := reachedWord.trans (congrArg Word.val (extended ref))
   have parentInput : StateRepr L b frame F
       (ParentPrefixes.sourceAt τ ((counter σ).val-(counter σ).val) (by omega)) addresses down := by
     simpa only [Nat.sub_self,zeroAt] using repr
   have savedHere : ∀ j,j<(counter σ).val → down.mem (start+2*j)=down.mem b ∧
       down.mem (start+2*j+1)=.val (wmod ((counter σ).val-j)) := by
     intro j bound
     exact ⟨(saved j bound).1.trans reference.symm,(saved j bound).2⟩
   obtain ⟨workspace,pointerBelow,pointerBefore,bottomAbove,bottomBefore,reserve,fits⟩ := entry_bounds entry reads
   obtain ⟨last,unwinding,parentRepr,parentStack,parentCursor,parentRef,parentGrowth,high,outside⟩ :=
     ParentPrefixes.running_prefix τ addresses (counter σ).val (n+1) (counter σ).val small (Nat.le_refl _) (counter σ).isLt
       down parentInput lo lo (lo-1) start (by omega) (Nat.le_refl _) pointerBelow entry.payloadAbove pointerBefore
         (by omega) bottomBefore (by omega) fits current bottom savedHere
   have returnedRepr : StateRepr L b frame F out.st addresses last := by
     rw [outputView]
     simpa only [Nat.sub_self,Nat.zero_add] using parentRepr
   have returnedGrowth : GrowsAllocator b frame 0 τ addresses down out.st addresses last := by
     rw [outputView]
     simpa only [Nat.sub_self,Nat.zero_add,zeroAt] using parentGrowth
   refine ⟨ref,η,τ,ep,ef,entered,mid,down,last,prefixAddresses,addresses,out,alias,setup,prefixRun,prefixRepr,ancestorEnv,prefixSize,prefixKept,prefixExtended,prefixGrowth,
     descent,native,outputView,unwinding,returnedRepr,zeroEnv,size,kept,parentStack.trans stack,extended,?_,parentCursor,parentRef.trans reference⟩
   simpa only [Nat.add_zero] using growth.comp returnedGrowth

namespace Checks
open CountdownWitness

/-- The native parent is recovered at both positive horizons of the SAME
populated Entry. Its own argument evaluation and successful call are outputs,
and its whole returned state is represented by the existing target witness. -/
theorem available (n : Nat) (small : n+1≤2) :
 ∃ (η : State P.C (Parameters A)) (ep : callee.H <+: η.H)
   (mid : Machine) (prefixAddresses addresses : Nat → Fin W)
   (out : Solidity.Out P.C (AllocatingActivation.allocated η).H (Parameters A)),
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code) (run (AllocatingActivation.code (C:=P.C) 2 F 8))
   (2-(n+1)) ParentPrefixes.Checks.input=.inl mid ∧
 StateRepr 1 2 16 F η prefixAddresses mid ∧ η.H.length=2+(2-(n+1)) ∧
 Heap.Keeps ep callee.heap η.heap ∧
 η.env=(countValue (n+1) (by have h:2<W:=(by decide);omega),(some (P.r0.wk ep),())) ∧
 (nextArgs A rfl).evalT (AllocatingActivation.allocated η)=
   .ok (countValue n (by have h:2<W:=(by decide);omega),(some ((P.r0.wk ep).wk (AllocatingActivation.extension η)),())) ∧
 (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body (n+1)) :
   Stmt P.C (Parameters A) (Parameters A)).run (AllocatingActivation.allocated η)=.ok out ∧
 StateRepr 1 2 16 F out.st addresses (EmissionUnwind.Checks.machine (n+1) small) ∧
 out.st.H.length=4 ∧
 (((TEnv.get (.here : Idx (Parameters A) (.val .uint)) out.st.env).val),
   (TEnv.get (.there .here : Idx (Parameters A) (.mem A)) out.st.env).map HRef.id)=(((n+1:Nat):Int),some 0) ∧
 Heap.Keeps (ep.trans ((AllocatingActivation.extension η).trans out.ext)) callee.heap out.st.heap ∧
 BaseExtends callee.H P.base addresses ∧
 GrowsAllocator 2 16 8 callee P.base EmissionPrefixes.Checks.before out.st addresses (EmissionUnwind.Checks.machine (n+1) small) ∧
 ((EmissionUnwind.Checks.machine (n+1) small).stack,
 [(EmissionUnwind.Checks.machine (n+1) small).mem 0,(EmissionUnwind.Checks.machine (n+1) small).mem 1,
 (EmissionUnwind.Checks.machine (n+1) small).mem 2,(EmissionUnwind.Checks.machine (n+1) small).mem 3,
 (EmissionUnwind.Checks.machine (n+1) small).mem 7,(EmissionUnwind.Checks.machine (n+1) small).mem 8,
 (EmissionUnwind.Checks.machine (n+1) small).mem 9,(EmissionUnwind.Checks.machine (n+1) small).mem 10,
 (EmissionUnwind.Checks.machine (n+1) small).mem 11,(EmissionUnwind.Checks.machine (n+1) small).mem 12,
 (EmissionUnwind.Checks.machine (n+1) small).mem 13,(EmissionUnwind.Checks.machine (n+1) small).mem 16,
 (EmissionUnwind.Checks.machine (n+1) small).mem 17,(EmissionUnwind.Checks.machine (n+1) small).mem 18,
 (EmissionUnwind.Checks.machine (n+1) small).mem 20,(EmissionUnwind.Checks.machine (n+1) small).mem 21])=
 ([w[77]],[w[30],w[16],w[16],.val (wmod (n+1)),w[10],.val (wmod (10+2*(2-(n+1)))),w[99],
 w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]) := by
 have actual := parent callee P.base EmissionPrefixes.Checks.before 10 AllocatingEmission.Checks.entry
   (by rw [AllocatingEmission.Checks.counter_two,AllocatingEmission.Checks.length_two];decide) n
   (by rw [AllocatingEmission.Checks.counter_two];exact small)
 simp only [AllocatingEmission.Checks.counter_two] at actual
 obtain ⟨ref,η,τ,ep,ef,entered,mid,down,last,prefixAddresses,addresses,out,alias,setup,prefixRun,prefixRepr,ancestorEnv,prefixSize,prefixKept,prefixExtended,prefixGrowth,descent,native,outputView,unwinding,represented,zeroEnv,size,kept,stack,extended,growth,cursor,reference⟩ := actual
 have sameRef : ref=P.r0 := Option.some.inj alias.symm
 subst ref
 have sameEntry : entered=ParentPrefixes.Checks.input :=
   (Evm.Out.ok.inj (setup.symm.trans EmissionPrefixes.Checks.setup)).1
 subst entered
 have sameDown : down=EmissionPrefixes.Checks.machine 2 (by decide) :=
   Sum.inl.inj (descent.symm.trans (EmissionPrefixes.Checks.specification 2 (by decide)).1)
 subst down
 have known := (EmissionUnwind.Checks.horizons (n+1) small).choose_spec.choose_spec.choose_spec.choose_spec
 rcases known with ⟨knownRun,knownEnv,knownRepr,knownSize,knownKept,knownExtended,knownGrowth,snapshot⟩
 have sameLast : last=EmissionUnwind.Checks.machine (n+1) small := Sum.inl.inj (unwinding.symm.trans knownRun)
 subst last
 have parameters := AllocatingActivation.allocated_parameters η n (by have h:2<W:=(by decide);omega) (P.r0.wk ep)
   (by rw [ancestorEnv];rfl) (by rw [ancestorEnv];rfl)
 have args := next_eval rfl (AllocatingActivation.allocated η) n (by have h:2<W:=(by decide);omega)
   ((P.r0.wk ep).wk (AllocatingActivation.extension η)) parameters.1 parameters.2
 have sizeOut : out.st.H.length=4 := by rw [outputView];exact size
 have bindings : (((TEnv.get (.here : Idx (Parameters A) (.val .uint)) out.st.env).val),
     (TEnv.get (.there .here : Idx (Parameters A) (.mem A)) out.st.env).map HRef.id)=(((n+1:Nat):Int),some 0) := by
   rw [outputView]
   change (((countValue (n+1) _).val),(TEnv.get (.there .here : Idx (Parameters A) (.mem A)) τ.env).map HRef.id)=_
   rw [zeroEnv]
   rfl
 have oldHeap : Heap.Keeps (ep.trans ((AllocatingActivation.extension η).trans out.ext)) callee.heap out.st.heap := by
   intro R r
   have transfer : ∀ (state : State P.C (Parameters A)) (e : callee.H <+: state.H),
       state=ParentPrefixes.sourceAt τ (n+1) (by have h:2<W:=(by decide);omega) →
       Heap.Keeps e callee.heap state.heap := by
     intro state e same
     cases same
     exact kept
   exact transfer out.st (ep.trans ((AllocatingActivation.extension η).trans out.ext)) outputView r
 exact ⟨η,ep,mid,prefixAddresses,addresses,out,prefixRun,prefixRepr,prefixSize,prefixKept,ancestorEnv,args,native,
   represented,sizeOut,bindings,oldHeap,extended,growth,snapshot⟩

noncomputable def ancestor (n : Nat) (small : n+1≤2) : State P.C (Parameters A) :=
 (available n small).choose
noncomputable def extension (n : Nat) (small : n+1≤2) : callee.H <+: (ancestor n small).H :=
 (available n small).choose_spec.choose
noncomputable def output (n : Nat) (small : n+1≤2) :
 Solidity.Out P.C (AllocatingActivation.allocated (ancestor n small)).H (Parameters A) :=
 (available n small).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- Source projections of the actual witnessed native call, not a second run. -/
theorem source_facts (n : Nat) (small : n+1≤2) :
 Heap.Keeps (extension n small) callee.heap (ancestor n small).heap ∧
 (nextArgs A rfl).evalT (AllocatingActivation.allocated (ancestor n small))=
   .ok (countValue n (by have h:2<W:=(by decide);omega),
     (some ((P.r0.wk (extension n small)).wk (AllocatingActivation.extension (ancestor n small))),())) ∧
 (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body (n+1)) :
   Stmt P.C (Parameters A) (Parameters A)).run (AllocatingActivation.allocated (ancestor n small))=.ok (output n small) ∧
 (output n small).st.H.length=4 ∧
 (((TEnv.get (.here : Idx (Parameters A) (.val .uint)) (output n small).st.env).val),
   (TEnv.get (.there .here : Idx (Parameters A) (.mem A)) (output n small).st.env).map HRef.id)=(((n+1:Nat):Int),some 0) ∧
 Heap.Keeps ((extension n small).trans ((AllocatingActivation.extension (ancestor n small)).trans (output n small).ext))
   callee.heap (output n small).st.heap := by
 have specification := (available n small).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
 rcases specification with ⟨prefixRun,prefixRepr,prefixSize,prefixKept,env,args,native,repr,size,bindings,kept,extended,growth,snapshot⟩
 exact ⟨prefixKept,args,native,size,bindings,kept⟩

/-- Full ordered contents of both distinct older objects in the ACTUAL native
parent result. Initial reads reuse the existing checked source observations. -/
theorem source_objects (n : Nat) (small : n+1≤2) :
 let e := (extension n small).trans ((AllocatingActivation.extension (ancestor n small)).trans (output n small).ext)
 (output n small).st.heap.len (P.r0.wk e) .dyn=2 ∧
 (output n small).st.heap.readAddr (.index (P.r0.wk e) .dyn (countValue 0 W_pos))=some (P.uint 7 (by decide)) ∧
 (output n small).st.heap.readAddr (.index (P.r0.wk e) .dyn (countValue 1 (by decide)))=some (P.uint 9 (by decide)) ∧
 (output n small).st.heap.len (Evm.Memory.CompileExamples.r1.wk e) .dyn=1 ∧
 (output n small).st.heap.readAddr (.index (Evm.Memory.CompileExamples.r1.wk e) .dyn (countValue 0 W_pos))=some (P.uint 4 (by decide)) := by
 have kept : Heap.Keeps ((extension n small).trans ((AllocatingActivation.extension (ancestor n small)).trans (output n small).ext))
     callee.heap (output n small).st.heap := (source_facts n small).2.2.2.2.2
 have oldKept : Heap.Keeps AllocatingSource.Checks.returned.ext callee.heap AllocatingSource.Checks.returned.st.heap :=
   AllocatingSource.Checks.specification.2.2.2
 have read7 := oldKept.readAddr (.index P.r0 .dyn (countValue 0 W_pos))
 change AllocatingSource.Checks.returned.st.heap.readAddr (.index (P.r0.wk AllocatingSource.Checks.returned.ext) .dyn (countValue 0 W_pos))=
   (callee.heap.readAddr (.index P.r0 .dyn (countValue 0 W_pos))).map id at read7
 rw [Option.map_id] at read7
 have read9 := oldKept.readAddr (.index P.r0 .dyn (countValue 1 (by decide)))
 change AllocatingSource.Checks.returned.st.heap.readAddr (.index (P.r0.wk AllocatingSource.Checks.returned.ext) .dyn (countValue 1 (by decide)))=
   (callee.heap.readAddr (.index P.r0 .dyn (countValue 1 (by decide)))).map id at read9
 rw [Option.map_id] at read9
 have read4 := oldKept.readAddr (.index Evm.Memory.CompileExamples.r1 .dyn (countValue 0 W_pos))
 change AllocatingSource.Checks.returned.st.heap.readAddr (.index (Evm.Memory.CompileExamples.r1.wk AllocatingSource.Checks.returned.ext) .dyn (countValue 0 W_pos))=
   (callee.heap.readAddr (.index Evm.Memory.CompileExamples.r1 .dyn (countValue 0 W_pos))).map id at read4
 rw [Option.map_id] at read4
 have initial7 : callee.heap.readAddr (.index P.r0 .dyn (countValue 0 W_pos))=some (P.uint 7 (by decide)) :=
   read7.symm.trans AllocatingSource.Checks.old_objects.2.1
 have initial9 : callee.heap.readAddr (.index P.r0 .dyn (countValue 1 (by decide)))=some (P.uint 9 (by decide)) :=
   read9.symm.trans AllocatingSource.Checks.old_objects.2.2.1
 have initial4 : callee.heap.readAddr (.index Evm.Memory.CompileExamples.r1 .dyn (countValue 0 W_pos))=some (P.uint 4 (by decide)) :=
   read4.symm.trans AllocatingSource.Checks.old_objects.2.2.2.2
 refine ⟨(kept.len P.r0 .dyn).trans HeapDomain.Checks.length_zero,?_,?_,
   (kept.len Evm.Memory.CompileExamples.r1 .dyn).trans HeapDomain.Checks.length_one,?_⟩
 · have same := kept.readAddr (.index P.r0 .dyn (countValue 0 W_pos))
   rw [initial7] at same
   exact same
 · have same := kept.readAddr (.index P.r0 .dyn (countValue 1 (by decide)))
   rw [initial9] at same
   exact same
 · have same := kept.readAddr (.index Evm.Memory.CompileExamples.r1 .dyn (countValue 0 W_pos))
   rw [initial4] at same
   exact same

theorem not_child_counter (n : Nat) (small : n+1≤2) :
 (TEnv.get (.here : Idx (Parameters A) (.val .uint)) (output n small).st.env).val≠(n:Int) := by
 have bindings := (source_facts n small).2.2.2.2.1
 have scalar := congrArg (fun pair : Int × Option Nat => pair.1) bindings
 change (TEnv.get (.here : Idx (Parameters A) (.val .uint)) (output n small).st.env).val=((n+1:Nat):Int) at scalar
 rw [scalar]
 omega

theorem wrong_alias (n : Nat) (small : n+1≤2) :
 (TEnv.get (.there .here : Idx (Parameters A) (.mem A)) (output n small).st.env).map HRef.id≠some 1 := by
 have bindings := (source_facts n small).2.2.2.2.1
 have reference := congrArg (fun pair : Int × Option Nat => pair.2) bindings
 change (TEnv.get (.there .here : Idx (Parameters A) (.mem A)) (output n small).st.env).map HRef.id=some 0 at reference
 rw [reference]
 decide

theorem wrong_contents (n : Nat) (small : n+1≤2) :
 let e := (extension n small).trans ((AllocatingActivation.extension (ancestor n small)).trans (output n small).ext)
 (output n small).st.heap.readAddr (.index (P.r0.wk e) .dyn (countValue 0 W_pos))≠some (P.uint 9 (by decide)) := by
 dsimp only
 rw [(source_objects n small).2.1]
 intro same
 have values := congrArg (fun v : PrimTy.uint.Denote => v.val) (Option.some.inj same)
 change (7:Int)=9 at values
 omega

theorem omitted_allocation (n : Nat) (small : n+1≤2) : (output n small).st.H.length≠3 := by
 rw [(source_facts n small).2.2.2.1]
 decide

/-- The actual child call with one less quotation exhausts, using the real
ancestor heap and actual arguments. It is not relabeled bare revert. -/
theorem shallow (n : Nat) (small : n+1≤2) :
 (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body n) :
   Stmt P.C (Parameters A) (Parameters A)).run (AllocatingActivation.allocated (ancestor n small))=.error .exhausted ∧
 (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body n) :
   Stmt P.C (Parameters A) (Parameters A)).run (AllocatingActivation.allocated (ancestor n small))≠.error .revert := by
 have facts := source_facts n small
 have ancestorKept : Heap.Keeps (extension n small) callee.heap (ancestor n small).heap := facts.1
 have preserved : Heap.Keeps (AllocatingActivation.extension (ancestor n small)) (ancestor n small).heap
     (AllocatingActivation.allocated (ancestor n small)).heap :=
   Heap.keeps_alloc (ancestor n small).heap (AllocatingActivation.object (ancestor n small))
 have reads : n≤(AllocatingActivation.allocated (ancestor n small)).heap.len
     ((P.r0.wk (extension n small)).wk (AllocatingActivation.extension (ancestor n small))) .dyn := by
   rw [preserved.len (P.r0.wk (extension n small)) .dyn,ancestorKept.len P.r0 .dyn,HeapDomain.Checks.length_zero]
   omega
 have actual :
     (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body n) :
       Stmt P.C (Parameters A) (Parameters A)).run (AllocatingActivation.allocated (ancestor n small))=.error .exhausted :=
   AllocatingSource.call_exhaustion "allocatingCountdown" (nextArgs A rfl) n
     (AllocatingActivation.allocated (ancestor n small)) n (by have h:2<W:=(by decide);omega)
     ((P.r0.wk (extension n small)).wk (AllocatingActivation.extension (ancestor n small))) facts.2.1 reads (Nat.le_refl _)
 refine ⟨actual,?_⟩
 rw [actual]
 intro bad
 cases bad

theorem successful_not_revert (n : Nat) (small : n+1≤2) :
 (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body (n+1)) :
   Stmt P.C (Parameters A) (Parameters A)).run (AllocatingActivation.allocated (ancestor n small))≠.error .revert := by
 rw [(source_facts n small).2.2.1]
 intro bad
 cases bad

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind
