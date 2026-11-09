import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveIngress
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3

/-! One allocating recursive image with budgets computed from actual typed
caller data. Universal return and bare-revert obligations are distinct from
approved-domain provenance and public general recursive compilation. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
abbrev A : RefTy := CountdownWitness.A

def counter {C : Contract} (σ : State C (Parameters A)) : Fin W := σ.env.1.word

def length {C : Contract} (σ : State C (Parameters A)) : Nat :=
 match TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env with
 | none => 0
 | some ref => σ.heap.len ref .dyn

def arena {C : Contract} (σ : State C (Parameters A)) : Nat :=
 if (counter σ).val≤length σ then max 3 (2*(counter σ).val) else 3
def cost {C : Contract} (σ : State C (Parameters A)) : Nat := AllocatingOutcome.demand (counter σ).val (length σ)

def args {C : Contract} : Args C (Parameters A) (Parameters A) := entryArgs A rfl (.there .here) .here

def plan {C : Contract} (b lo : Nat) (F : Frag (Parameters A)) : InterfaceV1.Emission C (Parameters A) (Parameters A) :=
 ⟨RecursiveIngress.code lo (lo-1)++AllocatingReturn.image (C:=C) b F lo (lo-1),F,4,lo,lo,arena,cost⟩

theorem counter_value {C : Contract} (σ : State C (Parameters A)) :
 TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (counter σ).val (counter σ).isLt :=
 Subtype.ext (word_val σ.env.1).symm

theorem length_of_alias {C : Contract} (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref) : length σ=σ.heap.len ref .dyn := by
 simp only [length,alias]

theorem arguments {C : Contract} (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref) :
 args.evalT σ=.ok (countValue (counter σ).val (counter σ).isLt,(some ref,())) := by
 simp only [args,entryArgs,Args.evalT,MPath.mvalT,Simple.evalT,Val.evalT,alias,ok_bind,counter_value]
 rfl

theorem source_zero {C : Contract} {Γ : Ctx} (name : Name) (argumentsExpr : Args C Γ (Parameters A))
 (σ : State C Γ) (a : TEnv C σ.H (Parameters A)) (evaluated : argumentsExpr.evalT σ=.ok a) :
 (InterfaceV1.recursiveSource name argumentsExpr .none AllocatingActivation.step 0).run σ=.error .exhausted := by
 change TRun.call argumentsExpr .none .refl (AllocatingActivation.body 0).runR σ=_
 simp only [TRun.call,evaluated,ok_bind,CallRet.enterT]
 change (do
   let out ← (AllocatingActivation.body 0).run (σ.withEnv a)
   pure (exported (ps:=Parameters A) (CallRet.none : CallRet Γ [] Γ) Ext.refl σ a out))=_
 rw [AllocatingActivation.base_exhausts]
 rfl

set_option backward.isDefEq.respectTransparency false in
/-- Real source success excludes a first-read failure, independent of emitter
admission. No source/target agreement premise is used. -/
theorem reads_of_success {C : Contract} (name : Name) (σ : State C (Parameters A))
 (ref : HRef σ.H A) (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (depth : Nat) (out : Solidity.Out C σ.H (Parameters A))
 (actual : (InterfaceV1.recursiveSource name (args (C:=C)) .none AllocatingActivation.step depth).run σ=.ok out) :
 (counter σ).val≤σ.heap.len ref .dyn := by
 by_cases reads : (counter σ).val≤σ.heap.len ref .dyn
 · exact reads
 · have evaluated := arguments σ ref alias
   cases number : (counter σ).val with
   | zero => omega
   | succ n =>
     have bound : n+1<W := by have h:=(counter σ).isLt;omega
     have count : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) bound := by
       simpa only [number] using counter_value σ
     have failed : ArrayProbe.value.evalT σ=.error .revert := (HeapDomain.failure_iff σ n bound ref count alias).2 (by omega)
     have env : σ.env=(countValue (n+1) bound,(some ref,())) := Prod.ext count (Prod.ext alias (by cases σ.env.2.2;rfl))
     have argsKnown : args.evalT σ=.ok (countValue (n+1) bound,(some ref,())) := by simpa only [number] using evaluated
     have bad : ArrayProbe.value.evalT (σ.withEnv (Δ:=Parameters A) (countValue (n+1) bound,(some ref,())))=.error .revert := by
       rw [←env]
       exact failed
     cases depth with
     | zero => rw [source_zero name args σ _ evaluated] at actual;cases actual
     | succ depth =>
       rw [AllocatingFailure.call_failure name args σ depth n bound ref argsKnown bad] at actual
       cases actual

/-- This body's successful environment is already the native no-result export.
The same full Out is therefore a real source call result. -/
theorem body_is_call {C : Contract} (name : Name) (σ : State C (Parameters A))
 (ref : HRef σ.H A) (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : (counter σ).val≤σ.heap.len ref .dyn) (depth : Nat) (out : Solidity.Out C σ.H (Parameters A))
 (actual : (AllocatingActivation.body depth).run σ=.ok out) :
 (InterfaceV1.recursiveSource name (args (C:=C)) .none AllocatingActivation.step depth).run σ=.ok out := by
 have evaluated := arguments σ ref alias
 have env : σ.env=(countValue (counter σ).val (counter σ).isLt,(some ref,())) :=
   Prod.ext (counter_value σ) (Prod.ext alias (by cases σ.env.2.2;rfl))
 have arguments : args.evalT σ=.ok σ.env := evaluated.trans (congrArg Except.ok env.symm)
 have called := call_return args .none .refl (AllocatingActivation.body depth).runR σ σ.env arguments out actual
 have locals := AllocatingResume.successful_env σ (counter σ).val (counter σ).isLt ref (counter_value σ) alias reads depth out actual
 have restored : exported (ps:=Parameters A) (CallRet.none : CallRet (Parameters A) [] (Parameters A)) Ext.refl σ σ.env out=out := by
   cases out with
   | mk st e =>
     change st.env=TEnv.wk e (Parameters A) σ.env at locals
     change (⟨st.withEnv (TEnv.wk e (Parameters A) σ.env),e⟩ : Solidity.Out C σ.H (Parameters A))=⟨st,e⟩
     rw [←locals]
     rfl
 exact called.trans (congrArg Except.ok restored)

theorem entry_bounds {C : Contract} {b lo L frame : Nat} {F : Frag (Parameters A)}
 {σ : State C (Parameters A)} {base : Nat → Fin W} {before : Machine} {start : Nat}
 (entry : InterfaceV1.Entry (plan b lo F) L b frame F σ base before start)
 (reads : (counter σ).val≤length σ) :
 b+4≤lo ∧ lo<frame ∧ lo<start ∧ b+2<lo-1 ∧ lo-1<start ∧
 start+2*(counter σ).val≤frame ∧ start+2*(counter σ).val<W := by
 have workspace := entry.workspace
 have below := entry.pointerBelow
 have lower := entry.payloadAbove
 have reserve := entry.reserve
 have separate := entry.separate
 have fits := entry.noWrap
 change b+4≤lo at workspace
 change lo<frame at below
 change lo≤start at lower
 change start+arena σ≤frame at reserve
 change lo<start ∨ start+arena σ≤lo at separate
 change start+arena σ<W at fits
 have three : 3≤arena σ := by rw [arena,ite_eq_left reads];exact Nat.le_max_left _ _
 have pairs : 2*(counter σ).val≤arena σ := by rw [arena,ite_eq_left reads];exact Nat.le_max_right _ _
 rcases separate with left | right <;> omega

/-- Universal native recursive return transport over every actual frozen
Entry and every source quotation, with one state-budgeted code image. -/
theorem returns {C : Contract} (b lo : Nat) (F : Frag (Parameters A)) (name : Name) (depth : Nat) :
 InterfaceV1.ReturnClaim b F (InterfaceV1.recursiveSource name (args (C:=C)) .none AllocatingActivation.step depth) (plan b lo F) := by
 intro L frame σ base before start entry out actual
 obtain ⟨ref,alias,pointerWord⟩ := entry.represented.pointers (.there .here)
 have reads := reads_of_success name σ ref alias depth out actual
 have costEq : (plan b lo F).heapCost σ=4*(counter σ).val := by
   change cost σ=_
   rw [cost,length_of_alias σ ref alias,AllocatingOutcome.demand,ite_eq_left reads]
 obtain ⟨workspace,pointerBelow,pointerBefore,bottomAbove,bottomBefore,reserve,fits⟩ := entry_bounds entry (by rw [length_of_alias σ ref alias];exact reads)
 by_cases zero : (counter σ).val=0
 · have prepared := RecursiveIngress.entry_prepared (plan b lo F) entry (by change 4≤4;decide) rfl
   have count : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue 0 W_pos := by
     simpa only [zero] using counter_value σ
   have env : σ.env=(countValue 0 W_pos,(some ref,())) := Prod.ext count (Prod.ext alias (by cases σ.env.2.2;rfl))
   have evaluated : args.evalT σ=.ok σ.env := by
     have known := arguments σ ref alias
     have canonical : σ.env=(countValue (counter σ).val (counter σ).isLt,(some ref,())) :=
       Prod.ext (counter_value σ) (Prod.ext alias (by cases σ.env.2.2;rfl))
     exact known.trans (congrArg Except.ok canonical.symm)
   have source := AllocatingZero.native_call name args σ σ.env evaluated count 1 (by decide)
   have same : out=⟨σ,List.prefix_refl _⟩ := AllocatingCoherence.source_coherence name args σ depth 1 out _ actual source
   subst out
   have body := AllocatingZero.image σ base (RecursiveIngress.prepared before lo (lo-1)) prepared.2.1.represented count lo (lo-1) start
     prepared.2.1.cursor prepared.2.2.1
   refine ⟨RecursiveIngress.prepared before lo (lo-1),base,(run_append_ok prepared.1).trans body,
     prepared.2.1.represented,rfl,BaseExtends.refl _,?_,prepared.2.1.cursor,prepared.2.2.2.1⟩
   simpa only [plan,show cost σ=4*(counter σ).val from costEq,zero,Nat.mul_zero] using prepared.2.2.2.2
 · have capacity : AllocationInput b frame (4*(counter σ).val) σ base before := by
     rw [←costEq]
     exact entry.capacity
   rcases capacity with impossible | ⟨positive,cursor,owner,space⟩
   · omega
   · obtain ⟨body,last,addresses,source,target,repr,stack,extended,growth,current,reference,saved,words⟩ :=
       RecursiveIngress.after_setup (counter σ).val (counter σ).isLt σ ref (counter_value σ) alias reads base before entry.represented
         cursor owner positive space lo lo start (by omega) (by omega) pointerBelow entry.payloadAbove pointerBefore reserve fits
         entry.cursor (lo-1) bottomAbove bottomBefore (by omega) (by omega)
     have called := body_is_call name σ ref alias reads ((counter σ).val+1) body source
     have same : out=body := AllocatingCoherence.source_coherence name args σ depth ((counter σ).val+1) out body actual called
     subst out
     exact ⟨last,addresses,target,repr,stack,extended,by simpa only [costEq] using growth,current,words⟩

/-- Bare revert transport is proved independently; valid reads can only
return or exhaust, and invalid reads fail after the actual first allocation. -/
theorem bare_revert {C : Contract} (b lo : Nat) (F : Frag (Parameters A)) (name : Name) (depth : Nat) :
 InterfaceV1.BareRevertClaim b F (InterfaceV1.recursiveSource name (args (C:=C)) .none AllocatingActivation.step depth) (plan b lo F) := by
 intro L frame σ base before start entry actual
 obtain ⟨ref,alias,pointerWord⟩ := entry.represented.pointers (.there .here)
 have evaluated := arguments σ ref alias
 by_cases reads : (counter σ).val≤σ.heap.len ref .dyn
 · obtain ⟨out,source,rest⟩ := AllocatingSource.call_success name args ((counter σ).val+1) σ (counter σ).val (counter σ).isLt ref evaluated reads (by omega)
   have classified := AllocatingQuotations.source_classification name args σ _ evaluated (counter σ).val (counter σ).isLt ref rfl rfl reads _ out source depth
   rw [actual] at classified
   by_cases enough : (counter σ).val<depth
   · rw [ite_eq_left enough] at classified;cases classified
   · rw [ite_eq_right enough] at classified;cases classified
 · have prepared := RecursiveIngress.entry_prepared (plan b lo F) entry (by change 4≤4;decide) rfl
   have costEq : (plan b lo F).heapCost σ=4 := by
     change cost σ=_
     rw [cost,length_of_alias σ ref alias,AllocatingOutcome.demand,ite_eq_right reads]
   have capacity : AllocationInput b frame 4 σ base (RecursiveIngress.prepared before lo (lo-1)) := by
     rw [←costEq]
     exact prepared.2.1.capacity
   rcases capacity with impossible | ⟨positive,cursor,owner,space⟩
   · cases impossible
   · cases number : (counter σ).val with
     | zero => omega
     | succ n =>
       have bound : n+1<W := by have h:=(counter σ).isLt;omega
       have count : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) bound := by
         simpa only [number] using counter_value σ
       have failed : ArrayProbe.value.evalT σ=.error .revert := (HeapDomain.failure_iff σ n bound ref count alias).2 (by omega)
       have workspace : b+4≤lo := entry.workspace
       have below : lo<frame := entry.pointerBelow
       have target := AllocatingFailure.target_image σ n bound ref count alias failed base _ prepared.2.1.represented
         cursor owner positive space (by omega) lo (lo-1)
       exact (run_append_ok prepared.1).trans target

/-- The quotation changes no code or state-derived metadata. -/
def family {C : Contract} (b lo : Nat) (F : Frag (Parameters A)) : InterfaceV1.RecursiveEmission C (Parameters A) (Parameters A) :=
 ⟨(plan (C:=C) b lo F).code,(fun _ => F),(fun _ => 4),lo,lo,(fun _ => arena),(fun _ => cost)⟩

theorem family_at {C : Contract} (b lo : Nat) (F : Frag (Parameters A)) (n : Nat) : (family (C:=C) b lo F).at n=plan b lo F := rfl

theorem family_returns {C : Contract} (b lo : Nat) (F : Frag (Parameters A)) (name : Name) :
 ∀ n, InterfaceV1.ReturnClaim b F (InterfaceV1.recursiveSource name (args (C:=C)) .none AllocatingActivation.step n) ((family b lo F).at n) :=
 fun n => returns b lo F name n

theorem family_bare_revert {C : Contract} (b lo : Nat) (F : Frag (Parameters A)) (name : Name) :
 ∀ n, InterfaceV1.BareRevertClaim b F (InterfaceV1.recursiveSource name (args (C:=C)) .none AllocatingActivation.step n) ((family b lo F).at n) :=
 fun n => bare_revert b lo F name n

/-- The remaining V3 domain duties are explicit inputs. Neither profile nor
coverage nor real outcome membership is inferred from the emitter. All code
correctness fields below are derived from the actual universal proofs. -/
def make {C : Contract} (b lo : Nat) (F : Frag (Parameters A)) (name : Name)
 (approved admitted : Nat → InterfaceV3.Admission C (Parameters A))
 (profile : InterfaceV3.FamilyAdmissionAgreement approved admitted)
 (coverage : InterfaceV3.FamilyEntryCoverage b F admitted (family b lo F))
 (successful : ∃ n, InterfaceV3.SuccessfulEntry b F (admitted n)
   (InterfaceV1.recursiveSource name args .none AllocatingActivation.step n) ((family b lo F).at n))
 (reverting : ∃ n, InterfaceV3.RevertingEntry b F (admitted n)
   (InterfaceV1.recursiveSource name args .none AllocatingActivation.step n) ((family b lo F).at n)) :
 InterfaceV3.PendingRecursiveReturns b F approved admitted name args .none AllocatingActivation.step where
 plan := family b lo F
 required_profile := profile
 required_coverage := coverage
 required_successful_entry := successful
 required_reverting_entry := reverting
 required_source_coherence := AllocatingCoherence.source_coherence name args
 required_return := family_returns b lo F name
 required_bare_revert := family_bare_revert b lo F name

namespace Checks
open CountdownWitness
abbrev selected : InterfaceV1.Emission P.C (Parameters A) (Parameters A) := plan 2 8 F
abbrev before := AllocatorReturn.Checks.input
abbrev bad := ArrayProbe.Checks.bad
abbrev badBefore := ArrayProbe.Checks.badMachine

theorem counter_two : (counter callee).val=2 := rfl
theorem counter_three : (counter bad).val=3 := rfl
theorem length_two : length callee=2 := by rw [length_of_alias callee P.r0 rfl];exact HeapDomain.Checks.length_zero
theorem bad_length_two : length bad=2 := by rw [length_of_alias bad P.r0 rfl];exact HeapDomain.Checks.length_zero

theorem cost_two : cost callee=8 := by rw [cost,counter_two,length_two,AllocatingOutcome.demand];decide
theorem cost_bad : cost bad=4 := by rw [cost,counter_three,bad_length_two,AllocatingOutcome.demand];decide

theorem entry : InterfaceV1.Entry selected 1 2 16 F callee P.base before 10 where
 represented := AllocatorReturn.Checks.represented
 callerBound := by decide
 resultBound := by decide
 workspace := by decide
 pointerAbove := by decide
 pointerBelow := by decide
 payloadAbove := by decide
 reserve := by change 10+arena callee≤16;rw [arena,counter_two,length_two];decide
 controlSpace := by change 3≤arena callee;rw [arena,counter_two,length_two];decide
 separate := .inl (by decide)
 noWrap := by change 10+arena callee<W;rw [arena,counter_two,length_two];decide
 cursor := rfl
 capacity := .inr ⟨by decide,⟨22,by decide⟩,AllocatorReturn.Checks.ownership,by change 22+cost callee<W;rw [cost_two];decide⟩

theorem bad_entry : InterfaceV1.Entry selected 1 2 16 F bad P.base badBefore 10 where
 represented := ArrayProbe.Checks.bad_repr
 callerBound := by decide
 resultBound := by decide
 workspace := by decide
 pointerAbove := by decide
 pointerBelow := by decide
 payloadAbove := by decide
 reserve := by change 10+arena bad≤16;rw [arena,counter_three,bad_length_two];decide
 controlSpace := by change 3≤arena bad;rw [arena,counter_three,bad_length_two];decide
 separate := .inl (by decide)
 noWrap := by change 10+arena bad<W;rw [arena,counter_three,bad_length_two];decide
 cursor := rfl
 capacity := .inr ⟨by decide,⟨22,by decide⟩,ArrayProbe.Checks.bad_ownership,by change 22+cost bad<W;rw [cost_bad];decide⟩

def call (n : Nat) : Stmt P.C (Parameters A) (Parameters A) :=
 InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step n

theorem source : (call 3).run callee=.ok AllocatingReturn.Checks.output :=
 body_is_call "allocatingCountdown" callee P.r0 rfl (by rw [counter_two];exact AllocatingSource.Checks.read_bound)
   3 AllocatingReturn.Checks.output AllocatingReturn.Checks.specification.1

theorem bad_source : (call 1).run bad=.error .revert :=
 AllocatingFailure.call_failure "allocatingCountdown" args bad 0 2 (by decide) P.r0 (by rfl) ArrayProbe.Checks.bad_evaluated

theorem successful_entry : InterfaceV2.SuccessfulEntry 2 F (call 3) selected :=
 ⟨1,16,callee,P.base,before,10,AllocatingReturn.Checks.output,entry,source⟩

theorem reverting_entry : InterfaceV2.RevertingEntry 2 F (call 1) selected :=
 ⟨1,16,bad,P.base,badBefore,10,bad_entry,bad_source⟩

/-- A real frozen V2 producer for this allocating family. V3 additionally
requires approved-domain provenance/coverage and admitted memberships. -/
def producer : InterfaceV2.PendingRecursiveReturns 2 F "allocatingCountdown" (args (C:=P.C)) .none AllocatingActivation.step where
 plan := family 2 8 F
 required_successful_entry := ⟨3,successful_entry⟩
 required_source_coherence := AllocatingCoherence.source_coherence "allocatingCountdown" args
 required_return := family_returns 2 8 F "allocatingCountdown"
 required_bare_revert := family_bare_revert 2 8 F "allocatingCountdown"

theorem returned : InterfaceV1.Returned selected 1 2 16 callee P.base before 10 AllocatingReturn.Checks.output :=
 returns 2 8 F "allocatingCountdown" 3 1 16 callee P.base before 10 entry _ source

noncomputable def target := returned.choose
noncomputable def addresses := returned.choose_spec.choose

theorem specification : run selected.code before=.ok target 0 ∧
 StateRepr 1 2 16 F AllocatingReturn.Checks.output.st addresses target ∧ target.stack=before.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 (cost callee) callee P.base before AllocatingReturn.Checks.output.st addresses target ∧
 target.mem 8=w[10] ∧ Footprint.Words 8 10 before target := returned.choose_spec.choose_spec

theorem same_target : target=AllocatingReturn.Checks.machine :=
 (Evm.Out.ok.inj (specification.1.symm.trans RecursiveIngress.Checks.prior_target)).1

theorem observations :
 (target.stack,[target.mem 0,target.mem 1,target.mem 2,target.mem 3,target.mem 7,target.mem 8,target.mem 9,
 target.mem 10,target.mem 11,target.mem 12,target.mem 13,target.mem 16,target.mem 17,target.mem 18,target.mem 20,target.mem 21])=
 ([w[77]],[w[30],w[16],w[16],w[2],w[10],w[10],w[99],w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]) := by
 rw [same_target]
 exact AllocatingReturn.Checks.observations

theorem target_revert : run selected.code badBefore=.revert :=
 bare_revert 2 8 F "allocatingCountdown" 1 1 16 bad P.base badBefore 10 bad_entry bad_source

theorem shared_code (n k : Nat) : ((family (C:=P.C) 2 8 F).at n).code = ((family (C:=P.C) 2 8 F).at k).code := rfl

theorem no_unreached_frames : arena bad=3 := by rw [arena,counter_three,bad_length_two];decide

theorem wrong_fixed_cost : cost callee≠cost bad := by rw [cost_two,cost_bad];decide

theorem zero_source : (call 0).run callee=.error .exhausted := source_zero "allocatingCountdown" args callee _ (arguments callee P.r0 rfl)

theorem zero_unmatched : ¬GrowingResult 1 2 16 (cost callee) F callee P.base before ((call 0).run callee) (run selected.code before) := by
 rw [zero_source]
 intro same
 rcases same with ⟨out,m,base,source,rest⟩ | ⟨source,rest⟩
 · cases source
 · cases source

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission
