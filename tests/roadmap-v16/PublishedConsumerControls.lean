import Solidity.Roadmap.V16.DispatchConsumer
import Solidity.Roadmap.V16.AbiEntryConsumer
import Solidity.Evm.MemoryCompileExamples
import Solidity.Evm.MemoryAllocSourceExamples
import Solidity.Semantics.AbiEntryChecks
import Lean

/-! Actual intrinsic chains and source-decoder values. No partial-elaborator,
SourceSpec, external entry or byte-EVM correspondence is assumed. -/
set_option autoImplicit false

open Lean Elab Term in
elab "publishedPrimitive%" n:ident : term => do
  let name := mkPrivateNameCore `Solidity.Evm.MemoryCompileExamples
    (`Solidity.Evm.Memory.CompileExamples ++ n.getId)
  unless (← getEnv).contains name do throwError "missing actual primitive observation {name}"
  return mkConst name

namespace Solidity.Roadmap.V16.PublishedControls
open Solidity.Evm

theorem out_of_positive {α : Type} {r : TRes α} (h : r.toOption.isSome = true) :
    r = .ok (r.toOption.get h) := by
  cases r with
  | error e => cases h
  | ok o => rfl

/-- Constructive, test-local equality for the existing result type; no execution
semantics, global instance, native shortcut or proof-budget change. -/
local instance : DecidableEq (TRes PrimTy.bool.Denote) := by
  change DecidableEq (TRes Bool)
  intro a b
  cases a with
  | error e =>
    cases b with
    | error f =>
      exact if h : e = f then .isTrue (congrArg Except.error h)
        else .isFalse (fun eq => h (Except.error.inj eq))
    | ok y => exact .isFalse (by intro h; cases h)
  | ok x =>
    cases b with
    | error f => exact .isFalse (by intro h; cases h)
    | ok y =>
      exact if h : x = y then .isTrue (congrArg Except.ok h)
        else .isFalse (fun eq => h (Except.ok.inj eq))

namespace dispatch
open Memory.CompileExamples
abbrev initial := σ
def machine : Machine := {Memory.CompileExamples.machine with stack := [w[77]]}

/-- A real aliased array's length is read; selected bodies leave it unchanged. -/
def guard (n : Int) (h : PrimTy.uint.inRange n = true) : Val C Γ .bool :=
  .binop .eqB rfl rfl (.mlen (.var (.there (.there .here)) rfl) rfl) (.simple (.lit n h))
def miss : DispatchArm C Γ := ⟨guard 1 rfl,badRhsRead⟩
def chosen : DispatchArm C Γ := ⟨guard 2 rfl,coreAssignment⟩
def duplicate : DispatchArm C Γ := ⟨guard 2 rfl,badIndexRead⟩
def P : Prog C Γ Γ := .cons (DispatchArm.chain [miss,chosen,duplicate] .revert) .nil
def compiled : Compiler.Compilation 0 (Frag.init Γ) P :=
  (Compiler.compile 0 (Frag.init Γ) P).get (by decide +kernel)
attribute [irreducible] compiled
theorem path : compiled.isMemory = true := by decide +kernel
theorem input : compiled.Input 1 4 base initial machine := by
  apply (compiled.memory_input path 1 4 base initial machine).mpr
  exact ⟨fixture_repr.stack [w[77]],by decide +kernel,.inl (by decide +kernel)⟩
theorem before : ∀ a ∈ [miss], a.cond.evalT initial = .ok false := by
  intro a h
  simp only [List.mem_singleton] at h
  subst a
  decide +kernel
theorem hit : chosen.cond.evalT initial = .ok true := by decide +kernel
theorem duplicate_guard : chosen.cond = duplicate.cond := rfl
theorem duplicate_true : duplicate.cond.evalT initial = .ok true := by decide +kernel

def bodyP : Prog C Γ Γ := .cons (.block coreAssignment) .nil
theorem body_positive : (bodyP.run initial).toOption.isSome = true := by decide +kernel
def bodyOut : Solidity.Out C H Γ := (bodyP.run initial).toOption.get body_positive
attribute [irreducible] bodyOut
theorem body_source : bodyP.run initial = .ok bodyOut := by
  simpa only [bodyOut] using out_of_positive body_positive
def post : Spec C Γ := .eq (.pvV .here) (.app0 (.lit ⟨8,by decide⟩))
theorem body_diamond : Spec.sat initial (.diamond bodyP post) := by
  rw [Spec.sat,body_source]
  exact ⟨⟨8,by decide⟩,by decide +kernel,rfl⟩

theorem represented : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ compiled.Rep 1 4 base initial machine o.st m' ∧ Spec.sat o.st post := by
  have result := dispatch_finite_diamond [miss] chosen [duplicate] .revert initial post before hit
    compiled (.inl path) input body_diamond
  exact result

theorem no_late_failure : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    chosen.cond.evalT initial = .ok true ∧ duplicate.cond.evalT initial = .ok true := by
  obtain ⟨o,m',hs,ht,_⟩ := represented
  exact ⟨o,m',hs,ht,hit,duplicate_true⟩

def observeSource (res : TRes (Solidity.Out C H Γ)) : Option (List Nat) := do
  let o ← res.toOption
  let a ← TEnv.get (.there .here : Idx Γ (.mem (.array (.prim .uint)))) o.st.env
  let b ← TEnv.get (.there (.there .here) : Idx Γ (.mem (.array (.prim .uint)))) o.st.env
  let c ← TEnv.get (.there (.there (.there .here)) : Idx Γ (.mem (.array (.prim .uint)))) o.st.env
  let a0 ← o.st.heap.index a .dyn (uint 0 W_pos)
  let a1 ← o.st.heap.index a .dyn (uint 1 (by decide))
  let c0 ← o.st.heap.index c .dyn (uint 0 W_pos)
  pure [(TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).val.toNat,
    (base a.id).val,(base b.id).val,(base c.id).val,o.st.heap.len a .dyn,a0.val.toNat,a1.val.toNat,
    o.st.heap.len c .dyn,c0.val.toNat]
def observeTarget : Evm.Out → Option (List Nat)
  | .ok m _ => [3,2,1,0,16,17,18,20,21].mapM fun a =>
      match m.mem a with | .val w => some w.val | .slot _ => none
  | _ => none

theorem source_observed : observeSource (P.run initial) = some [8,16,16,20,2,7,9,1,4] := by
  unfold P
  decide +kernel
theorem target_observed : observeTarget (run compiled.code machine) = some [8,16,16,20,2,7,9,1,4] := by
  decide +kernel

theorem ordered : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ compiled.Rep 1 4 base initial machine o.st m' ∧ Spec.sat o.st post ∧
    observeSource (.ok o) = some [8,16,16,20,2,7,9,1,4] ∧
    observeTarget (.ok m' 0) = some [8,16,16,20,2,7,9,1,4] := by
  obtain ⟨o,m',hs,ht,stack,rep,hpost⟩ := represented
  refine ⟨o,m',hs,ht,stack,rep,hpost,?_,?_⟩
  · rw [← hs]; exact source_observed
  · rw [← ht]; exact target_observed

theorem wrong_result : ¬ ∃ m', run compiled.code machine = .ok m' 0 ∧
    observeTarget (.ok m' 0) = some [9,16,16,20,2,7,9,1,4] := by
  rintro ⟨m',ht,wrong⟩
  obtain ⟨o,n,hs,hn,stack,rep,hpost,src,good⟩ := ordered
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  rw [wrong] at good
  cases good

/-- Reversing the two matching guards really selects the failing body. -/
def failP : Prog C Γ Γ := .cons (DispatchArm.chain [duplicate,chosen] .revert) .nil
def failCompiled : Compiler.Compilation 0 (Frag.init Γ) failP :=
  (Compiler.compile 0 (Frag.init Γ) failP).get (by decide +kernel)
attribute [irreducible] failCompiled
theorem fail_path : failCompiled.isMemory = true := by decide +kernel
theorem fail_input : failCompiled.Input 1 4 base initial machine := by
  apply (failCompiled.memory_input fail_path 1 4 base initial machine).mpr
  exact ⟨fixture_repr.stack [w[77]],by decide +kernel,.inl (by decide +kernel)⟩
theorem fail_source : failP.run initial = .error .revert := by
  have selected := dispatch_selected_run [] duplicate [chosen] .revert initial
    (by intros; contradiction) duplicate_true
  have exactShape : failP.run initial = (Prog.cons (.block duplicate.body) .nil).run initial := by
    simpa only [failP,List.nil_append] using selected
  rw [exactShape]
  exact (publishedPrimitive% sourceReverted_sound) (by decide +kernel)

theorem first_failure : failP.run initial = .error .revert ∧ run failCompiled.code machine = .revert :=
  ⟨fail_source,(finite_heap_failure failCompiled (.inl fail_path) fail_input fail_source).2⟩

def absent : DispatchArm C Γ := ⟨guard 3 rfl,coreAssignment⟩
def noneP : Prog C Γ Γ := .cons (DispatchArm.chain [miss,absent] .revert) .nil
def noneCompiled : Compiler.Compilation 0 (Frag.init Γ) noneP :=
  (Compiler.compile 0 (Frag.init Γ) noneP).get (by decide +kernel)
attribute [irreducible] noneCompiled
theorem none_path : noneCompiled.isMemory = true := by decide +kernel
theorem none_input : noneCompiled.Input 1 4 base initial machine := by
  apply (noneCompiled.memory_input none_path 1 4 base initial machine).mpr
  exact ⟨fixture_repr.stack [w[77]],by decide +kernel,.inl (by decide +kernel)⟩
theorem all_miss : ∀ a ∈ [miss,absent], a.cond.evalT initial = .ok false := by
  intro a h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl <;> decide +kernel
theorem none_source : noneP.run initial = .error .revert := by
  unfold noneP
  rw [dispatch_none_run [miss,absent] .revert initial all_miss]
  rfl
theorem no_candidate : noneP.run initial = .error .revert ∧ run noneCompiled.code machine = .revert :=
  ⟨none_source,(finite_heap_failure noneCompiled (.inl none_path) none_input none_source).2⟩

def localArm : DispatchArm C Γ := ⟨guard 2 rfl,declareAndRebind⟩
def localP : Prog C Γ Γ := .cons (DispatchArm.chain [miss,localArm,duplicate] .revert) .nil
def localCompiled : Compiler.Compilation 0 (Frag.init Γ) localP :=
  (Compiler.compile 0 (Frag.init Γ) localP).get (by decide +kernel)
attribute [irreducible] localCompiled
theorem local_path : localCompiled.isMemory = true := by decide +kernel
theorem local_input : localCompiled.Input 1 6 base initial machine := by
  apply (localCompiled.memory_input local_path 1 6 base initial machine).mpr
  exact ⟨fixture_six_cells.stack [w[77]],by decide +kernel,.inl (by decide +kernel)⟩
theorem local_frame_refused : ¬ localCompiled.Input 1 4 base initial machine := by
  intro h
  have bound := ((localCompiled.memory_input local_path 1 4 base initial machine).mp h).2.1
  have need : Memory.frameNeedProg localP = 6 := by decide +kernel
  rw [need] at bound
  omega

def localBody : Prog C Γ Γ := .cons (.block declareAndRebind) .nil
theorem local_positive : (localBody.run initial).toOption.isSome = true := by decide +kernel
def localOut : Solidity.Out C H Γ := (localBody.run initial).toOption.get local_positive
attribute [irreducible] localOut
theorem local_source : localBody.run initial = .ok localOut := by
  simpa only [localOut] using out_of_positive local_positive
def localPost : Spec C Γ := .eq (.pvV .here) (.app0 (.lit ⟨4,by decide⟩))
theorem local_diamond : Spec.sat initial (.diamond localBody localPost) := by
  rw [Spec.sat,local_source]
  exact ⟨⟨4,by decide⟩,by decide +kernel,rfl⟩
theorem local_hit : localArm.cond.evalT initial = .ok true := by decide +kernel
theorem local_drop : ∃ o m', localP.run initial = .ok o ∧ run localCompiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ localCompiled.Rep 1 6 base initial machine o.st m' ∧ Spec.sat o.st localPost :=
  dispatch_finite_diamond [miss] localArm [duplicate] .revert initial localPost before local_hit
    localCompiled (.inl local_path) local_input local_diamond

theorem body_box : Spec.sat initial (.box bodyP post) := by
  rw [Spec.sat,body_source]
  exact ⟨⟨8,by decide⟩,by decide +kernel,rfl⟩
theorem selected_box : Spec.sat initial (.box P post) :=
  (dispatch_box_iff [miss] chosen [duplicate] .revert initial post before hit).mpr body_box

def badGuard : Val C Γ .bool := .binop .eqB rfl rfl
  (.readMem (.index .dyn (.var (.there (.there (.there .here))) rfl) (.simple (.lit 1 rfl))))
  (.simple (.lit 0 rfl))
def guardArm : DispatchArm C Γ := ⟨badGuard,coreAssignment⟩
def guardP : Prog C Γ Γ := .cons (DispatchArm.chain [guardArm,chosen] .revert) .nil
def guardCompiled : Compiler.Compilation 0 (Frag.init Γ) guardP :=
  (Compiler.compile 0 (Frag.init Γ) guardP).get (by decide +kernel)
attribute [irreducible] guardCompiled
theorem guard_path : guardCompiled.isMemory = true := by decide +kernel
theorem guard_input : guardCompiled.Input 1 4 base initial machine := by
  apply (guardCompiled.memory_input guard_path 1 4 base initial machine).mpr
  exact ⟨fixture_repr.stack [w[77]],by decide +kernel,.inl (by decide +kernel)⟩
theorem guard_error : guardArm.cond.evalT initial = .error .revert := by decide +kernel
theorem guard_source : guardP.run initial = .error .revert := by
  have statement := dispatch_guard_error guardArm [chosen] .revert initial .revert guard_error
  change TRun.seq (DispatchArm.chain [guardArm,chosen] .revert).runR
    (Prog.nil : Prog C Γ Γ).runR initial = _
  simp only [TRun.seq,Stmt.run] at statement ⊢
  rw [statement]
theorem guard_failure : guardP.run initial = .error .revert ∧ run guardCompiled.code machine = .revert :=
  ⟨guard_source,(finite_heap_failure guardCompiled (.inl guard_path) guard_input guard_source).2⟩
theorem guard_not_hit : guardArm.cond.evalT initial ≠ .ok true := by rw [guard_error]; intro h; cases h

def observeLocalTarget : Evm.Out → Option (List Nat)
  | .ok m _ => [3,2,1,0,16,17,18,20,21,4,5].mapM fun a =>
      match m.mem a with | .val w => some w.val | .slot _ => none
  | _ => none
theorem local_source_observed : observeSource (localP.run initial) = some [4,16,16,20,2,7,9,1,4] := by decide +kernel
theorem local_target_observed : observeLocalTarget (run localCompiled.code machine) =
    some [4,16,16,20,2,7,9,1,4,20,2] := by decide +kernel
theorem local_ordered : ∃ o m', localP.run initial = .ok o ∧ run localCompiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ localCompiled.Rep 1 6 base initial machine o.st m' ∧ Spec.sat o.st localPost ∧
    observeSource (.ok o) = some [4,16,16,20,2,7,9,1,4] ∧
    observeLocalTarget (.ok m' 0) = some [4,16,16,20,2,7,9,1,4,20,2] := by
  obtain ⟨o,m',hs,ht,stack,rep,hpost⟩ := local_drop
  refine ⟨o,m',hs,ht,stack,rep,hpost,?_,?_⟩
  · rw [← hs]; exact local_source_observed
  · rw [← ht]; exact local_target_observed

theorem wrong_before : ¬ (∀ a ∈ [chosen], a.cond.evalT initial = .ok false) := by
  intro h
  have bad := h chosen (List.mem_cons_self ..)
  rw [hit] at bad
  cases bad
end dispatch
end Solidity.Roadmap.V16.PublishedControls

open Lean Elab Term in
elab "publishedEntryBody%" n:ident : term => do
  let name := mkPrivateNameCore `Solidity.Evm.MemoryAllocSourceExamples
    (`Solidity.Evm.Memory.AllocSourceExamples ++ n.getId)
  unless (← getEnv).contains name do throwError "missing actual scalar body fixture {name}"
  return mkConst name

namespace Solidity.Roadmap.V16.PublishedControls
open Solidity.Evm
namespace entry
abbrev K := publishedEntryBody% C
abbrev Γ : Ctx := publishedEntryBody% Γ
abbrev Δ : Ctx := publishedEntryBody% Δ
abbrev initial := publishedEntryBody% σ
abbrev bases := publishedEntryBody% bases
abbrev machine := publishedEntryBody% machine
abbrev cursor := publishedEntryBody% cursor
abbrev shape : AbiEntry.Shape := .word (.uint 256)
def value : AbiEntry.Val shape := .word ⟨2,by decide,by decide⟩
def packet : AbiEntry.Input := {data := [0,0,0,0] ++ List.replicate 31 0 ++ [2],free := 2 ^ 32}
theorem packet_published_data : packet.data = (AbiEntry.Checks.cd [2]).data := by decide +kernel
theorem packet_published_free : packet.free = (AbiEntry.Checks.cd [2]).free := rfl
theorem size : packet.size ≤ AbiEntry.lim := by decide +kernel
def decodedNumber : Except AbiEntry.Fail (AbiEntry.Val shape) → Option Nat
  | .error _ => none
  | .ok (.word w) => some w.val

theorem actual_number : decodedNumber (AbiEntry.eager packet (7 + 1) shape 0) = some 2 := by decide +kernel

theorem decoded : AbiEntry.eager packet (7 + 1) shape 0 = .ok value := by
  have observed := actual_number
  cases result : AbiEntry.eager packet (7 + 1) shape 0 with
  | error e => rw [result] at observed; cases observed
  | ok v =>
    rw [result] at observed
    cases v with
    | word w =>
      have number : w.val = 2 := Option.some.inj observed
      have wordEq : w = (⟨2,by decide,by decide⟩ : AbiEntry.Word (.uint 256)) := by
        cases w with
        | mk n bound valid =>
          change n = 2 at number
          subst n
          rfl
      exact congrArg (fun w : AbiEntry.Word (.uint 256) =>
        (Except.ok (AbiEntry.Val.word w) : Except AbiEntry.Fail (AbiEntry.Val shape))) wordEq
theorem lazy_reference : ∃ addr len, AbiEntry.cref packet shape 4 0 = .ok (addr,len) ∧
    AbiEntry.cval packet 7 shape addr len = .ok value ∧ (abiUint value).val = 2 :=
  abi_eager_observation size decoded (fun v => (abiUint v).val = 2) rfl

theorem state_binding : bindAbiUint initial (.here : Idx Γ (.val .uint)) value = initial := rfl

def P : Prog K Γ Δ := publishedEntryBody% program
attribute [irreducible] P
def compiled : Compiler.Compilation 1 (Frag.init Γ) P := by
  simpa only [P] using (publishedEntryBody% compiled)
attribute [irreducible] compiled
theorem path : compiled.isMemory = true := by decide +kernel

theorem input : compiled.Input 1 6 bases (bindAbiUint initial .here value) machine := by
  rw [state_binding]
  apply (compiled.memory_input path 1 6 bases initial machine).mpr
  exact ⟨Memory.AllocSourceExamples.initial_repr.1,by decide +kernel,
    .inr ⟨by decide,cursor,Memory.AllocSourceExamples.initial_repr.2,by decide +kernel⟩⟩

theorem positive : (P.run initial).toOption.isSome = true := by unfold P; decide +kernel
def output : Solidity.Out K initial.H Δ := (P.run initial).toOption.get positive
attribute [irreducible] output
theorem source : P.run initial = .ok output := by
  simpa only [output] using out_of_positive positive

def post : Spec K Δ :=
  .and (.eq (.app2 .mlen (.app0 .memory) (.pvI .here)) (.app0 (.lit ⟨0,by decide⟩)))
    (.eq (.app2 .mlen (.app0 .memory) (.pvI (.there .here))) (.app0 (.lit ⟨2,by decide⟩)))
theorem output_post : Spec.sat output.st post := by
  constructor
  · exact ⟨⟨0,by decide⟩,by decide +kernel,rfl⟩
  · exact ⟨⟨2,by decide⟩,by decide +kernel,rfl⟩
theorem body : Spec.sat (bindAbiUint initial .here value) (.diamond P post) := by
  rw [state_binding,Spec.sat,source]
  exact output_post

/-- Kernel-decoded2 really constructs the typed state and actual memory Input;
no representation oracle or external-entry/selector/bytecode claim. -/
theorem represented : ∃ addr len o m', AbiEntry.cref packet shape 4 0 = .ok (addr,len) ∧
    AbiEntry.cval packet 7 shape addr len = .ok value ∧
    P.run (bindAbiUint initial .here value) = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = machine.stack ∧ compiled.Rep 1 6 bases (bindAbiUint initial .here value) machine o.st m' ∧ Spec.sat o.st post :=
  abi_uint_finite_diamond compiled (.inl path) size decoded initial .here input body

theorem source_observed : (publishedEntryBody% sourceObserve) (P.run (bindAbiUint initial .here value)) =
    some [2,1,0,0,2,2] := by
  change (publishedEntryBody% sourceObserve) (P.run initial) = some [2,1,0,0,2,2]
  simpa only [P] using Memory.AllocSourceExamples.source_run
theorem target_observed : (publishedEntryBody% targetObserve) (run compiled.code machine) =
    some [0,20,2,16,19,99,2,0,0,0] := by
  simpa only [compiled,P] using Memory.AllocSourceExamples.target_run

theorem ordered : ∃ addr len o m', AbiEntry.cref packet shape 4 0 = .ok (addr,len) ∧
    AbiEntry.cval packet 7 shape addr len = .ok value ∧
    P.run (bindAbiUint initial .here value) = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = machine.stack ∧ compiled.Rep 1 6 bases (bindAbiUint initial .here value) machine o.st m' ∧
    Spec.sat o.st post ∧ (publishedEntryBody% sourceObserve) (.ok o) = some [2,1,0,0,2,2] ∧
    (publishedEntryBody% targetObserve) (.ok m' 0) = some [0,20,2,16,19,99,2,0,0,0] := by
  obtain ⟨addr,len,o,m',he,hl,hs,ht,stack,rep,hpost⟩ := represented
  refine ⟨addr,len,o,m',he,hl,hs,ht,stack,rep,hpost,?_,?_⟩
  · rw [← hs]; exact source_observed
  · rw [← ht]; exact target_observed

def wrongValue : AbiEntry.Val shape := .word ⟨3,by decide,by decide⟩
theorem wrong_decode : AbiEntry.eager packet (7 + 1) shape 0 ≠ .ok wrongValue := by
  rw [decoded]
  intro h
  have number := congrArg (fun v => (abiUint v).val) (Except.ok.inj h)
  change (2 : Int) = 3 at number
  omega

theorem wrong_binding : bindAbiUint initial .here value ≠
    initial.setLocal .here (Memory.indexValue (wmod 3)) := by
  intro h
  have number := congrArg (fun s => (TEnv.get (.here : Idx Γ (.val .uint)) s.env).val) h
  change (2 : Int) = 3 at number
  omega

def params : List AbiEntry.Param := [{shape,loc := .value}]
def values : AbiEntry.Vals (params.map AbiEntry.Param.shape) := .cons value .nil
theorem accepted : AbiEntry.verdict packet 8 params = .run values := by rfl
theorem prerequisites : ∃ es, AbiEntry.entry packet 8 params = .ok es ∧
    AbiEntry.bodyValues packet 8 params es 0 = .ok values := abi_run_prerequisites accepted

def boolParams : List AbiEntry.Param := [{shape := .word .bool,loc := .value}]
theorem wrong_kind_reverts : AbiEntry.verdict packet 8 boolParams = .revert := by rfl
theorem actual_entry_revert : AbiEntry.entry packet 8 boolParams = .error .revert :=
  abi_certified_revert packet 8 boolParams wrong_kind_reverts

def latePacket : AbiEntry.Input := AbiEntry.Checks.cd [0x20,1,0x1000]
def lateParams := AbiEntry.Checks.arr2 .calldata
abbrev lateFuel := (latePacket.size + 8) * 8
theorem late_entry : AbiEntry.entry latePacket lateFuel lateParams = .ok (.cons (.ref 68 1) .nil) := by rfl
theorem late_blocked : AbiEntry.verdict latePacket lateFuel lateParams =
    .blocked "calldata element fails only on access: needs access-time calldata semantics" := by rfl

def panicPacket : AbiEntry.Input := AbiEntry.Checks.cd [0x20,2 ^ 64]
def panicParams : List AbiEntry.Param := [{shape := .bytes,loc := .memory}]
theorem panic_entry : AbiEntry.entry panicPacket 16 panicParams = .error .panic := by rfl
theorem panic_blocked : AbiEntry.verdict panicPacket 16 panicParams =
    .blocked "possible Panic(0x41) allocation failure in memory decoding" := by rfl
theorem exhausted_decoder : AbiEntry.verdict packet 0 params = .blocked "ABI decoder fuel exhausted" := by rfl

theorem wrong_input_binding : ¬ compiled.Input 1 6 bases (bindAbiUint initial .here wrongValue) machine := by
  intro h
  have repr := ((compiled.memory_input path 1 6 bases (bindAbiUint initial .here wrongValue) machine).mp h).1
  have cell := repr.core.vals (.here : Idx Γ (.val .uint))
  change ∃ a : Fin W, w[2] = Word.val a ∧ (3 : Int) = a.val at cell
  obtain ⟨a,word,number⟩ := cell
  have address := congrArg Fin.val (Word.val.inj word)
  change (2 : Nat) = a.val at address
  omega

theorem wrong_compiler_result : ¬ ∃ m', run compiled.code machine = .ok m' 0 ∧
    (publishedEntryBody% targetObserve) (.ok m' 0) = some [0,21,2,16,19,99,2,0,0,0] := by
  rintro ⟨m',ht,wrong⟩
  obtain ⟨addr,len,o,n,he,hl,hs,hn,stack,rep,hpost,src,good⟩ := ordered
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  rw [wrong] at good
  cases good
end entry
end Solidity.Roadmap.V16.PublishedControls

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut inductives : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity).isPrefixOf n then
      if let .inductInfo info := info then
        inductives := inductives.push (Json.mkObj [
          ("name", toJson n.toString), ("constructors", toJson (info.ctors.map Name.toString))])
  let mut theorems : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity.Roadmap.V16).isPrefixOf ((privateToUserName? n).getD n) ||
        (`_private.Solidity.Roadmap.V16).isPrefixOf n then
      if let .thmInfo _ := info then
        let axs ← collectAxioms n
        let ty ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
        let premises ← liftTermElabM do
          Meta.forallBoundedTelescope info.type (some info.type.getNumHeadForalls) fun xs _ => do
            let mut rows : Array Json := #[]
            let mut rawType := info.type
            for x in xs do
              let decl ← x.fvarId!.getDecl
              let ty ← Meta.ppExpr decl.type
              let rawDomain := rawType.consumeMData.bindingDomain!
              rawType := rawType.consumeMData.bindingBody!
              rows := rows.push (Json.mkObj [
                ("name", toJson decl.userName.toString), ("type", toJson ty.pretty),
                ("isProp", toJson (← Meta.isProp decl.type)),
                ("closedExpr", toJson (reprStr rawDomain)),
                ("constants", toJson (decl.type.getUsedConstants.toList.map Name.toString))])
            return rows
        theorems := theorems.push (Json.mkObj [
          ("name", toJson n.toString), ("ownerName", toJson ((privateToUserName? n).getD n).toString),
          ("type", toJson ty), ("premises", .arr premises),
          ("typeConstants", toJson (info.type.getUsedConstants.toList.map Name.toString)),
          ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
          ("axioms", toJson (axs.toList.map Name.toString))])
  let mut definitions : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity.Roadmap.V16).isPrefixOf ((privateToUserName? n).getD n) ||
        (`_private.Solidity.Roadmap.V16).isPrefixOf n then
      if let .defnInfo _ := info then
        let axs ← collectAxioms n
        let ty ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
        definitions := definitions.push (Json.mkObj [
          ("name", toJson n.toString), ("ownerName", toJson ((privateToUserName? n).getD n).toString),
          ("type", toJson ty),
          ("typeConstants", toJson (info.type.getUsedConstants.toList.map Name.toString)),
          ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
          ("axioms", toJson (axs.toList.map Name.toString))])
  logInfo m!"V16-INVENTORY {(Json.mkObj [("definitions", .arr definitions), ("modules", toJson (env.header.moduleNames.toList.map Name.toString)), ("inductives", .arr inductives), ("theorems", .arr theorems)]).compress}"
