import Solidity.Roadmap.V16.FiniteMemoryCompilation
import Solidity.Roadmap.V16.CompilerConsumer
import Solidity.Roadmap.V16.SpecificationControls
import Solidity.Evm.MemoryAllocSourceExamples
import Lean

/-! Actual public core callerPrefix and allocating memory suffix. This consumes
existing algorithms and richer input witnesses; no duplicate execution model. -/
set_option autoImplicit false
open Lean Elab Term in
elab "publishedMixedAllocation%" n:ident : term => do
  let name := mkPrivateNameCore `Solidity.Evm.MemoryAllocSourceExamples
    (`Solidity.Evm.Memory.AllocSourceExamples ++ n.getId)
  unless (← getEnv).contains name do throwError "missing published allocation fixture {name}"
  return mkConst name

namespace Solidity.Roadmap.V16.MixedMemoryControls
open Solidity.Evm
abbrev K := publishedMixedAllocation% C
abbrev Γ : Ctx := publishedMixedAllocation% Γ
abbrev Δ : Ctx := publishedMixedAllocation% Δ
abbrev initial := publishedMixedAllocation% σ
abbrev bases := publishedMixedAllocation% bases
abbrev cursor := publishedMixedAllocation% cursor
def machine : Machine := { (publishedMixedAllocation% machine) with stack := [w[77]] }
def callerPrefix : Prog K Γ Γ := .cons (.assignLocal .here (.simple (.lit 3 rfl))) .nil
def suffix : Prog K Γ Δ := publishedMixedAllocation% program
attribute [irreducible] suffix
def P : Prog K Γ Δ := constructionAppend callerPrefix suffix
attribute [irreducible] P
def prefixCompiled : Compiler.Compilation 1 (Frag.init Γ) callerPrefix :=
  (Compiler.compile 1 (Frag.init Γ) callerPrefix).get (by decide +kernel)
def suffixCompiled : Compiler.Compilation 1 (Frag.init Γ) suffix := by
  simpa only [suffix] using (publishedMixedAllocation% compiled)
def compiled : Compiler.Compilation 1 (Frag.init Γ) P :=
  (Compiler.compile 1 (Frag.init Γ) P).get (by unfold P callerPrefix; decide +kernel)
attribute [irreducible] prefixCompiled suffixCompiled compiled

theorem prefix_core : prefixCompiled.usesMemory = false := by decide +kernel
theorem suffix_memory : suffixCompiled.isMemory = true := by decide +kernel
theorem whole_memory : compiled.isMemory = true := by decide +kernel

def lowPrefix : Memory.CompiledProg 1 (Frag.init Γ) callerPrefix :=
  (Memory.compileProg 1 (Frag.init Γ) callerPrefix).get (by decide +kernel)
attribute [irreducible] lowPrefix

theorem prefix_low_accepted : Memory.compileProg 1 (Frag.init Γ) callerPrefix = some lowPrefix := by
  with_unfolding_all
    exact (Option.some_get (x := Memory.compileProg 1 (Frag.init Γ) callerPrefix) (by decide +kernel)).symm

theorem prefix_accepted : Compiler.compile 1 (Frag.init Γ) callerPrefix = some prefixCompiled := by
  with_unfolding_all
    exact (Option.some_get (x := Compiler.compile 1 (Frag.init Γ) callerPrefix) (by decide +kernel)).symm

theorem low_prefix_code : lowPrefix.code = prefixCompiled.code := by
  with_unfolding_all rfl
theorem low_prefix_fragment : lowPrefix.frag = Frag.init Γ := by decide +kernel

theorem suffix_accepted : Compiler.compile 1 (Frag.init Γ) suffix = some suffixCompiled := by
  with_unfolding_all
    exact (Option.some_get (x := Compiler.compile 1 (Frag.init Γ) suffix) (by decide +kernel)).symm

theorem whole_accepted : Compiler.compile 1 (Frag.init Γ) P = some compiled := by
  with_unfolding_all
    exact (Option.some_get (x := Compiler.compile 1 (Frag.init Γ) P) (by decide +kernel)).symm

/-- Canonical mixed code is derived from BOTH actual compilation functions.
All source, fragment and low/public code links are checked here, not assumed. -/
theorem code_composes : compiled.code = prefixCompiled.code ++ suffixCompiled.code := by
  have joined := finite_memory_compile_append_link lowPrefix
    (finiteMemoryCertificate suffixCompiled suffix_memory) low_prefix_fragment
    prefix_low_accepted (finite_memory_compile_inversion suffixCompiled suffix_memory suffix_accepted)
  have joinedP : finiteMemoryShape 1 (Frag.init Γ) P = some
      ((finiteMemoryCertificate suffixCompiled suffix_memory).frag,
        lowPrefix.code ++ (finiteMemoryCertificate suffixCompiled suffix_memory).code) := by
    simpa only [P] using joined
  have lowWhole := finite_memory_compile_inversion compiled whole_memory whole_accepted
  have actual : finiteMemoryShape 1 (Frag.init Γ) P = some
      ((finiteMemoryCertificate compiled whole_memory).frag,
        (finiteMemoryCertificate compiled whole_memory).code) := by
    simp only [finiteMemoryShape,lowWhole,Option.map_some]
  have eq := Option.some.inj (actual.symm.trans joinedP)
  simpa only [finite_memory_certificate_code,low_prefix_code] using congrArg Prod.snd eq

/-- Real reached state; core Sim alone is not assumed to imply Memory.StateRepr. -/
def reached : State K Γ := initial.setLocal .here (Memory.indexValue ⟨3,by decide⟩)
def reachedMachine : Machine := Memory.writeMachine machine 1 w[3]

theorem initial_repr : Memory.StateRepr 1 1 6 (Frag.init Γ) initial bases machine :=
  Memory.AllocSourceExamples.initial_repr.1.stack [w[77]]
theorem initial_allocator : Memory.StructAllocatorRepr initial.heap bases 6 cursor machine :=
  Memory.AllocSourceExamples.initial_repr.2.stack [w[77]]

theorem prefix_source : callerPrefix.run initial = .ok ⟨reached,List.prefix_refl _⟩ := by rfl
theorem prefix_target : run prefixCompiled.code machine = .ok reachedMachine 0 := by
  with_unfolding_all rfl

theorem reached_repr : Memory.StateRepr 1 1 6 (Frag.init Γ) reached bases reachedMachine :=
  initial_repr.setVal .here (Memory.indexValue ⟨3,by decide⟩) w[3] (ReprV.uint_of rfl)
theorem reached_allocator : Memory.StructAllocatorRepr reached.heap bases 6 cursor reachedMachine :=
  initial_allocator.localWrite 1 (by decide) (by decide) w[3]

theorem prefix_input : prefixCompiled.Input 1 6 bases initial machine := by
  with_unfolding_all
    exact ⟨initial_repr.core,by decide +kernel⟩

def prefixPost : Spec K Γ := .eq (.pvV .here) (.app0 (.lit ⟨3,by decide⟩))
theorem prefix_diamond : Spec.sat initial (.diamond callerPrefix prefixPost) := by
  rw [Spec.sat,prefix_source]
  exact ⟨⟨3,by decide⟩,rfl,rfl⟩

/-- Also consume the REAL public core certificate; this weak Sim relation
is retained, and is not cast into the separately constructed rich heap relation. -/
theorem prefix_representation : prefixCompiled.Rep 1 6 bases initial machine reached reachedMachine := by
  obtain ⟨o,m',hs,ht,stack,rep,hpost⟩ :=
    compiler_nonpaying_diamond prefixCompiled prefix_input (by decide +kernel) prefix_diamond
  have stateEq : o = ⟨reached,List.prefix_refl _⟩ := Except.ok.inj (hs.symm.trans prefix_source)
  subst o
  have machineEq : m' = reachedMachine := by cases ht.symm.trans prefix_target; rfl
  subst m'
  change prefixCompiled.Rep 1 6 bases initial machine reached reachedMachine at rep
  exact rep

theorem suffix_cost : suffixCompiled.allocationCost reached = 5 := by decide +kernel
theorem whole_cost : compiled.allocationCost initial = 5 := by decide +kernel
theorem stale_initial_cost : suffixCompiled.allocationCost initial = 4 := by decide +kernel

theorem suffix_input : suffixCompiled.Input 1 6 bases reached reachedMachine := by
  apply (suffixCompiled.memory_input suffix_memory 1 6 bases reached reachedMachine).mpr
  exact ⟨reached_repr,by decide +kernel,.inr ⟨by decide,cursor,reached_allocator,by decide +kernel⟩⟩
theorem whole_input : compiled.Input 1 6 bases initial machine := by
  apply (compiled.memory_input whole_memory 1 6 bases initial machine).mpr
  exact ⟨initial_repr,by decide +kernel,.inr ⟨by decide,cursor,initial_allocator,by decide +kernel⟩⟩

def post : Spec K Δ :=
  .and (.eq (.app2 .mlen (.app0 .memory) (.pvI .here)) (.app0 (.lit ⟨0,by decide⟩)))
    (.eq (.app2 .mlen (.app0 .memory) (.pvI (.there .here))) (.app0 (.lit ⟨3,by decide⟩)))

theorem whole_positive : (P.run initial).toOption.isSome = true := by unfold P callerPrefix; decide +kernel
def output : Solidity.Out K initial.H Δ := (P.run initial).toOption.get whole_positive
attribute [irreducible] output
theorem whole_source : P.run initial = .ok output := by
  have get_source {α : Type} {r : TRes α} (h : r.toOption.isSome = true) : r = .ok (r.toOption.get h) := by
    cases r with
    | error e => cases h
    | ok o => rfl
  simpa only [output] using get_source whole_positive

theorem output_post : Spec.sat output.st post := by
  constructor
  · exact ⟨⟨0,by decide⟩,by decide +kernel,rfl⟩
  · exact ⟨⟨3,by decide⟩,by decide +kernel,rfl⟩
theorem diamond : Spec.sat initial (.diamond P post) := by
  simpa only [Spec.sat,whole_source] using output_post

theorem represented : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ compiled.Rep 1 6 bases initial machine o.st m' ∧ Spec.sat o.st post :=
  finite_heap_diamond compiled (.inl whole_memory) whole_input diamond


theorem source_sequence : P.run initial = suffix.run reached := by
  unfold P
  rw [intrinsic_append_run,prefix_source]
  simp only [Except.bind]
  cases suffix.run reached <;> rfl

theorem suffix_source : suffix.run reached = .ok output := source_sequence.symm.trans whole_source

theorem suffix_diamond : Spec.sat reached (.diamond suffix post) := by
  simpa only [Spec.sat,suffix_source] using output_post

/-- Both real stage executions and BOTH complete representations are retained.
The suffix Input was constructed from the literal update, not a new premise. -/
theorem staged : ∃ o m', callerPrefix.run initial = .ok ⟨reached,List.prefix_refl _⟩ ∧
    run prefixCompiled.code machine = .ok reachedMachine 0 ∧
    suffix.run reached = .ok o ∧ run suffixCompiled.code reachedMachine = .ok m' 0 ∧
    P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ prefixCompiled.Rep 1 6 bases initial machine reached reachedMachine ∧
    suffixCompiled.Rep 1 6 bases reached reachedMachine o.st m' ∧
    compiled.Rep 1 6 bases initial machine o.st m' ∧ Spec.sat o.st post := by
  obtain ⟨o,m',hs,ht,stack,rep,hpost⟩ :=
    finite_heap_diamond suffixCompiled (.inl suffix_memory) suffix_input suffix_diamond
  have whole : run compiled.code machine = .ok m' 0 := by
    rw [code_composes,Evm.run_append_ok prefix_target]
    exact ht
  obtain ⟨u,n,hsource,htarget,_,repr,_⟩ := represented
  have stateEq : u = o := Except.ok.inj (hsource.symm.trans (source_sequence.trans hs))
  subst u
  have machineEq : n = m' := by cases htarget.symm.trans whole; rfl
  subst n
  exact ⟨o,m',prefix_source,prefix_target,hs,ht,source_sequence.trans hs,whole,stack,prefix_representation,rep,repr,hpost⟩

/-- Retain the published COMPLETE source observation and every target local,
old sentinel and all allocated cells, in order, including the new final cell20. -/
def targetObserve : Evm.Out → Option (List Nat)
  | .ok m _ => do
    let cells ← [0,1,2,3,5,16,17,18,19,20].mapM (fun a => (publishedMixedAllocation% wordValue) (m.mem a))
    pure (m.stack.length :: cells)
  | _ => none

theorem source_observed : (publishedMixedAllocation% sourceObserve) (P.run initial) = some [2,1,0,0,3,3] := by
  unfold P callerPrefix
  decide +kernel
theorem target_observed : targetObserve (run compiled.code machine) = some [1,21,3,16,20,99,3,0,0,0,0] := by
  decide +kernel

theorem ordered : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ compiled.Rep 1 6 bases initial machine o.st m' ∧ Spec.sat o.st post ∧
    (publishedMixedAllocation% sourceObserve) (.ok o) = some [2,1,0,0,3,3] ∧
    targetObserve (.ok m' 0) = some [1,21,3,16,20,99,3,0,0,0,0] := by
  obtain ⟨o,m',_,_,_,_,hs,ht,stack,_,_,rep,hpost⟩ := staged
  refine ⟨o,m',hs,ht,stack,rep,hpost,?_,?_⟩
  · rw [← hs];exact source_observed
  · rw [← ht];exact target_observed

theorem wrong_stale_cost : compiled.allocationCost initial ≠ suffixCompiled.allocationCost initial := by
  rw [whole_cost,stale_initial_cost]
  decide

theorem wrong_frame : ¬ compiled.Input 1 3 bases initial machine := by
  intro h
  have bound := ((compiled.memory_input whole_memory 1 3 bases initial machine).mp h).2.1
  have no : ¬ 1 + Memory.frameNeedProg P ≤ 3 := by decide +kernel
  exact no bound

theorem wrong_reached_input : ¬ suffixCompiled.Input 1 6 bases initial reachedMachine := by
  intro h
  have repr := ((suffixCompiled.memory_input suffix_memory 1 6 bases initial reachedMachine).mp h).1
  have cell := repr.core.vals (.here : Idx Γ (.val .uint))
  change ∃ a : Fin W, w[3] = Word.val a ∧ (2 : Int) = a.val at cell
  obtain ⟨a,word,number⟩ := cell
  have address := congrArg Fin.val (Word.val.inj word)
  change (3 : Nat) = a.val at address
  omega

theorem wrong_cursor : ¬ ∃ m', run compiled.code machine = .ok m' 0 ∧
    targetObserve (.ok m' 0) = some [1,20,3,16,20,99,3,0,0,0,0] := by
  rintro ⟨m',ht,wrong⟩
  obtain ⟨o,n,hs,hn,_,_,_,_,good⟩ := ordered
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  rw [wrong] at good
  cases good

theorem exact_allocator : ∃ o m' base', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = [w[77]] ∧
    Memory.StateRepr 1 1 6 compiled.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.StructAllocatorRepr o.st.heap base' 6 ⟨21,by decide⟩ m' := by
  obtain ⟨o,m',hs,ht,stack,rep,_,_,_⟩ := ordered
  obtain ⟨base',repr,extension,grows⟩ := (finite_memory_rep_iff compiled whole_memory).mp rep
  have capacity : cursor.val + compiled.allocationCost initial < W := by rw [whole_cost];decide
  have allocator := grows cursor (by decide) initial_allocator capacity
  have at21 : Memory.StructAllocatorRepr o.st.heap base' 6 ⟨21,by decide⟩ m' := by
    simpa only [whole_cost] using allocator
  exact ⟨o,m',base',hs,ht,stack,repr,extension,at21⟩

theorem wrong_source_length : (publishedMixedAllocation% sourceObserve) (P.run initial) ≠ some [2,1,0,0,2,3] := by
  rw [source_observed]
  decide

theorem wrong_alias : ¬ ∃ m', run compiled.code machine = .ok m' 0 ∧
    targetObserve (.ok m' 0) = some [1,21,3,16,16,99,3,0,0,0,0] := by
  rintro ⟨m',ht,wrong⟩
  obtain ⟨o,n,hs,hn,_,_,_,_,good⟩ := ordered
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  rw [wrong] at good
  cases good

theorem wrong_failure : run compiled.code machine ≠ .revert := by
  intro h
  obtain ⟨o,n,_,ht,_⟩ := ordered
  rw [h] at ht
  cases ht

theorem stale_budget_not_capacity : (W - 5) + suffixCompiled.allocationCost initial < W ∧
    ¬ (W - 5) + compiled.allocationCost initial < W := by
  rw [whole_cost,stale_initial_cost]
  decide +kernel


/-- Actual unchanged Spec.sat composition, not a rule/closer or target change. -/
theorem nested_box : Spec.sat initial (.box callerPrefix (.box suffix post)) := by
  have box : Spec.sat initial (.box P post) := by
    simpa only [Spec.sat,whole_source] using output_post
  apply (intrinsic_append_box_iff callerPrefix suffix initial post).mp
  simpa only [P] using box

theorem nested_diamond : Spec.sat initial (.diamond callerPrefix (.diamond suffix post)) := by
  apply (intrinsic_append_diamond_iff callerPrefix suffix initial post).mp
  simpa only [P] using diamond

theorem false_nested_diamond : ¬ Spec.sat initial (.diamond callerPrefix (.diamond suffix (.not .tt))) := by
  intro h
  have bad : Spec.sat initial (.diamond P (.not .tt)) := by
    simpa only [P] using (intrinsic_append_diamond_iff callerPrefix suffix initial (.not .tt)).mpr h
  obtain ⟨o,m',hs,ht,stack,rep,post⟩ := finite_heap_diamond compiled (.inl whole_memory) whole_input bad
  exact post trivial

namespace halts
abbrev C := TransactionControls.contract
abbrev start := SpecificationControls.entryState
def payloadP : Prog C [] [] := TransactionControls.system.call true
def skippedP : Prog C [] [] := .cons (.revertData [.bytes [8]]) .nil

theorem payload_source : payloadP.run start = .error (.revertWith [9]) := rfl

theorem payload_append : (constructionAppend payloadP skippedP).run start = .error (.revertWith [9]) := by
  rw [intrinsic_append_run,payload_source]
  rfl

theorem wrong_payload : (constructionAppend payloadP skippedP).run start ≠ .error (.revertWith [8]) := by
  intro h
  rw [payload_append] at h
  cases h

def exhaustedP : Prog C [] [] := .recBase
theorem exhaustion_source : exhaustedP.run start = .error .exhausted := rfl

theorem exhaustion_append : (constructionAppend exhaustedP skippedP).run start = .error .exhausted := by
  rw [intrinsic_append_run,exhaustion_source]
  rfl

theorem exhaustion_diamond : Spec.sat start (.diamond (constructionAppend exhaustedP skippedP) .tt) := by
  apply (intrinsic_append_diamond_iff exhaustedP skippedP start .tt).mpr
  rfl

theorem exhaustion_no_success : ∀ o, (constructionAppend exhaustedP skippedP).run start ≠ .ok o := by
  intro o h
  rw [exhaustion_append] at h
  cases h

theorem exhaustion_refused : Compiler.compile 0 (Frag.init []) exhaustedP = none := rfl
end halts


namespace profileGap
/-- These constructors are admitted intrinsic syntax, but are not asserted to
have full SourceSpec admission. This is an actual backend-combination control. -/
def assertionPrefix : Prog K Γ Γ := .cons (.assert (.simple (.bool true))) .nil
def assertionThenAllocation : Prog K Γ Δ := constructionAppend assertionPrefix suffix
attribute [irreducible] assertionThenAllocation

theorem assertion_prefix_accepted : (Compiler.compile 1 (Frag.init Γ) assertionPrefix).isSome = true := by
  decide +kernel

theorem assertion_allocation_source_success : (assertionThenAllocation.run initial).toOption.isSome = true := by
  unfold assertionThenAllocation assertionPrefix
  decide +kernel

/-- Exact current public refusal; no reserved producer is modified to hide it. -/
theorem assertion_allocation_refused : Compiler.compile 1 (Frag.init Γ) assertionThenAllocation = none := by
  with_unfolding_all rfl
end profileGap

end Solidity.Roadmap.V16.MixedMemoryControls

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
