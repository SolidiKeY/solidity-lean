import Solidity.Backend.InternalFlow.StoragePrograms
import Solidity.Evm.Compiler
import Solidity.Syntax.Splice

/-! Inhabited plain storage-return call, with real compiled prefix and heap growth.
The intrinsic program is explicit; no frontend lowering/world theorem is claimed. -/
namespace Solidity.Backend.InternalFlow.StorageReturnChecks
open Evm Evm.Memory PublishedDirectCalls

def C : Contract := contract!{
  struct Inner { uint value; uint other; }
  struct Outer { uint tag; Inner part; }
  Outer box;
  Inner spare;
  uint unrelated;
  Inner[] rows;
  function pick(uint[] memory a, uint seed) returns (Inner storage out) {
    out = box.part; out.value = seed + 31;
    uint[] memory scratch = new uint[](2); a = scratch; a[0] = 99; a[1] = 101;
  }
}
local instance : InContract := ⟨C⟩
def bases : Nat → Fin W := fun _ => wmod 0
def initial : State C [] := State.init C
def machine : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a = 0 then w[256] else if a = 127 then w[99] else w[0]}

theorem noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?

/-- The public state and allocator inputs have the same concrete witness. -/
theorem initial_repr : StateRepr 1 1 128 (Frag.init []) initial bases machine ∧
    StructAllocatorRepr initial.heap bases 128 (wmod 256) machine := by
  have hh : HeapRepr initial.heap bases 128 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr initial.heap bases 128 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated initial.heap bases := fun _ r => (noRef r).elim
  have hc : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0, W_pos⟩)
      (Machine.init (fun _ => 0) ⟨0, W_pos⟩) := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  refine ⟨⟨?_, hh, ?_, by decide, hs, hx, ?_⟩, ⟨⟨hh, ?_, fun r => (noRef r).elim⟩, hs, hx,
    fun r => (noRef r).elim⟩⟩
  · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    · intro p i; nomatch i
    · intro R i hi; nomatch i
    · intro R i hi; nomatch i
  · intro R i; nomatch i
  · intro s f R r hf; exact (noRef r).elim
  · refine ⟨by decide, by decide, rfl, ?_⟩
    intro a ha
    change 256 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl

private theorem actual_get {α : Type} (result : TRes α)
    (h : result.toOption.isSome = true) : result = .ok (result.toOption.get h) := by
  cases result with
  | error e => cases h
  | ok value => rfl


abbrev A : RefTy := .array (.prim .uint)
abbrev R : RefTy := .struct "Inner{value:uint;other:uint}"
abbrev Caller : Ctx := [.mem A,.mem A,.mem A,.val .uint,.val .uint]
abbrev Params : Ctx := [.val .uint,.mem A]
abbrev Input : Ctx := .alias R :: Params
abbrev BodyCtx : Ctx := .mem A :: Input
abbrev Final : Ctx := .alias R :: Caller

def part {Γ : Ctx} : SPath C Γ (.ref R) :=
  .loc (.field (.loc (.root "box" rfl)) "part" rfl)
def value {Γ : Ctx} (i : Idx Γ (.alias R)) : Loc C Γ (.prim .uint) :=
  .field (.alias i) "value" rfl

def callerPrefix : Prog C [] Caller := (sol{
  box.tag = 101; box.part.value = 41; box.part.other = 43;
  spare.value = 17; spare.other = 19; unrelated = 9;
  uint x = 42; uint y = 5;
  uint[] memory xs = new uint[](2); xs[0] = 7; xs[1] = 11;
  uint[] memory same = xs;
  uint[] memory other = new uint[](1); other[0] = 23;
} : Prog C [] Caller)
def prefixProducer : Calls.Program 1 (Frag.init []) callerPrefix :=
  (Calls.compile 1 (Frag.init []) callerPrefix).get (by decide +kernel)
attribute [irreducible] prefixProducer
def caller : Solidity.Out C [] Caller := (callerPrefix.run initial).toOption.get (by decide +kernel)
def arguments : Args C Caller Params :=
  .snoc (.snocMemory .nil A (.user "a") (.var (.there (.there .here)) rfl))
    .uint (.user "seed") (.simple (.local (.there (.there (.there (.there .here))))))
def ret : CallRet Caller [.alias R] Final := .storage R (.user "out")
def write {Γ : Ctx} (i : Idx Γ (.mem A)) (index v : Simple C Γ .uint) : Stmt C Γ Γ :=
  .assignMem (.index .dyn (.var i rfl) (.simple index)) (.val (.simple v))
def body : Prog C Input BodyCtx :=
  .cons (.rebind .here (.path part))
  (.cons (.assign (value .here) (.val (.binop .add rfl rfl
    (.simple (.local (.there .here))) (.simple (.lit 31 rfl)))))
  (.cons (.declMem A (.user "private") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl)
  (.cons (.rebindMem (.there (.there (.there .here))) (.alias (.var .here rfl)))
  (.cons (write .here (.lit 0 rfl) (.lit 99 rfl))
  (.cons (write .here (.lit 1 rfl) (.lit 101 rfl)) .nil)))))
def call : Stmt C Caller Final := .call "pick" arguments ret body

def expanded : Calls.Program 1 prefixProducer.frag
    (StorageCalls.expand arguments R (.user "out") body) :=
  (StoragePrograms.compile 1 prefixProducer.frag
    (StorageCalls.expand arguments R (.user "out") body)).get (by decide +kernel)
attribute [irreducible] expanded
def callProducer : Calls.Statement 1 prefixProducer.frag call :=
  StorageCalls.storageReturn "pick" arguments R (.user "out") body expanded (by decide +kernel)
attribute [irreducible] callProducer

def values : TEnv C caller.st.H Params := (arguments.evalT caller.st).toOption.get (by decide +kernel)
def entry : Solidity.Out C caller.st.H Input := ret.enterT (caller.st.withEnv values)
def bodyOutput : Solidity.Out C entry.st.H BodyCtx := (body.runR entry.st).toOption.get (by decide +kernel)
def exported : Solidity.Out C caller.st.H Final :=
  ⟨bodyOutput.st.withEnv (ret.leaveT (TEnv.wk (entry.ext.trans bodyOutput.ext) Caller caller.st.env)
    (TEnv.take [.alias R] (TEnv.drop body.ext bodyOutput.st.env))),entry.ext.trans bodyOutput.ext⟩
def suffix : Prog C Final Final :=
  .cons (.assign (value .here) (.val (.simple (.lit 84 rfl))))
  (.cons (.assignLocal (.there (.there (.there (.there (.there .here)))) ) (.read (value .here)))
  (.cons (write (.there (.there (.there .here))) (.lit 1 rfl)
    (.local (.there (.there (.there (.there (.there .here))))))) .nil))
def suffixProducer : Calls.Program 1 callProducer.frag suffix :=
  (Calls.compile 1 callProducer.frag suffix).get (by decide +kernel)
attribute [irreducible] suffixProducer
def final : Solidity.Out C exported.st.H Final := (suffix.run exported.st).toOption.get (by decide +kernel)
def program : Prog C Caller Final := .cons call suffix
def producer : Calls.Program 1 prefixProducer.frag program :=
  (StoragePrograms.compile 1 prefixProducer.frag program).get (by decide +kernel)
attribute [irreducible] producer
def checked : Compiler.Compilation 1 prefixProducer.frag program :=
  .memoryCalls producer (by decide +kernel)
attribute [irreducible] checked

theorem actual_prefix : callerPrefix.run initial = .ok caller := actual_get _ (by decide +kernel)
theorem actual_arguments : arguments.evalT caller.st = .ok values := actual_get _ (by decide +kernel)
theorem actual_body : body.runR entry.st = .ok bodyOutput := actual_get _ (by decide +kernel)
theorem actual_call : call.run caller.st = .ok exported :=
  InternalFlow.call_return arguments ret body.ext body.runR caller.st values actual_arguments bodyOutput actual_body
theorem actual_suffix : suffix.run exported.st = .ok final := actual_get _ (by decide +kernel)

-- No midpoint representation/capacity is postulated.
theorem represented : ∃ m₁ base₁ m₂ base₂ m₃ base₃,
    Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
    Evm.run callProducer.code m₁ = .ok m₂ 0 ∧ Evm.run suffixProducer.code m₂ = .ok m₃ 0 ∧
    StateRepr 1 1 128 prefixProducer.frag caller.st base₁ m₁ ∧
    StateRepr 1 1 128 callProducer.frag exported.st base₂ m₂ ∧
    StateRepr 1 1 128 suffixProducer.frag final.st base₃ m₃ ∧
    m₁.stack = machine.stack ∧ m₂.stack = m₁.stack ∧ m₃.stack = m₂.stack ∧
    BaseExtends caller.st.H base₁ base₂ ∧ BaseExtends exported.st.H base₂ base₃ ∧
    checked.Input 1 128 base₁ caller.st m₁ ∧ checked.Agrees 1 128 base₁ caller.st m₁ := by
  have whole : AllocationInput 1 128 (prefixProducer.cost initial + producer.cost caller.st) initial bases machine :=
    .inr ⟨by decide,wmod 256,initial_repr.2,by decide +kernel⟩
  obtain ⟨m₁,base₁,ht₁,hr₁,hk₁,he₁,ha₁⟩ := program_endpoint prefixProducer initial_repr.1
    (by decide +kernel) (whole.of_le (Nat.le_add_right _ _)) caller actual_prefix
  have space : AllocationInput 1 128 (producer.cost caller.st) caller.st base₁ m₁ := ha₁.nextInput whole
  obtain ⟨m₂,base₂,ht₂,hr₂,hk₂,he₂,ha₂⟩ := statement_endpoint
    (L := 1) (frame := 128) (σ := caller.st) (base := base₁) (m := m₁)
    callProducer hr₁ (by decide +kernel) (space.of_le (by decide +kernel)) exported actual_call
  have combined : AllocationInput 1 128 (callProducer.cost caller.st + suffixProducer.cost exported.st)
      caller.st base₁ m₁ := by
    have heq : callProducer.cost caller.st + suffixProducer.cost exported.st = producer.cost caller.st := by decide +kernel
    rw [heq]
    exact space
  have nextSpace : AllocationInput 1 128 (suffixProducer.cost exported.st) exported.st base₂ m₂ := ha₂.nextInput combined
  obtain ⟨m₃,base₃,ht₃,hr₃,hk₃,he₃,ha₃⟩ := program_endpoint
    (L := 1) (frame := 128) (σ := exported.st) (base := base₂) (m := m₂)
    suffixProducer hr₂ (by decide +kernel) nextSpace final actual_suffix
  have hi : checked.Input 1 128 base₁ caller.st m₁ := by
    apply (checked.memoryCalls_input (by decide +kernel) 1 128 base₁ caller.st m₁).mpr
    refine ⟨hr₁,by decide +kernel,?_⟩
    have heq : checked.allocationCost caller.st = producer.cost caller.st := by unfold checked; rfl
    rw [heq]
    exact space
  exact ⟨m₁,base₁,m₂,base₂,m₃,base₃,ht₁,ht₂,ht₃,hr₁,hr₂,hr₃,hk₁,hk₂,hk₃,he₂,he₃,hi,checked.correct hi⟩


/-- The full selected program reaches the composed actual source extension. -/
theorem actual_program : program.run caller.st =
    .ok (⟨final.st,exported.ext.trans final.ext⟩ : Solidity.Out C caller.st.H Final) := by
  rw [program,Prog.run_cons_ok actual_call,actual_suffix]
  rfl

/-- The actual selected whole-program code, not just separately compiled pieces,
reaches the represented final state with its true cost and transported identities. -/
theorem whole_endpoint : ∃ m₁ base₁ m₂ base₂,
    Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
    Evm.run producer.code m₁ = .ok m₂ 0 ∧
    StateRepr 1 1 128 producer.frag final.st base₂ m₂ ∧
    m₂.stack = machine.stack ∧ BaseExtends caller.st.H base₁ base₂ ∧
    GrowsAllocator 1 128 (producer.cost caller.st) caller.st base₁ m₁ final.st base₂ m₂ := by
  obtain ⟨m₁,base₁,mc,bc,ms,bs,hprefix,hcall,hsuffix,hr,hc,hs,hk,hkc,hks,hec,hes,hi,ha⟩ := represented
  have facts := (checked.memoryCalls_input (by unfold checked; rfl) 1 128 base₁ caller.st m₁).mp hi
  have capacity : AllocationInput 1 128 (producer.cost caller.st) caller.st base₁ m₁ := by
    simpa only [checked,Compiler.Compilation.allocationCost] using facts.2.2
  obtain ⟨m₂,base₂,ht,repr,stack,hex,alloc⟩ := program_endpoint
    (L := 1) (frame := 128) (σ := caller.st) (base := base₁) (m := m₁)
    producer hr (by decide +kernel) capacity
    (⟨final.st,exported.ext.trans final.ext⟩ : Solidity.Out C caller.st.H Final) actual_program
  exact ⟨m₁,base₁,m₂,base₂,hprefix,ht,repr,stack.trans hk,hex,alloc⟩

def identity {H : HTy} (r : Option (HRef H A)) : Option Nat := r.map (·.id)
def arrayObject {H : HTy} (hp : Heap H) (id : Nat) : Option (List Int) :=
  if h : H[id]? = some A then
    let r : HRef H A := ⟨id,h⟩
    some ((hp.len r .dyn : Int) :: (MObj.elems .dyn (hp.get r)).map (fun v => v.1))
  else none
def contents {Γ : Ctx} (σ : State C Γ) : Option (List (List Int)) :=
  (List.range σ.H.length).mapM (arrayObject σ.heap)
def refObs (r : Option (SRef C (.ref R))) : Option (Name × List Semantics.Selector) :=
  r.map (fun r => (r.root,r.path.labels))
def scalars (σ : State C Final) : List Int :=
  [σ.env.2.2.2.2.2.1.1,σ.env.2.2.2.2.1.1]
def aliases (σ : State C Final) : List (Option Nat) :=
  [identity σ.env.2.1,identity σ.env.2.2.1,identity σ.env.2.2.2.1]
def storageValues {Γ : Ctx} (σ : State C Γ) : Option (List Int) :=
  ([.read (.field (.loc (.root "box" rfl)) "tag" rfl),
    .read (.field part "value" rfl), .read (.field part "other" rfl),
    .read (.field (.loc (.root "spare" rfl)) "value" rfl),
    .read (.field (.loc (.root "spare" rfl)) "other" rfl),
    .read (.root "unrelated" rfl), .len (.loc (.root "rows" rfl)) rfl] : List (Val C Γ .uint)).mapM
      (fun v => (v.evalT σ).toOption.map (fun n => n.1))
def words (out : Evm.Out) (addresses : List Nat) : Option (List Word) :=
  match out with | .ok m _ => some (m.stack ++ addresses.map m.mem) | _ => none
def stores (out : Evm.Out) : Option (List Nat) :=
  match out with | .ok m _ => some ((List.range 7).map (fun n => m.store (.root n))) | _ => none

theorem argument_order : (values.1.1,identity values.2.1) = (42,some 0) := by decide +kernel
theorem source_prefix : (storageValues caller.st,contents caller.st) =
    (some [101,41,43,17,19,9,0],some [[2,7,11],[1,23]]) := by decide +kernel
theorem source_entry : (entry.st.H.length,refObs entry.st.env.1,identity entry.st.env.2.2.1) =
    (2,none,some 0) := by decide +kernel
theorem source_body : (storageValues bodyOutput.st,contents bodyOutput.st,
    [identity bodyOutput.st.env.1,identity bodyOutput.st.env.2.2.2.1]) =
    (some [101,73,43,17,19,9,0],some [[2,7,11],[1,23],[2,99,101]],[some 2,some 2]) := by decide +kernel
theorem source_export : (storageValues exported.st,contents exported.st,refObs exported.st.env.1) =
    (some [101,73,43,17,19,9,0],some [[2,7,11],[1,23],[2,99,101]],
      some ("box",[.field "part"])) := by decide +kernel
theorem source_caller_tail : (scalars exported.st,aliases exported.st) =
    ([42,5],[some 1,some 0,some 0]) := by decide +kernel
theorem source_suffix : (storageValues final.st,contents final.st,refObs final.st.env.1) =
    (some [101,84,43,17,19,9,0],some [[2,7,84],[1,23],[2,99,101]],
      some ("box",[.field "part"])) := by decide +kernel
theorem source_final_tail : (scalars final.st,aliases final.st) =
    ([84,5],[some 1,some 0,some 0]) := by decide +kernel

theorem target_prefix : words (Evm.run prefixProducer.code machine)
    [0,127,1,2,3,4,5,256,257,258,259,260] =
    some [w[77],w[261],w[99],w[42],w[5],w[256],w[256],w[259],w[2],w[7],w[11],w[1],w[23]] := by decide +kernel
theorem target_body : words (Evm.run (prefixProducer.code ++ expanded.code) machine)
    [0,127,1,2,3,4,5,6,7,8,9,256,257,258,259,260,261,262,263] =
    some [w[77],w[264],w[99],w[42],w[5],w[256],w[256],w[259],w[261],w[42],.slot (.root 1),w[261],
      w[2],w[7],w[11],w[1],w[23],w[2],w[99],w[101]] := by decide +kernel
theorem target_export : words (Evm.run (prefixProducer.code ++ callProducer.code) machine)
    [0,127,1,2,3,4,5,6,7,8,9,256,257,258,259,260,261,262,263] =
    some [w[77],w[264],w[99],w[42],w[5],w[256],w[256],w[259],.slot (.root 1),w[42],.slot (.root 1),w[261],
      w[2],w[7],w[11],w[1],w[23],w[2],w[99],w[101]] := by decide +kernel
theorem target_suffix : words (Evm.run (prefixProducer.code ++ producer.code) machine)
    [0,127,1,2,3,4,5,6,7,8,9,256,257,258,259,260,261,262,263] =
    some [w[77],w[264],w[99],w[84],w[5],w[256],w[256],w[259],.slot (.root 1),w[42],.slot (.root 1),w[261],
      w[2],w[7],w[84],w[1],w[23],w[2],w[99],w[101]] := by decide +kernel
theorem target_storage_order :
    [stores (Evm.run prefixProducer.code machine),
     stores (Evm.run (prefixProducer.code ++ callProducer.code) machine),
     stores (Evm.run (prefixProducer.code ++ producer.code) machine)] =
    [some [101,41,43,17,19,9,0],some [101,73,43,17,19,9,0],some [101,84,43,17,19,9,0]] := by decide +kernel

theorem exact_frame_cost :
    [prefixProducer.need,expanded.need,callProducer.need,suffixProducer.need,producer.need,
     prefixProducer.cost initial,callProducer.cost caller.st,suffixProducer.cost exported.st,producer.cost caller.st] =
    [5,9,9,6,9,5,3,0,3] := by decide +kernel
theorem exact_extensions : [caller.st.H.length,entry.st.H.length,bodyOutput.st.H.length,exported.st.H.length,final.st.H.length] =
    [2,2,3,3,3] := by decide +kernel

theorem wrong_root : refObs exported.st.env.1 ≠ some ("spare",[]) := by decide +kernel
theorem wrong_path : refObs exported.st.env.1 ≠ some ("box",[]) := by decide +kernel
theorem wrong_target_alias : words (Evm.run (prefixProducer.code ++ callProducer.code) machine) [6] ≠
    some [w[77],.slot (.root 3)] := by decide +kernel
theorem wrong_private_escape : words (Evm.run (prefixProducer.code ++ callProducer.code) machine) [6] ≠
    some [w[77],w[261]] := by decide +kernel
theorem wrong_scalar_destination : scalars final.st ≠ [42,84] := by decide +kernel
theorem wrong_missing_mutation : storageValues exported.st ≠ some [101,41,43,17,19,9,0] := by decide +kernel
theorem wrong_unrelated_root : storageValues final.st ≠ some [101,84,43,84,19,9,0] := by decide +kernel
theorem wrong_old_memory : contents final.st ≠ some [[2,99,84],[1,23],[2,99,101]] := by decide +kernel
theorem wrong_cost : prefixProducer.cost initial + producer.cost caller.st ≠ 11 := by decide +kernel

def failedBody : Prog C Input BodyCtx := .cons .revert body
def failedCall : Stmt C Caller Final := .call "failedPick" arguments ret failedBody
def failedProgram : Prog C Caller Final := .cons failedCall suffix
def failedProducer : Calls.Program 1 prefixProducer.frag failedProgram :=
  (StoragePrograms.compile 1 prefixProducer.frag failedProgram).get (by decide +kernel)
attribute [irreducible] failedProducer

theorem failed_call : failedCall.run caller.st = .error .revert :=
  InternalFlow.call_body_failure arguments ret failedBody.ext failedBody.runR caller.st values actual_arguments .revert rfl
theorem failed_source : failedProgram.run caller.st = .error .revert := by
  show TRun.seq failedCall.runR suffix.runR caller.st = _
  have h := failed_call
  simp only [TRun.seq,Stmt.run] at h ⊢
  rw [h]
theorem failed_cost : (failedProducer.allocates,failedProducer.cost caller.st) = (true,0) := by decide +kernel

theorem failed_target : Evm.run (prefixProducer.code ++ failedProducer.code) machine = .revert := by
  have capacity : AllocationInput 1 128 (prefixProducer.cost initial) initial bases machine :=
    .inr ⟨by decide,wmod 256,initial_repr.2,by decide +kernel⟩
  obtain ⟨m₁,base₁,ht,hr,hk,he,ha⟩ := program_endpoint prefixProducer initial_repr.1
    (by decide +kernel) capacity caller actual_prefix
  have noCost : AllocationInput 1 128 (failedProducer.cost caller.st) caller.st base₁ m₁ :=
    .inl (congrArg Prod.snd failed_cost)
  rw [run_append_ok ht]
  exact TuplePrograms.program_revert (L := 1) (frame := 128) (σ := caller.st) (base := base₁) (m := m₁)
    failedProducer hr (by decide +kernel) noCost failed_source

theorem public_refusal : (Compiler.compile 1 prefixProducer.frag program).isSome = false := by decide +kernel
theorem old_owned_refusal : (TuplePrograms.compile 1 prefixProducer.frag program).isSome = false := by decide +kernel
theorem owned_acceptance : (StoragePrograms.compile 1 prefixProducer.frag program).isSome = true := by decide +kernel

def unsetCall : Stmt C Caller Final := .call "unset" arguments ret (.nil : Prog C Input Input)
theorem unset_return_refusal : (StoragePrograms.compile 1 prefixProducer.frag (.cons unsetCall .nil)).isSome = false := by decide +kernel
theorem unset_source : ((unsetCall.run caller.st).toOption.map (fun o => o.st.env.1.isSome)) = some false := by decide +kernel

def fragilePath : SPath C Input (.ref R) :=
  .loc (.index (.arr .dyn) (.loc (.root "rows" rfl)) (.simple (.lit 0 rfl)))
theorem fragile_guard : spathIn (Frag.init Input) true fragilePath = false := rfl
theorem fragile_refusal : (StorageFrames.statement 1 (Frag.init Input)
    (.rebind .here (.path fragilePath))).isSome = false := rfl

def bytesBody : Prog C Input Input := .cons (.revertData [.bytes [0,7,0]]) .nil
theorem bytes_refusal : (StoragePrograms.compile 1 prefixProducer.frag
    (.cons (.call "bytes" arguments ret bytesBody) .nil)).isSome = false := by decide +kernel
theorem bytes_source : (Stmt.call "bytes" arguments ret bytesBody).run caller.st = .error (.revertWith [0,7,0]) :=
  InternalFlow.call_body_failure arguments ret bytesBody.ext bytesBody.runR caller.st values actual_arguments (.revertWith [0,7,0]) rfl

theorem recursion_refusal : (StoragePrograms.compile 1 prefixProducer.frag
    (.cons (.callRec "rec" 2 arguments ret (fun _ => .nil)) .nil)).isSome = false := by decide +kernel

#print axioms initial_repr
#print axioms noRef
#print axioms actual_prefix
#print axioms actual_arguments
#print axioms actual_body
#print axioms actual_call
#print axioms actual_suffix
#print axioms represented
#print axioms actual_program
#print axioms whole_endpoint
#print axioms argument_order
#print axioms source_prefix
#print axioms source_entry
#print axioms source_body
#print axioms source_export
#print axioms source_caller_tail
#print axioms source_suffix
#print axioms source_final_tail
#print axioms target_prefix
#print axioms target_body
#print axioms target_export
#print axioms target_suffix
#print axioms target_storage_order
#print axioms exact_frame_cost
#print axioms exact_extensions
#print axioms wrong_root
#print axioms wrong_path
#print axioms wrong_target_alias
#print axioms wrong_private_escape
#print axioms wrong_scalar_destination
#print axioms wrong_missing_mutation
#print axioms wrong_unrelated_root
#print axioms wrong_old_memory
#print axioms wrong_cost
#print axioms failed_call
#print axioms failed_source
#print axioms failed_cost
#print axioms failed_target
#print axioms public_refusal
#print axioms old_owned_refusal
#print axioms owned_acceptance
#print axioms unset_return_refusal
#print axioms unset_source
#print axioms fragile_guard
#print axioms fragile_refusal
#print axioms bytes_refusal
#print axioms bytes_source
#print axioms recursion_refusal
#print axioms StorageFrames.pushDead
#print axioms StorageFrames.pushAlias
#print axioms StorageFrames.setAlias
#print axioms StorageFrames.declareUnset
#print axioms StorageFrames.bindPath
#print axioms StorageFrames.declarePath
#print axioms StorageFrames.statement
#print axioms StorageCalls.expand_runSt
#print axioms StorageCalls.expand_runR
#print axioms StorageCalls.storageReturn
#print axioms StoragePrograms.compile
end Solidity.Backend.InternalFlow.StorageReturnChecks
