import Solidity.Backend.InternalFlow.MixedStoreAliasFrame
import Solidity.Backend.InternalFlow.MemoryStoreLocalFrame
import Solidity.Backend.InternalFlow.CallerView
import Solidity.Backend.InternalFlow.StoragePrograms
import Solidity.Backend.InternalFlow.FragilePrograms
import Solidity.Backend.InternalFlow.StoragePrefixFrame
import Solidity.Evm.Compiler
import Solidity.Syntax.Splice

/-! Actual dynamic-storage prefix, indexed return and memory-growing call.
No supplied populated midpoint or alternate semantics is used. -/
namespace Solidity.Backend.InternalFlow.FragileReturnChecks
open Evm Evm.Memory PublishedDirectCalls

def C : Contract := contract!{
  struct Item { uint value; uint other; }
  Item seed0;
  Item seed1;
  Item[] rows;
  uint unrelated;
  function pick(uint[] memory a, uint seed, uint index) returns (Item storage out) {
    out = rows[index]; out.value = seed + 31;
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
abbrev R : RefTy := .struct "Item{value:uint;other:uint}"
abbrev Caller : Ctx := [.mem A,.mem A,.mem A,.val .uint,.val .uint]
abbrev Params : Ctx := [.val .uint,.val .uint,.mem A]
abbrev Input : Ctx := .alias R :: Params
abbrev BodyCtx : Ctx := .mem A :: Input
abbrev Final : Ctx := .alias R :: Caller

def rows {Γ : Ctx} : SPath C Γ (.array (.ref R)) := .loc (.root "rows" rfl)
def row {Γ : Ctx} (i : Val C Γ .uint) : SPath C Γ (.ref R) := .loc (.index (.arr .dyn) rows i)
def value {Γ : Ctx} (i : Idx Γ (.alias R)) : Loc C Γ (.prim .uint) := .field (.alias i) "value" rfl

def storagePrefix : Prog C [] [] := (sol{
  seed0.value = 11; seed0.other = 13;
  seed1.value = 21; seed1.other = 23;
  rows.push(seed0); rows.push(seed1); unrelated = 9;
} : Prog C [] [])
def stored : Solidity.Out C [] [] := (storagePrefix.run initial).toOption.get (by decide +kernel)
def storageCode : List Instr := Evm.compileProg 1 storagePrefix

private theorem core_endpoint {C' : Contract} {Γ Δ : Ctx} {L b : Nat}
    {F : Frag Γ} {G : Frag Δ} {P : Prog C' Γ Δ} {σ : State C' Γ} {m : Machine}
    (fragment : inFragP F P = some G) (repr : Sim C' L b F σ m)
    (room : L + Evm.Prog.pushes P ≤ Lmax) (pays : Evm.Prog.pays P = false)
    (o : Solidity.Out C' σ.H Δ) (executed : P.run σ = .ok o) :
    ∃ m', Evm.run (Evm.compileProg b P) m = .ok m' 0 ∧ m'.stack = m.stack ∧
      Sim C' (L + Evm.Prog.pushes P) b G o.st m' := by
  rcases Evm.compile_exact fragment repr room pays with ⟨o',m',hs,ht,hk,hrepr⟩ | ⟨hs,ht⟩ | ⟨hs,ht⟩
  · have he : o' = o := Except.ok.inj (hs.symm.trans executed)
    subst o'
    exact ⟨m',ht,hk,hrepr⟩
  · rcases hs with hs | ⟨_,hs⟩ <;> rw [executed] at hs <;> contradiction
  · rw [executed] at hs
    contradiction

theorem actual_storage : storagePrefix.run initial = .ok stored := actual_get _ (by decide +kernel)

theorem storage_prefix_repr :
    ∃ reached, Evm.run storageCode machine = .ok reached 0 ∧
    StateRepr 3 1 128 (Frag.init []) stored.st bases reached ∧
    StructAllocatorRepr stored.st.heap bases 128 (wmod 256) reached ∧ reached.stack = machine.stack := by
  obtain ⟨m,ht,hk,hc⟩ := core_endpoint (P := storagePrefix) (b := 1) (L := 1)
    (F := Frag.init []) (G := Frag.init []) (by decide +kernel) initial_repr.1.core
    (by decide +kernel) (by decide +kernel) stored actual_storage
  have hm : m.mem = machine.mem := StoragePrefixFrame.run_mem storageCode (by decide +kernel) ht
  have core : Sim C 3 1 (Frag.init []) stored.st m := by
    simpa only [show Evm.Prog.pushes storagePrefix = 2 from by decide +kernel] using hc
  have sourceFrame := StoragePrefixFrame.store_prog_frame storagePrefix (by decide +kernel) actual_storage
  have alloc : StructAllocatorRepr stored.st.heap bases 128 (wmod 256) m :=
    StoragePrefixFrame.allocator_heap sourceFrame.H.symm sourceFrame.heap.symm (initial_repr.2.mem_eq hm)
  have noStoredRef {T : RefTy} (r : HRef stored.st.H T) : False := by
    have he : stored.st.H = [] := sourceFrame.H
    rw [he] at r
    exact noRef r
  refine ⟨m,ht,⟨core,⟨fun r => (noStoredRef r).elim,fun r => (noStoredRef r).elim,
    fun r => (noStoredRef r).elim⟩,?_,by decide,⟨fun r => (noStoredRef r).elim,
      fun r => (noStoredRef r).elim,fun r => (noStoredRef r).elim⟩,
    fun _ r => (noStoredRef r).elim,?_⟩,alloc,hk⟩
  · intro T i
    nomatch i
  · intro s f R r hf
    exact (noStoredRef r).elim

def memoryPrefix : Prog C [] Caller := (sol{
  uint x = 42; uint y = 1;
  uint[] memory xs = new uint[](2); xs[0] = 7; xs[1] = 11;
  uint[] memory same = xs;
  uint[] memory other = new uint[](1); other[0] = 23;
} : Prog C [] Caller)
def prefixProducer : Calls.Program 1 (Frag.init []) memoryPrefix :=
  (Calls.compile 1 (Frag.init []) memoryPrefix).get (by decide +kernel)
attribute [irreducible] prefixProducer
def caller : Solidity.Out C stored.st.H Caller := (memoryPrefix.run stored.st).toOption.get (by decide +kernel)
def prefixCode : List Instr := storageCode ++ prefixProducer.code

def arguments : Args C Caller Params :=
  .snoc (.snoc (.snocMemory .nil A (.user "a") (.var (.there (.there .here)) rfl))
    .uint (.user "seed") (.simple (.local (.there (.there (.there (.there .here)))))))
    .uint (.user "index") (.simple (.local (.there (.there (.there .here)))))
def ret : CallRet Caller [.alias R] Final := .storage R (.user "out")
def write {Γ : Ctx} (i : Idx Γ (.mem A)) (index v : Simple C Γ .uint) : Stmt C Γ Γ :=
  .assignMem (.index .dyn (.var i rfl) (.simple index)) (.val (.simple v))
def body : Prog C Input BodyCtx :=
  .cons (.rebind .here (.path (row (.simple (.local (.there .here))))))
  (.cons (.assign (value .here) (.val (.binop .add rfl rfl
    (.simple (.local (.there (.there .here)))) (.simple (.lit 31 rfl)))))
  (.cons (.declMem A (.user "scratch") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl)
  (.cons (.rebindMem (.there (.there (.there (.there .here)))) (.alias (.var .here rfl)))
  (.cons (write .here (.lit 0 rfl) (.lit 99 rfl))
  (.cons (write .here (.lit 1 rfl) (.lit 101 rfl)) .nil)))))
def call : Stmt C Caller Final := .call "pick" arguments ret body

def expanded : Calls.Program 1 prefixProducer.frag (StorageCalls.expand arguments R (.user "out") body) :=
  (FragilePrograms.compile 1 prefixProducer.frag (StorageCalls.expand arguments R (.user "out") body)).get (by decide +kernel)
attribute [irreducible] expanded
def callProducer : Calls.Statement 1 prefixProducer.frag call :=
  FragileCalls.storageReturnFragile "pick" arguments R (.user "out") body expanded (by decide +kernel)
attribute [irreducible] callProducer

def values : TEnv C caller.st.H Params := (arguments.evalT caller.st).toOption.get (by decide +kernel)
def entry : Solidity.Out C caller.st.H Input := ret.enterT (caller.st.withEnv values)
def bodyOutput : Solidity.Out C entry.st.H BodyCtx := (body.runR entry.st).toOption.get (by decide +kernel)
def exported : Solidity.Out C caller.st.H Final :=
  ⟨bodyOutput.st.withEnv (ret.leaveT (TEnv.wk (entry.ext.trans bodyOutput.ext) Caller caller.st.env)
    (TEnv.take [.alias R] (TEnv.drop body.ext bodyOutput.st.env))),entry.ext.trans bodyOutput.ext⟩
def suffix : Prog C Final Final :=
  .cons (.assign (value .here) (.val (.simple (.lit 84 rfl))))
  (.cons (.assignLocal (.there (.there (.there (.there (.there .here))))) (.read (value .here)))
  (.cons (write (.there (.there (.there .here))) (.lit 1 rfl)
    (.local (.there (.there (.there (.there (.there .here))))))) .nil))
def suffixProducer : Calls.Program 1 callProducer.frag suffix :=
  (Calls.compile 1 callProducer.frag suffix).get (by decide +kernel)
attribute [irreducible] suffixProducer
def final : Solidity.Out C exported.st.H Final := (suffix.run exported.st).toOption.get (by decide +kernel)
def program : Prog C Caller Final := .cons call suffix
def producer : Calls.Program 1 prefixProducer.frag program :=
  (FragilePrograms.compile 1 prefixProducer.frag program).get (by decide +kernel)
attribute [irreducible] producer
def checked : Compiler.Compilation 1 prefixProducer.frag program := .memoryCalls producer (by decide +kernel)
attribute [irreducible] checked

theorem actual_prefix : memoryPrefix.run stored.st = .ok caller := actual_get _ (by decide +kernel)
theorem actual_arguments : arguments.evalT caller.st = .ok values := actual_get _ (by decide +kernel)
theorem actual_body : body.runR entry.st = .ok bodyOutput := actual_get _ (by decide +kernel)
theorem actual_call : call.run caller.st = .ok exported :=
  InternalFlow.call_return arguments ret body.ext body.runR caller.st values actual_arguments bodyOutput actual_body
theorem actual_suffix : suffix.run exported.st = .ok final := actual_get _ (by decide +kernel)
theorem actual_program : program.run caller.st = .ok (⟨final.st,exported.ext.trans final.ext⟩ : Solidity.Out C caller.st.H Final) := by
  rw [program,Prog.run_cons_ok actual_call,actual_suffix]
  rfl


/-- The actual storage-push prefix is outside the old frame predicate. -/
theorem original_within_refusal : Prog.within .nonpayable storagePrefix = false := by decide +kernel

theorem prefix_endpoint (tail : Nat)
    (room : 256 + (prefixProducer.cost stored.st + tail) < W) :
    ∃ m₁ base₁, Evm.run prefixCode machine = .ok m₁ 0 ∧
      StateRepr 3 1 128 prefixProducer.frag caller.st base₁ m₁ ∧ m₁.stack = machine.stack ∧
      AllocationInput 1 128 tail caller.st base₁ m₁ := by
  obtain ⟨start,hstart,repr,alloc,hstack⟩ := storage_prefix_repr
  have whole : AllocationInput 1 128 (prefixProducer.cost stored.st + tail) stored.st bases start :=
    .inr ⟨by decide,wmod 256,alloc,by simpa only [show (wmod 256).val = 256 from by decide +kernel] using room⟩
  obtain ⟨m₁,base₁,ht,hr,hk,he,ha⟩ := program_endpoint
    (L := 3) (frame := 128) (σ := stored.st) (base := bases) (m := start)
    prefixProducer repr (by decide +kernel) (whole.of_le (Nat.le_add_right _ _)) caller actual_prefix
  refine ⟨m₁,base₁,?_,hr,hk.trans hstack,ha.nextInput whole⟩
  rw [prefixCode,run_append_ok hstart]
  exact ht

theorem whole_endpoint : ∃ m₁ base₁ m₂ base₂,
    Evm.run prefixCode machine = .ok m₁ 0 ∧ Evm.run producer.code m₁ = .ok m₂ 0 ∧
    StateRepr 3 1 128 producer.frag final.st base₂ m₂ ∧ m₂.stack = machine.stack ∧
    BaseExtends caller.st.H base₁ base₂ ∧
    GrowsAllocator 1 128 (producer.cost caller.st) caller.st base₁ m₁ final.st base₂ m₂ ∧
    checked.Input 3 128 base₁ caller.st m₁ ∧ checked.Agrees 3 128 base₁ caller.st m₁ := by
  obtain ⟨m₁,base₁,hpre,repr,stack,space⟩ := prefix_endpoint (producer.cost caller.st) (by decide +kernel)
  obtain ⟨m₂,base₂,ht,hr,hk,he,ha⟩ := program_endpoint
    (L := 3) (frame := 128) (σ := caller.st) (base := base₁) (m := m₁)
    producer repr (by decide +kernel) space
    (⟨final.st,exported.ext.trans final.ext⟩ : Solidity.Out C caller.st.H Final) actual_program
  have hi : checked.Input 3 128 base₁ caller.st m₁ := by
    apply (checked.memoryCalls_input (by unfold checked; rfl) 3 128 base₁ caller.st m₁).mpr
    refine ⟨repr,by decide +kernel,?_⟩
    simpa only [checked,Compiler.Compilation.allocationCost] using space
  exact ⟨m₁,base₁,m₂,base₂,hpre,ht,hr,hk.trans stack,he,ha,hi,checked.correct hi⟩

theorem stages : ∃ m₁ base₁ m₂ base₂ m₃ base₃,
    Evm.run prefixCode machine = .ok m₁ 0 ∧ Evm.run callProducer.code m₁ = .ok m₂ 0 ∧
    Evm.run suffixProducer.code m₂ = .ok m₃ 0 ∧
    StateRepr 3 1 128 callProducer.frag exported.st base₂ m₂ ∧
    StateRepr 3 1 128 suffixProducer.frag final.st base₃ m₃ ∧
    m₃.stack = machine.stack ∧ BaseExtends caller.st.H base₁ base₂ ∧ BaseExtends exported.st.H base₂ base₃ := by
  obtain ⟨m₁,base₁,hpre,repr,stack,space⟩ := prefix_endpoint
    (callProducer.cost caller.st + suffixProducer.cost exported.st) (by decide +kernel)
  obtain ⟨m₂,base₂,ht,hr,hk,he,ha⟩ := statement_endpoint
    (L := 3) (frame := 128) (σ := caller.st) (base := base₁) (m := m₁)
    callProducer repr (by decide +kernel) (space.of_le (Nat.le_add_right _ _)) exported actual_call
  obtain ⟨m₃,base₃,ht',hr',hk',he',ha'⟩ := program_endpoint
    (L := 3) (frame := 128) (σ := exported.st) (base := base₂) (m := m₂)
    suffixProducer hr (by decide +kernel) (ha.nextInput space) final actual_suffix
  exact ⟨m₁,base₁,m₂,base₂,m₃,base₃,hpre,ht,ht',hr,hr',hk'.trans (hk.trans stack),he,he'⟩

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
def scalars (σ : State C Final) : List Int := [σ.env.2.2.2.2.2.1.1,σ.env.2.2.2.2.1.1]
def aliases (σ : State C Final) : List (Option Nat) :=
  [identity σ.env.2.1,identity σ.env.2.2.1,identity σ.env.2.2.2.1]
def storageValues {Γ : Ctx} (σ : State C Γ) : Option (List Int) :=
  ([.read (.field (.loc (.root "seed0" rfl)) "value" rfl),
    .read (.field (.loc (.root "seed0" rfl)) "other" rfl),
    .read (.field (.loc (.root "seed1" rfl)) "value" rfl),
    .read (.field (.loc (.root "seed1" rfl)) "other" rfl), .len rows rfl,
    .read (.field (row (.simple (.lit 0 rfl))) "value" rfl),
    .read (.field (row (.simple (.lit 0 rfl))) "other" rfl),
    .read (.field (row (.simple (.lit 1 rfl))) "value" rfl),
    .read (.field (row (.simple (.lit 1 rfl))) "other" rfl),
    .read (.root "unrelated" rfl)] : List (Val C Γ .uint)).mapM
      (fun v => (v.evalT σ).toOption.map (fun n => n.1))
def words (out : Evm.Out) (addresses : List Nat) : Option (List Word) :=
  match out with | .ok m _ => some (m.stack ++ addresses.map m.mem) | _ => none
def slots : List Slot := [.root 0,.root 1,.root 2,.root 3,.root 4,
  .data (.root 4) 0,.data (.root 4) 1,.data (.root 4) 2,.data (.root 4) 3,.root 5]
def stores (out : Evm.Out) : Option (List Nat) :=
  match out with | .ok m _ => some (slots.map m.store) | _ => none

theorem argument_order : (values.1.1,values.2.1.1,identity values.2.2.1) = (1,42,some 0) := by decide +kernel
theorem source_prefix_values : storageValues caller.st = some [11,13,21,23,2,11,13,21,23,9] := by decide +kernel
theorem source_entry : (entry.st.H.length,refObs entry.st.env.1) = (2,none) := by decide +kernel
theorem source_body : (storageValues bodyOutput.st,contents bodyOutput.st,
    [identity bodyOutput.st.env.1,identity bodyOutput.st.env.2.2.2.2.1]) =
    (some [11,13,21,23,2,11,13,73,23,9],some [[2,7,11],[1,23],[2,99,101]],[some 2,some 2]) := by decide +kernel
theorem source_export : (storageValues exported.st,contents exported.st,refObs exported.st.env.1) =
    (some [11,13,21,23,2,11,13,73,23,9],some [[2,7,11],[1,23],[2,99,101]],
      some ("rows",[.idx ⟨1,by decide⟩])) := by decide +kernel
theorem source_tail : (scalars exported.st,aliases exported.st,scalars final.st,aliases final.st) =
    ([42,1],[some 1,some 0,some 0],[84,1],[some 1,some 0,some 0]) := by decide +kernel
theorem source_final : (storageValues final.st,contents final.st,refObs final.st.env.1) =
    (some [11,13,21,23,2,11,13,84,23,9],some [[2,7,84],[1,23],[2,99,101]],
      some ("rows",[.idx ⟨1,by decide⟩])) := by decide +kernel

theorem target_prefix : (words (Evm.run prefixCode machine) [0,127,1,2,3,4,5,256,257,258,259,260],stores (Evm.run prefixCode machine)) =
    (some [w[77],w[261],w[99],w[42],w[1],w[256],w[256],w[259],w[2],w[7],w[11],w[1],w[23]],
      some [11,13,21,23,2,11,13,21,23,9]) := by decide +kernel
theorem target_body : (words (Evm.run (prefixCode ++ expanded.code) machine)
    [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262,263],stores (Evm.run (prefixCode ++ expanded.code) machine)) =
    (some [w[77],w[264],w[99],w[42],w[1],w[256],w[256],w[259],w[261],w[42],w[1],.slot (.data (.root 4) 2),w[261],
      w[2],w[7],w[11],w[1],w[23],w[2],w[99],w[101]],some [11,13,21,23,2,11,13,73,23,9]) := by decide +kernel
theorem target_export : words (Evm.run (prefixCode ++ callProducer.code) machine)
    [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262,263] =
    some [w[77],w[264],w[99],w[42],w[1],w[256],w[256],w[259],.slot (.data (.root 4) 2),w[42],w[1],.slot (.data (.root 4) 2),w[261],
      w[2],w[7],w[11],w[1],w[23],w[2],w[99],w[101]] := by decide +kernel
theorem target_final : (words (Evm.run (prefixCode ++ producer.code) machine)
    [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262,263],stores (Evm.run (prefixCode ++ producer.code) machine)) =
    (some [w[77],w[264],w[99],w[84],w[1],w[256],w[256],w[259],.slot (.data (.root 4) 2),w[42],w[1],.slot (.data (.root 4) 2),w[261],
      w[2],w[7],w[84],w[1],w[23],w[2],w[99],w[101]],some [11,13,21,23,2,11,13,84,23,9]) := by decide +kernel

theorem exact_cost : [Evm.Prog.pushes storagePrefix,prefixProducer.need,expanded.need,callProducer.need,producer.need,
    prefixProducer.cost stored.st,callProducer.cost caller.st,producer.cost caller.st] = [2,5,10,10,10,5,3,3] := by decide +kernel
theorem exact_extensions : [stored.st.H.length,caller.st.H.length,entry.st.H.length,bodyOutput.st.H.length,exported.st.H.length,final.st.H.length] =
    [0,2,2,3,3,3] := by decide +kernel
theorem fragile_classification : [expanded.frag.get .here,callProducer.frag.get .here,producer.frag.get .here] =
    [.fragile,.fragile,.fragile] := by decide +kernel

def staleBody : Prog C Input Input :=
  .cons (.rebind .here (.path (row (.simple (.local (.there .here))))))
    (.cons (.assign (value .here) (.val (.simple (.lit 73 rfl)))) (.cons (.pop rows) .nil))
def staleCall : Stmt C Caller Final := .call "stale" arguments ret staleBody
def staleOut : Solidity.Out C caller.st.H Final := (staleCall.run caller.st).toOption.get (by decide +kernel)
def staleExpanded : Calls.Program 1 prefixProducer.frag (StorageCalls.expand arguments R (.user "out") staleBody) :=
  (FragilePrograms.compile 1 prefixProducer.frag (StorageCalls.expand arguments R (.user "out") staleBody)).get (by decide +kernel)
attribute [irreducible] staleExpanded

theorem stale_source : (refObs staleOut.st.env.1,
    (staleOut.st.env.1.bind (fun r => staleOut.st.storage.findLive r)).isSome) =
    (some ("rows",[.idx ⟨1,by decide⟩]),false) := by decide +kernel
theorem stale_fragment : staleExpanded.frag.get .here = .dead := by decide +kernel
theorem stale_refusal : (FragilePrograms.compile 1 prefixProducer.frag (.cons staleCall .nil)).isSome = false := by decide +kernel
theorem stale_target : stores (Evm.run (prefixCode ++ staleExpanded.code) machine) =
    some [11,13,21,23,1,11,13,73,23,9] := by decide +kernel

def reboundBody : Prog C Input Input :=
  .cons (.rebind .here (.path (row (.simple (.local (.there .here))))))
    (.cons (.pop rows) (.cons (.rebind .here (.path (row (.simple (.lit 0 rfl))))) .nil))
def reboundCall : Stmt C Caller Final := .call "rebound" arguments ret reboundBody
def reboundOut : Solidity.Out C caller.st.H Final := (reboundCall.run caller.st).toOption.get (by decide +kernel)
def reboundProducer : Calls.Program 1 prefixProducer.frag (.cons reboundCall .nil) :=
  (FragilePrograms.compile 1 prefixProducer.frag (.cons reboundCall .nil)).get (by decide +kernel)
attribute [irreducible] reboundProducer

theorem rebound_source : (refObs reboundOut.st.env.1,
    (reboundOut.st.env.1.bind (fun r => reboundOut.st.storage.findLive r)).isSome) =
    (some ("rows",[.idx ⟨0,by decide⟩]),true) := by decide +kernel
theorem rebound_target : (words (Evm.run (prefixCode ++ reboundProducer.code) machine) [0,6],
    stores (Evm.run (prefixCode ++ reboundProducer.code) machine)) =
    (some [w[77],w[261],.slot (.data (.root 4) 0)],some [11,13,21,23,1,11,13,21,23,9]) := by decide +kernel

def oobArgs : Args C Caller Params :=
  .snoc (.snoc (.snocMemory .nil A (.user "a") (.var (.there (.there .here)) rfl))
    .uint (.user "seed") (.simple (.local (.there (.there (.there (.there .here)))))))
    .uint (.user "index") (.simple (.lit 2 rfl))
def oobCall : Stmt C Caller Final := .call "oob" oobArgs ret body
def oobProducer : Calls.Program 1 prefixProducer.frag (.cons oobCall .nil) :=
  (FragilePrograms.compile 1 prefixProducer.frag (.cons oobCall .nil)).get (by decide +kernel)
attribute [irreducible] oobProducer

private theorem error_tag {α : Type} {res : TRes α}
    (h : (match res with | .error .revert => true | _ => false) = true) : res = .error .revert := by
  cases hr : res with
  | error e => cases e <;> simp only [hr,Bool.false_eq_true] at h <;> rfl
  | ok v => simp only [hr,Bool.false_eq_true] at h

theorem oob_source : oobCall.run caller.st = .error .revert := error_tag (by decide +kernel)
theorem oob_cost : (oobProducer.allocates,oobProducer.cost caller.st) = (true,0) := by decide +kernel
theorem oob_target : Evm.run (prefixCode ++ oobProducer.code) machine = .revert := by
  obtain ⟨m₁,base₁,hpre,repr,stack,space⟩ := prefix_endpoint 0 (by decide +kernel)
  have noCost : AllocationInput 1 128 (oobProducer.cost caller.st) caller.st base₁ m₁ := .inl (congrArg Prod.snd oob_cost)
  have source : (Prog.cons oobCall .nil).run caller.st = .error .revert := by
    show TRun.seq oobCall.runR Prog.nil.runR caller.st = _
    have h := oob_source
    simp only [TRun.seq,Stmt.run] at h ⊢
    rw [h]
  rw [run_append_ok hpre]
  exact TuplePrograms.program_revert (L := 3) (frame := 128) (σ := caller.st) (base := base₁) (m := m₁)
    oobProducer repr (by decide +kernel) noCost source

theorem wrong_element : refObs exported.st.env.1 ≠ some ("rows",[.idx ⟨0,by decide⟩]) := by decide +kernel
theorem wrong_root : refObs exported.st.env.1 ≠ some ("seed1",[]) := by decide +kernel
theorem wrong_slot : words (Evm.run (prefixCode ++ callProducer.code) machine) [6] ≠
    some [w[77],.slot (.data (.root 4) 0)] := by decide +kernel
theorem wrong_memory_pointer : words (Evm.run (prefixCode ++ callProducer.code) machine) [6] ≠
    some [w[77],w[261]] := by decide +kernel
theorem lost_old_alias : aliases exported.st ≠ [some 1,some 2,some 2] := by decide +kernel
theorem wrong_cost : prefixProducer.cost stored.st + producer.cost caller.st ≠ 11 := by decide +kernel
theorem old_selector_refusal : (StoragePrograms.compile 1 prefixProducer.frag program).isSome = false := by decide +kernel
theorem public_refusal : (Compiler.compile 1 prefixProducer.frag program).isSome = false := by decide +kernel
theorem owned_acceptance : (FragilePrograms.compile 1 prefixProducer.frag program).isSome = true := by decide +kernel
theorem unset_refusal : (FragilePrograms.compile 1 prefixProducer.frag
    (.cons (.call "unset" arguments ret (.nil : Prog C Input Input)) .nil)).isSome = false := by decide +kernel

def declareSelected : Stmt C Caller Final :=
  .declStorage R (.user "selected") (some (.path (row (.simple (.local (.there (.there (.there .here))))))))
def declarationProducer : Calls.Program 1 prefixProducer.frag (.cons declareSelected .nil) :=
  (FragilePrograms.compile 1 prefixProducer.frag (.cons declareSelected .nil)).get (by decide +kernel)
attribute [irreducible] declarationProducer

theorem declaration_source :
    ((declareSelected.run caller.st).toOption.map (fun out => (refObs out.st.env.1,scalars out.st,aliases out.st))) =
    some (some ("rows",[.idx ⟨1,by decide⟩]),[42,1],[some 1,some 0,some 0]) := by decide +kernel
theorem declaration_target :
    (words (Evm.run (prefixCode ++ declarationProducer.code) machine) [0,6],declarationProducer.frag.get .here,
      declarationProducer.cost caller.st) =
    (some [w[77],w[261],.slot (.data (.root 4) 2)],.fragile,0) := by decide +kernel
theorem wrong_scalar_destination : scalars exported.st ≠ [1,42] := by decide +kernel
theorem wrong_old_content : contents final.st ≠ some [[2,7,11],[1,23],[2,99,101]] := by decide +kernel
theorem wrong_cursor : words (Evm.run (prefixCode ++ producer.code) machine) [0] ≠ some [w[77],w[261]] := by decide +kernel

/-- Actual successful private allocation/mutation followed by a bare failure.
The final allocation is unreachable; no failed State or rollback is recovered. -/
def lateBody : Prog C Input (.mem A :: Input) :=
  .cons (.block body) (.cons .revert
    (.cons (.declMem A (.user "skipped") (some (.newArr (.lit 3 rfl) rfl)) rfl rfl) .nil))
def lateCall : Stmt C Caller Final := .call "lateFailure" arguments ret lateBody
def lateProducer : Calls.Program 1 prefixProducer.frag (.cons lateCall .nil) :=
  (FragilePrograms.compile 1 prefixProducer.frag (.cons lateCall .nil)).get (by decide +kernel)
attribute [irreducible] lateProducer

theorem late_source : lateCall.run caller.st = .error .revert := by
  have hb : lateBody.runR entry.st = .error .revert := error_tag (by decide +kernel)
  exact InternalFlow.call_body_failure arguments ret lateBody.ext lateBody.runR caller.st values actual_arguments .revert hb

theorem late_cost : (lateProducer.allocates,lateProducer.cost caller.st,lateProducer.need) = (true,3,10) := by decide +kernel

theorem late_target : Evm.run (prefixCode ++ lateProducer.code) machine = .revert := by
  obtain ⟨m₁,base₁,hpre,repr,stack,space⟩ := prefix_endpoint (lateProducer.cost caller.st) (by decide +kernel)
  have source : (Prog.cons lateCall .nil).run caller.st = .error .revert := by
    show TRun.seq lateCall.runR Prog.nil.runR caller.st = _
    have h := late_source
    simp only [TRun.seq,Stmt.run] at h ⊢
    rw [h]
  rw [run_append_ok hpre]
  exact TuplePrograms.program_revert (L := 3) (frame := 128) (σ := caller.st) (base := base₁) (m := m₁)
    lateProducer repr (by decide +kernel) space source

theorem late_no_skipped_cost : lateProducer.cost caller.st ≠ 0 ∧ lateProducer.cost caller.st ≠ 7 := by
  have hc : lateProducer.cost caller.st = 3 := congrArg (fun x => x.2.1) late_cost
  rw [hc]
  decide +kernel

#print axioms noRef
#print axioms initial_repr
#print axioms actual_storage
#print axioms storage_prefix_repr
#print axioms actual_prefix
#print axioms actual_arguments
#print axioms actual_body
#print axioms actual_call
#print axioms actual_suffix
#print axioms actual_program
#print axioms original_within_refusal
#print axioms prefix_endpoint
#print axioms whole_endpoint
#print axioms stages
#print axioms argument_order
#print axioms source_prefix_values
#print axioms source_entry
#print axioms source_body
#print axioms source_export
#print axioms source_tail
#print axioms source_final
#print axioms target_prefix
#print axioms target_body
#print axioms target_export
#print axioms target_final
#print axioms exact_cost
#print axioms exact_extensions
#print axioms fragile_classification
#print axioms stale_source
#print axioms stale_fragment
#print axioms stale_refusal
#print axioms stale_target
#print axioms rebound_source
#print axioms rebound_target
#print axioms oob_source
#print axioms oob_cost
#print axioms oob_target
#print axioms wrong_element
#print axioms wrong_root
#print axioms wrong_slot
#print axioms wrong_memory_pointer
#print axioms lost_old_alias
#print axioms wrong_cost
#print axioms old_selector_refusal
#print axioms public_refusal
#print axioms owned_acceptance
#print axioms unset_refusal
#print axioms FragileFrames.pushFragile
#print axioms FragileFrames.setFragile
#print axioms FragileFrames.bindPathFragile
#print axioms FragileFrames.declarePathFragile
#print axioms FragileFrames.statement
#print axioms FragileCalls.storageReturnFragile
#print axioms FragilePop.sameMemory
#print axioms FragilePop.popRoot
#print axioms FragilePop.statement
#print axioms FragilePrograms.compile
#print axioms StoragePrefixFrame.step_mem
#print axioms StoragePrefixFrame.exec_mem
#print axioms StoragePrefixFrame.run_mem
#print axioms StoragePrefixFrame.store_stmt_frame
#print axioms StoragePrefixFrame.store_prog_frame
#print axioms StoragePrefixFrame.allocator_heap
#print axioms declaration_source
#print axioms declaration_target
#print axioms wrong_scalar_destination
#print axioms wrong_old_content
#print axioms wrong_cursor
end Solidity.Backend.InternalFlow.FragileReturnChecks

namespace Solidity.Backend.InternalFlow.FragileReturnChecks.CapturedResult
open Evm Evm.Memory
/-- Actual result export removes the private memory binder, retaining the
callee's exact typed storage reference rather than a memory pointer. -/
theorem returned_reference : exported.st.env.1 = bodyOutput.st.env.2.1 := by rfl

def selectResult : Thin [.alias R] Final :=
  .keep (.drop (.drop (.drop (.drop (.drop .refl)))))
def reached : Solidity.Out C exported.st.H Final := ⟨exported.st,List.prefix_refl _⟩
theorem result_view : TEnv.thin selectResult (TEnv.drop Ext.refl reached.st.env) =
    TEnv.wk reached.ext [.alias R] (TEnv.thin selectResult exported.st.env) := by rfl

theorem returned_slot : ∃ (m₁ : Machine) (base₁ : Nat → Fin W)
    (m₂ : Machine) (base₂ : Nat → Fin W) (m₃ : Machine) (base₃ : Nat → Fin W)
    (r : SRef C (.ref R)) (slot : Slot),
    Evm.run prefixCode machine = .ok m₁ 0 ∧
    Evm.run callProducer.code m₁ = .ok m₂ 0 ∧
    Evm.run suffixProducer.code m₂ = .ok m₃ 0 ∧
    StateRepr 3 1 128 callProducer.frag exported.st base₂ m₂ ∧
    StateRepr 3 1 128 suffixProducer.frag final.st base₃ m₃ ∧
    m₃.stack = machine.stack ∧ BaseExtends caller.st.H base₁ base₂ ∧
    BaseExtends exported.st.H base₂ base₃ ∧
    bodyOutput.st.env.2.1 = some r ∧ exported.st.env.1 = some r ∧
    refObs (some r) = some ("rows",[.idx ⟨1,by decide⟩]) ∧
    m₂.mem 6 = .slot slot ∧ PathSlot C false r slot ∧
    ∃ sv, exported.st.storage.findLive r = some sv := by
  obtain ⟨m₁,base₁,m₂,base₂,m₃,base₃,hp,hc,hs,hr₂,hr₃,stack,he₂,he₃⟩ := stages
  have observed := congrArg (fun p => p.2.2) source_export
  cases old : exported.st.env.1 with
  | none => rw [old] at observed; cases observed
  | some r =>
    have flagSome := congrArg (fun flags => flags[1]?) fragile_classification
    have flag := Option.some.inj flagSome
    change callProducer.frag.get (.here : Idx Final (.alias R)) = .fragile at flag
    have live := CallerView.represented_fragile_drop reached Ext.refl selectResult result_view
      hr₂ (.here : Idx [.alias R] (.alias R)) r old flag
    obtain ⟨slot,word,path,sv,found⟩ := live
    change m₂.mem 6 = .slot slot at word
    rw [old] at observed
    exact ⟨m₁,base₁,m₂,base₂,m₃,base₃,r,slot,hp,hc,hs,hr₂,hr₃,stack,he₂,he₃,
      returned_reference.symm.trans old,rfl,observed,word,path,sv,found⟩

theorem returned_slot_not_memory_pointer : ∃ (m₁ m₂ : Machine) (slot : Slot),
    Evm.run prefixCode machine = .ok m₁ 0 ∧ Evm.run callProducer.code m₁ = .ok m₂ 0 ∧
    m₂.mem 6 = .slot slot ∧ ∀ address : Fin W, m₂.mem 6 ≠ .val address := by
  obtain ⟨m₁,base₁,m₂,base₂,m₃,base₃,r,slot,hp,hc,hs,hr₂,hr₃,stack,he₂,he₃,
    body,old,observed,word,path,live⟩ := returned_slot
  refine ⟨m₁,m₂,slot,hp,hc,word,?_⟩
  intro address wrong
  rw [word] at wrong
  cases wrong

/-- Actual shrinking keeps a syntactic source reference but invalidates it;
the existing selector computes dead and refuses its export. -/
theorem stale_is_not_live : ∃ r : SRef C (.ref R),
    staleOut.st.env.1 = some r ∧ staleOut.st.storage.findLive r = none ∧
    staleExpanded.frag.get .here = .dead ∧
    (FragilePrograms.compile 1 prefixProducer.frag (.cons staleCall .nil)).isSome = false := by
  have observed := congrArg Prod.fst stale_source
  have absent := congrArg Prod.snd stale_source
  cases old : staleOut.st.env.1 with
  | none => rw [old] at observed; cases observed
  | some r =>
    refine ⟨r,rfl,?_,stale_fragment,stale_refusal⟩
    rw [old] at absent
    cases live : staleOut.st.storage.findLive r with
    | none => rfl
    | some value => simp only [Option.bind_some,live,Option.isSome_some] at absent; cases absent
end Solidity.Backend.InternalFlow.FragileReturnChecks.CapturedResult

namespace Solidity.Backend.InternalFlow.FragileReturnChecks.MemoryLocalFrame
open Evm Evm.Memory
private theorem get_return {α : Type} (result : TRes α) (h : result.toOption.isSome = true) :
    result = .ok (result.toOption.get h) := by
  cases result with
  | error e => cases h
  | ok value => rfl

def store : Stmt C Final Final := write (.there (.there (.there .here))) (.lit 0 rfl) (.lit 91 rfl)
def written : Solidity.Out C final.st.H Final := (store.run final.st).toOption.get (by decide +kernel)
theorem source_run : store.run final.st = .ok written := get_return _ (by decide +kernel)
theorem locals_frame : written.st.env = TEnv.wk written.ext Final final.st.env :=
  CallerView.memory_store_environment _ _ source_run

def compiled : CompiledStmt 1 producer.frag store :=
  (Memory.compileStmt 1 producer.frag store).get (by decide +kernel)
attribute [irreducible] compiled
def cert : Calls.Statement 1 producer.frag store := Calls.plainStmt compiled

theorem actual_endpoint : ∃ (m₁ : Machine)
    (m₂ : Machine) (base₂ : Nat → Fin W) (m₃ : Machine) (base₃ : Nat → Fin W),
    Evm.run prefixCode machine = .ok m₁ 0 ∧ Evm.run producer.code m₁ = .ok m₂ 0 ∧
    Evm.run cert.code m₂ = .ok m₃ 0 ∧ StateRepr 3 1 128 producer.frag final.st base₂ m₂ ∧ StateRepr 3 1 128 cert.frag written.st base₃ m₃ ∧
    m₃.stack = machine.stack ∧ BaseExtends final.st.H base₂ base₃ ∧
    GrowsAllocator 1 128 0 final.st base₂ m₂ written.st base₃ m₃ ∧
    (∀ (R : RefTy) (i : Idx Final (.mem R)) (r : HRef final.st.H R),
      TEnv.get i final.st.env = some r → m₃.mem (cellOf 1 i) = .val (base₂ r.id)) ∧
    (∀ (p : PrimTy) (i : Idx Final (.val p)),
      ReprV p (TEnv.get i final.st.env) (m₃.mem (cellOf 1 i))) := by
  obtain ⟨m₁,_base₁,m₂,base₂,hp,hc,repr,stack,extend,grow,input,agrees⟩ := whole_endpoint
  obtain ⟨m₃,base₃,ht,hr,hk,he,hg⟩ := PublishedDirectCalls.statement_endpoint
    (L := 3) (frame := 128) cert repr (by decide +kernel) (.inl rfl) written source_run
  refine ⟨m₁,m₂,base₂,m₃,base₃,hp,hc,ht,repr,hr,hk.trans stack,he,hg,?_,?_⟩
  · exact CallerView.represented written Thin.refl locals_frame hr he
  · intro p i
    exact CallerView.represented_value_drop written Ext.refl Thin.refl locals_frame hr i

theorem changed_contents :
    (contents final.st,contents written.st) =
      (some [[2,7,84],[1,23],[2,99,101]],some [[2,91,84],[1,23],[2,99,101]]) := by
  apply Prod.ext
  · exact congrArg (fun p => p.2.1) source_final
  · decide +kernel

theorem wrong_content_frame : contents written.st ≠ contents final.st := by
  have before := congrArg Prod.fst changed_contents
  have after := congrArg Prod.snd changed_contents
  dsimp only at before after
  rw [after,before]
  decide +kernel

theorem original_guard_rejects : store.withinM .nonpayable = false := by decide +kernel
end Solidity.Backend.InternalFlow.FragileReturnChecks.MemoryLocalFrame


namespace Solidity.Backend.InternalFlow.FragileReturnChecks.MixedSuffix
open Evm Evm.Memory
/-- The actual suffix writes persistent state, a scalar and the older heap;
its returned storage-reference local is preserved operationally. -/
theorem alias_frame : final.st.env.1 = exported.st.env.1 :=
  CallerView.mixed_store_alias _ _ _ _ _ _ (.here : Idx Final (.alias R)) actual_suffix

theorem exact_body_result : final.st.env.1 = bodyOutput.st.env.2.1 :=
  alias_frame.trans CapturedResult.returned_reference

/-- On the SAME actual compiled program, final slot/liveness follows from the
reached representation and preserved actual body result, not a supplied live alias. -/
theorem final_slot : ∃ (m₁ : Machine) (base₁ : Nat → Fin W)
    (m₂ : Machine) (base₂ : Nat → Fin W) (r : SRef C (.ref R)) (slot : Slot),
    Evm.run prefixCode machine = .ok m₁ 0 ∧ Evm.run producer.code m₁ = .ok m₂ 0 ∧
    StateRepr 3 1 128 producer.frag final.st base₂ m₂ ∧ m₂.stack = machine.stack ∧
    BaseExtends caller.st.H base₁ base₂ ∧
    GrowsAllocator 1 128 (producer.cost caller.st) caller.st base₁ m₁ final.st base₂ m₂ ∧
    bodyOutput.st.env.2.1 = some r ∧ exported.st.env.1 = some r ∧ final.st.env.1 = some r ∧
    refObs (some r) = some ("rows",[.idx ⟨1,by decide⟩]) ∧
    m₂.mem 6 = .slot slot ∧ PathSlot C false r slot ∧
    ∃ sv, final.st.storage.findLive r = some sv := by
  obtain ⟨m₁,base₁,m₂,base₂,hp,ht,hr,stack,he,hg,hi,ha⟩ := whole_endpoint
  have observed := congrArg (fun p => p.2.2) source_export
  cases old : exported.st.env.1 with
  | none => rw [old] at observed; cases observed
  | some r =>
    have flag := Option.some.inj (congrArg (fun flags => flags[2]?) fragile_classification)
    change producer.frag.get (.here : Idx Final (.alias R)) = .fragile at flag
    obtain ⟨found,slot,bound,word,path,sv,live⟩ := hr.core.fragile (.here : Idx Final (.alias R)) flag
    change final.st.env.1 = some found at bound
    have same : found = r := Option.some.inj (bound.symm.trans (alias_frame.trans old))
    subst found
    change m₂.mem 6 = .slot slot at word
    rw [old] at observed
    exact ⟨m₁,base₁,m₂,base₂,r,slot,hp,ht,hr,stack,he,hg,
      CapturedResult.returned_reference.symm.trans old,rfl,alias_frame.trans old,
      observed,word,path,sv,live⟩

theorem wrong_element_after_suffix :
    refObs final.st.env.1 ≠ some ("rows",[.idx ⟨0,by decide⟩]) := by
  rw [alias_frame]
  exact wrong_element
end Solidity.Backend.InternalFlow.FragileReturnChecks.MixedSuffix
