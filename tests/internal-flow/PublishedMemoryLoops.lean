import Solidity.Backend.InternalFlow.PublishedLoops
import Solidity.Evm.Compiler
import Solidity.Evm.MemoryLoopScopeBudget
import Solidity.Evm.MemoryLoopSourceExamples
import Solidity.Evm.MemoryLoopScopeSourceExamples
import Solidity.Evm.MemoryLoopScopeDivergenceExamples
import Solidity.Semantics.RunFuel
import Solidity.Syntax.Splice

namespace Solidity.Backend.InternalFlow.PublishedLoopChecks
open Evm Evm.Memory PublishedLoops

def C : Contract := contract!{ uint count; struct Record { uint n; int signed; } }
local instance : InContract := ⟨C⟩
def bases : Nat → Fin W := fun _ => wmod 0
def machine : Machine := {Machine.init with stack := [w[77]], mem := fun a =>
  if a = 0 then w[128] else if a = 63 then w[99] else w[0]}
theorem initial_repr (K : Contract) :
    StateRepr 1 1 64 (Frag.init []) (State.init K) bases machine ∧
    StructAllocatorRepr (State.init K).heap bases 64 (wmod 128) machine := by
  have noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?
  have hh : HeapRepr (State.init K).heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr (State.init K).heap bases 64 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated (State.init K).heap bases := fun _ r => (noRef r).elim
  have hc := Sim.init K 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
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
    change 128 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl

private theorem actual_get {α : Type} (r : TRes α) (h : r.toOption.isSome = true) :
    r = .ok (r.toOption.get h) := by cases r <;> cases h <;> rfl
abbrev A : RefTy := .array (.prim .uint)
abbrev Caller : Ctx := [.mem A,.mem A,.val .uint]
abbrev Iter : Ctx := .val .uint :: Caller
abbrev Final : Ctx := .val .uint :: Caller

def seedProgram : Prog C [] Caller := (sol{
  count = 9; uint marker = 42;
  uint[] memory xs = new uint[](2); xs[0] = 7; xs[1] = 11;
  uint[] memory same = xs;
} : Prog C [] Caller)
def pre : Calls.Program 1 (Frag.init []) seedProgram := (Calls.compile 1 (Frag.init []) seedProgram).get (by decide +kernel)
attribute [irreducible] pre
def mid : Solidity.Out C [] Caller := (seedProgram.run (State.init C)).toOption.get (by decide +kernel)
theorem prefix_run : seedProgram.run (State.init C) = .ok mid := actual_get _ (by decide +kernel)

def condition : Val C Iter .bool := .binop .lt rfl rfl (.simple (.local .here))
  (.mlen (.var (.there (.there .here)) rfl) rfl)
def body : Prog C Iter Iter :=
  .cons (.assignMem (.index .dyn (.var (.there .here) rfl) (.simple (.local .here)))
    (.val (.binop .add rfl rfl (.simple (.local .here)) (.simple (.lit 3 rfl)))))
  (.cons (.assign (.root "count" rfl) (.val (.binop .add rfl rfl (.read (.root "count" rfl)) (.simple (.lit 1 rfl)))))
  (.cons (.assignLocal .here (.binop .add rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl)))) .nil))
def direct : Prog C Iter Iter := .cons (.loop .auto condition body) .nil

def scope (selected : Bool) : Prog C Caller Caller :=
  .cons (.block (.cons (.declLocal .uint (.user "i") (some (.simple (.lit 0 rfl))))
    (.cons (.ite (.simple (.bool selected)) direct (.cons .revert .nil)) .nil))) .nil
def suffix : Prog C Caller Final := .cons (.declLocal .uint (.user "answer")
  (some (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl)))))) .nil

def scopedProgram := (LoopScopes.compileProg 1 (scope true) pre.frag).get (by decide +kernel)
attribute [irreducible] scopedProgram
def publicResult := (Compiler.compile 1 pre.frag (scope true)).get (by decide +kernel)
attribute [irreducible] publicResult
def finished : Solidity.Out C mid.st.H Caller := ((scope true).runF 3 mid.st).toOption.get (by decide +kernel)
def endState : Solidity.Out C finished.st.H Final := (suffix.run finished.st).toOption.get (by decide +kernel)
theorem scope_run : (scope true).run mid.st = .ok finished := by
  have hf : (scope true).runF 3 mid.st = .ok finished := actual_get _ (by decide +kernel)
  have exactRun := (Prog.runF_approx 3 (scope true) mid.st).eq (by rw [hf]; intro h; cases h)
  exact exactRun.symm.trans hf
theorem suffix_run : suffix.run finished.st = .ok endState := actual_get _ (by decide +kernel)

theorem reached : ∃ m₁ base₁ m₂ base₂ cost,
    run pre.code machine = .ok m₁ 0 ∧ run scopedProgram.code m₁ = .ok m₂ 0 ∧
    run (pre.code ++ scopedProgram.code) machine = .ok m₂ 0 ∧
    LoopScopes.Cost scopedProgram.cert mid.st finished cost ∧
    StateRepr 1 1 64 pre.frag mid.st base₁ m₁ ∧ StateRepr 1 1 64 scopedProgram.frag finished.st base₂ m₂ ∧
    BaseExtends mid.st.H base₁ base₂ ∧ GrowsAllocator 1 64 cost mid.st base₁ m₁ finished.st base₂ m₂ ∧
    m₂.stack = machine.stack ∧ BaseExtends (State.init C).H bases base₂ ∧
    GrowsAllocator 1 64 (pre.cost (State.init C) + cost) (State.init C) bases machine finished.st base₂ m₂ := by
  apply after_allocating_prefix pre scopedProgram.cert (initial_repr C).1 (by decide +kernel) (by decide +kernel)
    (budget := 0) (.inr ⟨by decide,wmod 128,(initial_repr C).2,by decide +kernel⟩) mid prefix_run
  · intro amount demand
    exact Nat.le_of_eq (LoopScopes.demand_nonallocating scopedProgram.cert (by decide +kernel) demand)
  · exact scope_run

theorem public_input_and_correct : ∃ m₁ base₁,
    run pre.code machine = .ok m₁ 0 ∧ publicResult.Input 1 64 base₁ mid.st m₁ ∧ publicResult.Agrees 1 64 base₁ mid.st m₁ := by
  obtain ⟨m₁,base₁,m₂,base₂,cost,hp,ht,hall,hcost,hr,rest⟩ := reached
  have hi : publicResult.Input 1 64 base₁ mid.st m₁ := by
    apply (publicResult.memoryLoopScopes_input (by decide +kernel) 1 64 base₁ mid.st m₁).mpr
    exact ⟨hr,by decide +kernel,LoopScopes.room_nonallocating _ (by decide +kernel) _ _ _⟩
  exact ⟨m₁,base₁,hp,hi,publicResult.correct hi⟩

def heapWords {Γ : Ctx} (σ : State C Γ) : Option (List Int) := do
  if h : σ.H[0]? = some A then
    let r : HRef σ.H A := ⟨0,h⟩
    pure ((σ.heap.len r .dyn : Int) :: (MObj.elems .dyn (σ.heap.get r)).map (fun n => n.1))
  else none
def memoryId {H : HTy} (r : Option (HRef H A)) : Option Nat := r.map (·.id)
def caller (σ : State C Caller) : List (Option Nat) := [memoryId σ.env.1,memoryId σ.env.2.1,some σ.env.2.2.1.1.toNat]
def cells (code : List Instr) (addresses : List Nat) : Option (List Word) :=
  match run code machine with | .ok m _ => some (m.stack ++ addresses.map m.mem) | _ => none

theorem prefix_observations : (heapWords mid.st,caller mid.st,mid.st.H.length) =
    (some [2,7,11],[some 0,some 0,some 42],1) := by decide +kernel
theorem final_observations : (heapWords finished.st,caller finished.st,
    endState.st.env.1.1,finished.st.H.length) =
    (some [2,3,4],[some 0,some 0,some 42],4,1) := by decide +kernel

theorem prefix_target : cells pre.code [0,63,1,2,3,128,129,130] =
    some [w[77],w[131],w[99],w[42],w[128],w[128],w[2],w[7],w[11]] := by decide +kernel
/-- Full raw cells are an executable target control; the relational endpoint is proved above. -/
def scope_target : Bool := decide (cells (pre.code ++ scopedProgram.code) [0,63,1,2,3,4,128,129,130] =
    some [w[77],w[131],w[99],w[42],w[128],w[128],w[2],w[2],w[3],w[4]])
/-- info: true -/
#guard_msgs in #eval scope_target

theorem wrong_tail : caller finished.st ≠ [some 0,some 0,some 4] := by decide +kernel
def wrong_cursor : Bool := decide (cells (pre.code ++ scopedProgram.code) [0] ≠ some [w[77],w[134]])
/-- info: true -/
#guard_msgs in #eval wrong_cursor
theorem wrong_alias : caller finished.st ≠ [some 1,some 0,some 42] := by decide +kernel
theorem wrong_branch : (scope false).run mid.st = .error .revert := by
  have hf : (scope false).runF 3 mid.st = .error .revert := rfl
  exact ((Prog.runF_approx 3 (scope false) mid.st).eq (by rw [hf]; intro h; cases h)).symm.trans hf

theorem exact_prefix_and_loop_cost : pre.cost (State.init C) = 3 ∧ scopedProgram.cert.allocates = false := by decide +kernel

private theorem some_ref_of_id {H : HTy} (v : Option (HRef H A)) (r : HRef H A)
    (h : v.map (fun s => s.id) = some r.id) : v = some r := by
  cases v with
  | none => cases h
  | some t =>
    have same : t.id = r.id := Option.some.inj h
    have eq : t = r := by cases t; cases r; cases same; rfl
    exact congrArg some eq

def old : HRef mid.st.H A := ⟨0,by decide +kernel⟩
theorem old_aliases_represented : ∃ (m₁ : Machine) (base₁ : Nat → Fin W) (m₂ : Machine) (base₂ : Nat → Fin W) (cost : Nat),
    run pre.code machine = .ok m₁ 0 ∧ run scopedProgram.code m₁ = .ok m₂ 0 ∧
    m₂.mem (cellOf 1 (.here : Idx Caller (.mem A))) = .val (base₁ old.id) ∧
    m₂.mem (cellOf 1 (.there .here : Idx Caller (.mem A))) = .val (base₁ old.id) ∧
    StateRepr 1 1 64 scopedProgram.frag finished.st base₂ m₂ ∧
    LoopScopes.Cost scopedProgram.cert mid.st finished cost ∧ cost = 0 := by
  obtain ⟨m₁,base₁,m₂,base₂,cost,hp,ht,hall,hc,hr,hr',he,hg,rest⟩ := reached
  have a : TEnv.get (.here : Idx Caller (.mem A)) finished.st.env = some (old.wk finished.ext) :=
    some_ref_of_id _ _ (by decide +kernel)
  have b : TEnv.get (.there .here : Idx Caller (.mem A)) finished.st.env = some (old.wk finished.ext) :=
    some_ref_of_id _ _ (by decide +kernel)
  exact ⟨m₁,base₁,m₂,base₂,cost,hp,ht,old_alias finished hr' he old .here a,
    old_alias finished hr' he old (.there .here) b,hr',hc,LoopScopes.cost_nonallocating hc (by decide +kernel)⟩

def count {Γ : Ctx} (σ : State C Γ) : Option Int :=
  ((Val.read (.root "count" rfl) : Val C Γ .uint).evalT σ).toOption.map (·.1)
theorem root_observations : (count mid.st,count finished.st) = (some 9,some 11) := by decide +kernel
/-- info: true -/
#guard_msgs in #eval decide ((match run (pre.code ++ scopedProgram.code) machine with
  | .ok m _ => some (m.store (.root 0)) | _ => none) = some 11)

def start : Solidity.Out C mid.st.H Iter :=
  ⟨mid.st.push (t := .val .uint) (indexValue ⟨0,W_pos⟩),List.prefix_refl _⟩
def horizonStep : Solidity.Out C mid.st.H Iter → TRes (Solidity.Out C mid.st.H Iter) :=
  InternalFlow.scopedLoopBody body
def horizonCondition (o : Solidity.Out C mid.st.H Iter) : TRes Bool := condition.evalT o.st
structure HorizonObservation where
  done : Bool
  index : Int
  values : Option (List Int)
  persistent : Option Int
  deriving DecidableEq, Repr

def horizons (n : Nat) : Option HorizonObservation :=
  let obs := fun done (o : Solidity.Out C mid.st.H Iter) =>
    some (HorizonObservation.mk done o.st.env.1.1 (heapWords o.st) (count o.st))
  match TLoop.iterN horizonStep horizonCondition n start with
  | .inl o => obs false o
  | .inr (.ok o) => obs true o
  | _ => none
theorem ordered_horizons : [0,1,2,3].map horizons =
    [some ⟨false,0,some [2,7,11],some 9⟩,some ⟨false,1,some [2,3,11],some 10⟩,
     some ⟨false,2,some [2,3,4],some 11⟩,some ⟨true,2,some [2,3,4],some 11⟩] := by decide +kernel

theorem horizon_split : TLoop.iterN horizonStep horizonCondition (1+2) start =
    match TLoop.iterN horizonStep horizonCondition 1 start with
    | .inl mid => TLoop.iterN horizonStep horizonCondition 2 mid
    | .inr r => .inr r := by
  have h := InternalFlow.loop_prefix_add horizonStep horizonCondition 1 2 start
  cases h1 : TLoop.iterN horizonStep horizonCondition 1 start <;> simpa only [h1] using h

def rejected := (LoopScopes.compileProg 1 (scope false) pre.frag).get (by decide +kernel)
attribute [irreducible] rejected
theorem wrong_branch_target : run (pre.code ++ rejected.code) machine = .revert := by
  obtain ⟨m₁,base₁,m₂,base₂,cost,hp,ht,hall,hc,hr,rest⟩ := reached
  rw [run_append_ok hp]
  exact scoped_revert rejected.cert hr (by decide +kernel)
    (LoopScopes.room_nonallocating _ (by decide +kernel) _ _ _) wrong_branch

def spin : Prog C Caller Caller := .cons (.loop .auto (.simple (.bool true)) .nil) .nil
def spinCompiled := (Loops.compileProg 1 pre.frag spin).get (by decide +kernel)
attribute [irreducible] spinCompiled
private theorem cons_halt {K : Contract} {Γ Δ Ξ : Ctx} {σ : State K Γ}
    {head : Stmt K Γ Δ} (tail : Prog K Δ Ξ) {halt : THalt} (h : head.run σ = .error halt) :
    (Prog.cons head tail).run σ = .error halt := by
  show TRun.seq head.runR tail.runR σ = _
  simp only [TRun.seq,Stmt.run] at h ⊢
  rw [h]

theorem source_diverges : spin.run mid.st = .error .diverge := by
  let go : Solidity.Out C mid.st.H Caller → TRes (Solidity.Out C mid.st.H Caller) :=
    InternalFlow.scopedLoopBody (Prog.nil : Prog C Caller Caller)
  let cond := fun _ : Solidity.Out C mid.st.H Caller => (.ok true : TRes Bool)
  let entry : Solidity.Out C mid.st.H Caller := ⟨mid.st,List.prefix_refl _⟩
  have step : TLoop.step go cond entry = .inl entry := rfl
  have iter : ∀ n, TLoop.iterN go cond n entry = .inl entry := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [TLoop.iterN,step]; exact ih
  have hl : (Stmt.loop .auto (.simple (.bool true)) (Prog.nil : Prog C Caller Caller)).run mid.st = .error .diverge := by
    rw [Stmt.run_loop]
    exact InternalFlow.loop_all_prefixes_running go cond entry (fun n => ⟨entry,iter n⟩)
  exact cons_halt .nil hl

theorem target_fault : run (pre.code ++ spinCompiled.code) machine = .fault := by
  obtain ⟨m₁,base₁,m₂,base₂,cost,hp,ht,hall,hc,hr,rest⟩ := reached
  rw [run_append_ok hp]
  exact direct_diverge spinCompiled.cert hr (by decide +kernel)
    (Loops.room_nonallocating _ (by decide +kernel) _ _ _) source_diverges

theorem nested_body_refused : (Loops.compileProg 1 (Frag.init Iter)
    (.cons (.loop .auto condition (.cons (.loop .auto condition body) .nil)) .nil)).isSome = false := by decide +kernel
theorem old_frame_guard : Prog.withinM .view body = false := rfl

def post := (Calls.compile 1 scopedProgram.frag suffix).get (by decide +kernel)
attribute [irreducible] post

theorem whole_endpoint : ∃ (m : Machine) (base : Nat → Fin W),
    run ((pre.code ++ scopedProgram.code) ++ post.code) machine = .ok m 0 ∧
    StateRepr 1 1 64 post.frag endState.st base m ∧ m.stack = machine.stack ∧ m.mem 4 = w[4] ∧
    BaseExtends (State.init C).H bases base ∧
    GrowsAllocator 1 64 3 (State.init C) bases machine endState.st base m ∧ m.mem 0 = w[131] := by
  obtain ⟨m₁,base₁,m₂,base₂,cost,hp,ht,hall,hc,hr,hr',he,hg,rest⟩ := reached
  obtain ⟨m₃,base₃,ht',hr'',hk,he',hg'⟩ := PublishedDirectCalls.program_endpoint post hr' (by decide +kernel)
    (.inl (by decide +kernel)) endState suffix_run
  have hv := hr''.core.vals (.here : Idx Final (.val .uint))
  obtain ⟨n,hn,hvalue⟩ := hv
  have value : endState.st.env.1.1 = 4 := by decide +kernel
  change endState.st.env.1.1 = (n.val : Int) at hvalue
  have hn4 : n.val = 4 := by rw [value] at hvalue; omega
  have n4 : n = wmod 4 := Fin.ext (by simpa only [show (wmod 4).val = 4 from by decide +kernel] using hn4)
  have cell : m₃.mem 4 = w[4] := by
    change m₃.mem 4 = .val (wmod 4)
    simpa only [Machine.memAt,lvl_here,show Final.length = 4 from rfl] using hn.trans (congrArg Word.val n4)
  have cz : cost = 0 := LoopScopes.cost_nonallocating hc (by decide +kernel)
  have pz : post.cost finished.st = 0 := by decide +kernel
  have total : GrowsAllocator 1 64 3 (State.init C) bases machine endState.st base₃ m₃ := by
    simpa only [exact_prefix_and_loop_cost.1,cz,pz,Nat.add_zero] using rest.2.2.comp hg'
  have space : (wmod 128).val + 3 < W := by decide +kernel
  have alloc := total (wmod 128) (by decide) (initial_repr C).2 space
  have pointer : m₃.mem 0 = w[131] := by
    have eq : (⟨(wmod 128).val+3,space⟩ : Fin W) = wmod 131 := by
      apply Fin.ext
      change (wmod 128).val + 3 = (wmod 131).val
      decide +kernel
    exact alloc.arrays.free.cell.trans (congrArg Word.val eq)
  refine ⟨m₃,base₃,?_,hr'',hk.trans rest.1,cell,BaseExtends.trans (mid.ext.trans finished.ext) rest.2.1 he',total,pointer⟩
  rw [run_append_ok hall]
  exact ht'

def prepare : Prog C Caller Iter := .cons (.declLocal .uint (.user "i") (some (.simple (.lit 0 rfl)))) .nil
def prepareCompiled := (Calls.compile 1 pre.frag prepare).get (by decide +kernel)
attribute [irreducible] prepareCompiled
def directCompiled := (Loops.compileProg 1 prepareCompiled.frag direct).get (by decide +kernel)
attribute [irreducible] directCompiled
def directOut : Solidity.Out C start.st.H Iter := (direct.runF 3 start.st).toOption.get (by decide +kernel)
theorem direct_source : direct.run start.st = .ok directOut := by
  have hf : direct.runF 3 start.st = .ok directOut := actual_get _ (by decide +kernel)
  exact ((Prog.runF_approx 3 direct start.st).eq (by rw [hf]; intro h; cases h)).symm.trans hf

theorem direct_reached : ∃ (m : Machine) (base : Nat → Fin W) (cost : Nat),
    run ((pre.code ++ prepareCompiled.code) ++ directCompiled.code) machine = .ok m 0 ∧
    Loops.Cost directCompiled.cert start.st directOut cost ∧
    StateRepr 1 1 64 directCompiled.frag directOut.st base m ∧ m.stack = machine.stack := by
  obtain ⟨m₁,base₁,m₂,base₂,amount,hp,ht,hall,hc,hr,rest⟩ := reached
  have prepared : prepare.run mid.st = .ok start := rfl
  obtain ⟨m₃,base₃,ht',hr',hk,he,hg⟩ := PublishedDirectCalls.program_endpoint prepareCompiled hr (by decide +kernel)
    (.inl (by decide +kernel)) start prepared
  obtain ⟨m₄,base₄,cost,ht'',hc',hr'',hk',he',hg'⟩ := direct_endpoint directCompiled.cert hr' (by decide +kernel)
    (Loops.room_nonallocating _ (by decide +kernel) _ _ _) directOut direct_source
  have prefixStack : m₁.stack = machine.stack := by
    have h : (match run pre.code machine with | .ok m _ => m.stack | _ => []) = machine.stack := by decide +kernel
    rw [hp] at h
    exact h
  refine ⟨m₄,base₄,cost,?_,hc',hr'',hk'.trans (hk.trans prefixStack)⟩
  rw [run_append_ok (show run (pre.code ++ prepareCompiled.code) machine = .ok m₃ 0 by rw [run_append_ok hp]; exact ht')]
  exact ht''

/-- Infer the actual published private witnesses from their publicResult proof. -/
def top {K : Contract} {Δ : Ctx} (i : Idx Δ (.val .uint))
    (r : TRes (Solidity.Out K (State.init K).H Δ)) : Option Int :=
  r.toOption.map fun o => (TEnv.get i o.st.env).1

def publicSource {K : Contract} {Δ : Ctx} {P : Prog K [] Δ}
    {compiled : Compiler.Compilation 1 (Frag.init []) P} {base : Nat → Fin W} {m : Machine}
    (_ : compiled.Agrees 1 64 base (State.init K) m) (i : Idx Δ (.val .uint))
    (finite : Bool) : Option Int :=
  top i (if finite then P.runF 4 (State.init K) else P.run (State.init K))
def publicTarget {K : Contract} {Δ : Ctx} {P : Prog K [] Δ}
    {compiled : Compiler.Compilation 1 (Frag.init []) P} {base : Nat → Fin W} {m : Machine}
    (_ : compiled.Agrees 1 64 base (State.init K) m) (addresses : List Nat) : Option (List Nat) :=
  match run compiled.code m with
  | .ok m _ => addresses.mapM fun a => match m.mem a with | .val n => some n.val | _ => none
  | _ => none

theorem publicSource_lift {K : Contract} {Δ : Ctx} {P : Prog K [] Δ}
    {compiled : Compiler.Compilation 1 (Frag.init []) P} {base : Nat → Fin W} {m : Machine}
    (proof : compiled.Agrees 1 64 base (State.init K) m) (i : Idx Δ (.val .uint)) (v : Int)
    (finite : publicSource proof i true = some v) : publicSource proof i false = some v := by
  have nondiv : P.runF 4 (State.init K) ≠ .error .diverge := by
    intro h; change top i (P.runF 4 (State.init K)) = some v at finite
    rw [h] at finite; cases finite
  have exactRun := (Prog.runF_approx 4 P (State.init K)).eq nondiv
  change top i (P.runR (State.init K)) = _
  rw [← exactRun]
  exact finite

theorem published_direct_arrays : publicSource Evm.Memory.LoopSourceExamples.arrays_simulate .here false = some 4 := by
  apply publicSource_lift
  decide +kernel
/-- info: true -/
#guard_msgs in #eval decide (publicTarget Evm.Memory.LoopSourceExamples.arrays_simulate [0,1,2,3,4,128,129,130,63] = some [131,128,128,2,4,2,3,4,99])

theorem published_direct_arraysIR : publicSource Evm.Memory.LoopSourceExamples.arraysIR_simulate .here false = some 4 := by
  apply publicSource_lift
  decide +kernel
/-- info: true -/
#guard_msgs in #eval decide (publicTarget Evm.Memory.LoopSourceExamples.arraysIR_simulate [0,1,2,3,4,128,129,130,63] = some [131,128,128,2,4,2,3,4,99])

theorem published_direct_records : publicSource Evm.Memory.LoopSourceExamples.records_simulate .here false = some 3 := by
  apply publicSource_lift
  decide +kernel
/-- info: true -/
#guard_msgs in #eval decide (publicTarget Evm.Memory.LoopSourceExamples.records_simulate [0,1,2,3,128,63] = some [130,128,128,128,3,99])

theorem published_direct_recordsIR : publicSource Evm.Memory.LoopSourceExamples.recordsIR_simulate .here false = some 3 := by
  apply publicSource_lift
  decide +kernel
/-- info: true -/
#guard_msgs in #eval decide (publicTarget Evm.Memory.LoopSourceExamples.recordsIR_simulate [0,1,2,3,128,63] = some [130,0,5,128,3,99])

theorem published_scoped_arrays : publicSource Evm.Memory.LoopScopeSourceExamples.arrays_simulate .here false = some 4 := by
  apply publicSource_lift
  decide +kernel
/-- info: true -/
#guard_msgs in #eval decide (publicTarget Evm.Memory.LoopScopeSourceExamples.arrays_simulate [0,1,2,3,4,128,129,130,63] = some [131,128,128,2,4,2,3,4,99])

theorem published_scoped_arraysIR : publicSource Evm.Memory.LoopScopeSourceExamples.arraysIR_simulate .here false = some 4 := by
  apply publicSource_lift
  decide +kernel
/-- info: true -/
#guard_msgs in #eval decide (publicTarget Evm.Memory.LoopScopeSourceExamples.arraysIR_simulate [0,1,2,3,4,128,129,130,63] = some [131,128,128,2,4,2,3,4,99])

theorem published_scoped_records : publicSource Evm.Memory.LoopScopeSourceExamples.records_simulate .here false = some 3 := by
  apply publicSource_lift
  decide +kernel
/-- info: true -/
#guard_msgs in #eval decide (publicTarget Evm.Memory.LoopScopeSourceExamples.records_simulate [0,1,2,3,128,63] = some [130,128,128,128,3,99])

theorem published_scoped_recordsIR : publicSource Evm.Memory.LoopScopeSourceExamples.recordsIR_simulate .here false = some 3 := by
  apply publicSource_lift
  decide +kernel
/-- info: true -/
#guard_msgs in #eval decide (publicTarget Evm.Memory.LoopScopeSourceExamples.recordsIR_simulate [0,1,2,3,128,63] = some [130,0,5,128,3,99])

/-- Ordinary memory-result call followed by the same actual scoped loop.
Its default result allocation stays private; the returned second object escapes. -/
def makeBody : Prog C [.mem A] [.mem A] :=
  .cons (.rebindMem .here (.newArr (.lit 2 rfl) rfl))
  (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl))) (.val (.simple (.lit 7 rfl))))
  (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl))) (.val (.simple (.lit 11 rfl)))) .nil))
def callSeed : Prog C [] Caller :=
  .cons (.assign (.root "count" rfl) (.val (.simple (.lit 9 rfl))))
  (.cons (.declLocal .uint (.user "marker") (some (.simple (.lit 42 rfl))))
  (.cons (.call "make" (.nil : Args C [.val .uint] []) (.mem A (.user "xs") rfl rfl) makeBody)
  (.cons (.declMem A (.user "same") (some (.alias (.var .here rfl))) rfl rfl) .nil)))
def callBefore := (Calls.compile 1 (Frag.init []) callSeed).get (by decide +kernel)
attribute [irreducible] callBefore
@[irreducible] def callMid : Solidity.Out C [] Caller := (callSeed.run (State.init C)).toOption.get (by decide +kernel)
def callScope := (LoopScopes.compileProg 1 (scope true) callBefore.frag).get (by decide +kernel)
attribute [irreducible] callScope
@[irreducible] def callEnd : Solidity.Out C callMid.st.H Caller := ((scope true).runF 3 callMid.st).toOption.get (by decide +kernel)
def returned : HRef callMid.st.H A := ⟨1,by decide +kernel⟩
theorem call_prefix_actual : callSeed.run (State.init C) = .ok callMid := by
  unfold callMid
  exact actual_get _ (by decide +kernel)
theorem call_scope_actual : (scope true).run callMid.st = .ok callEnd := by
  have hf : (scope true).runF 3 callMid.st = .ok callEnd := by
    unfold callEnd
    exact actual_get _ (by decide +kernel)
  exact ((Prog.runF_approx 3 (scope true) callMid.st).eq (by rw [hf]; intro h; cases h)).symm.trans hf

/-- Complete source heap observations; no metadata/simulation premise is assumed. -/
def callArray {Γ : Ctx} (σ : State C Γ) (id : Nat) : Option (List Int) :=
  if h : σ.H[id]? = some A then
    let r : HRef σ.H A := ⟨id,h⟩
    some ((σ.heap.len r .dyn : Int) :: (MObj.elems .dyn (σ.heap.get r)).map (fun n => n.1))
  else none
structure CallLoopObservation where
  enteredHeap : Nat
  finalHeap : Nat
  enteredLocals : List (Option Nat)
  finalLocals : List (Option Nat)
  defaultBefore : Option (List Int)
  returnedBefore : Option (List Int)
  defaultAfter : Option (List Int)
  returnedAfter : Option (List Int)
  persistent : Option Int
  deriving DecidableEq, Repr

theorem call_loop_controls :
    CallLoopObservation.mk callMid.st.H.length callEnd.st.H.length (caller callMid.st) (caller callEnd.st)
      (callArray callMid.st 0) (callArray callMid.st 1) (callArray callEnd.st 0) (callArray callEnd.st 1) (count callEnd.st) =
      ⟨2,2,[some 1,some 1,some 42],[some 1,some 1,some 42],some [0],some [2,7,11],some [0],some [2,3,4],some 11⟩ ∧
    caller callEnd.st ≠ [some 0,some 0,some 42] ∧ count callEnd.st ≠ some 9 := by
  refine ⟨?_,?_,?_⟩ <;> decide +kernel
/-- info: true -/
#guard_msgs in #eval decide (cells (callBefore.code ++ callScope.code) [0,63,1,2,3,4,128,129,130,131] =
  some [w[77],w[132],w[99],w[42],w[129],w[129],w[2],w[0],w[2],w[3],w[4]])
/-- info: true -/
#guard_msgs in #eval decide (callBefore.cost (State.init C) = 4 ∧ callBefore.cost (State.init C) ≠ 3)

#print axioms initial_repr
#print axioms prefix_run
#print axioms scope_run
#print axioms suffix_run
#print axioms reached
#print axioms public_input_and_correct
#print axioms prefix_observations
#print axioms final_observations
#print axioms prefix_target
#print axioms wrong_tail
#print axioms wrong_alias
#print axioms wrong_branch
#print axioms exact_prefix_and_loop_cost
#print axioms old_aliases_represented
#print axioms root_observations
#print axioms ordered_horizons
#print axioms horizon_split
#print axioms wrong_branch_target
#print axioms source_diverges
#print axioms target_fault
#print axioms nested_body_refused
#print axioms old_frame_guard
#print axioms whole_endpoint
#print axioms direct_source
#print axioms direct_reached
#print axioms publicSource_lift
#print axioms published_direct_arrays
#print axioms published_direct_arraysIR
#print axioms published_direct_records
#print axioms published_direct_recordsIR
#print axioms published_scoped_arrays
#print axioms published_scoped_arraysIR
#print axioms published_scoped_records
#print axioms published_scoped_recordsIR
#print axioms PublishedLoops.direct_endpoint
#print axioms PublishedLoops.direct_revert
#print axioms PublishedLoops.direct_diverge
#print axioms PublishedLoops.scoped_endpoint
#print axioms PublishedLoops.scoped_revert
#print axioms PublishedLoops.scoped_diverge
#print axioms PublishedLoops.block_endpoint
#print axioms PublishedLoops.after_allocating_prefix
#print axioms PublishedLoops.old_alias
end Solidity.Backend.InternalFlow.PublishedLoopChecks
