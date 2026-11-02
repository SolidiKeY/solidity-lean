import Solidity.Backend.Passes.MemoryCallBoundary
import Solidity.Backend.Passes.TripleSequence

/-! An actual intrinsic memory-return call between separately compiled passes.
The caller's existing alias precedes the call; the fresh escaped object and
private parameter rebinding are distinguished. No independent Source lowering
or external CALL/world semantics is manufactured. -/
namespace Solidity.Backend.Passes.MemoryCallControls
open Evm Evm.Memory Evm.Compiler

def C : Contract := {vars := []}
abbrev A : RefTy := .array (.prim .uint)
abbrev Before : Ctx := [.val .uint,.mem A]
abbrev Captured : Ctx := .mem A :: Before
abbrev After : Ctx := .mem A :: Captured

def allocate : Prog C [] Before :=
  .cons (.declMem A (.user "old") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
  (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl))) (.val (.simple (.lit 7 rfl))))
  (.cons (.declLocal .uint (.user "marker") (some (.simple (.lit 42 rfl)))) .nil))

/-- Existing call frame: return variable, memory parameter, then a fresh body local. -/
def body : Prog C [.mem A,.mem A] [.mem A,.mem A,.mem A] :=
  .cons (.declMem A (.user "owned") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl)
  (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl))) (.val (.simple (.lit 33 rfl))))
  (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl))) (.val (.simple (.lit 34 rfl))))
  (.cons (.rebindMem (.there .here) (.alias (.var .here rfl)))
  (.cons (.rebindMem (.there (.there .here)) (.newArr (.lit 1 rfl) rfl))
  (.cons (.assignMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.lit 44 rfl)))) .nil)))))

def arguments : Args C Captured [.mem A] := .snocMemory .nil A (.user "a") (.var .here rfl)
def call : Prog C Before After :=
  .cons (.declMem A (.user "argumentCapture") (some (.alias (.var (.there .here) rfl))) rfl rfl)
  (.cons (.call "escape" arguments (.mem A (.user "result") rfl rfl) body) .nil)

def consume : Prog C After After :=
  .cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
    (.val (.binop .add rfl rfl (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl))))
      (.simple (.lit 9 rfl)))))
  (.cons (.assignMem (.index .dyn (.var (.there (.there (.there .here))) rfl) (.simple (.lit 0 rfl)))
    (.val (.binop .add rfl rfl
      (.readMem (.index .dyn (.var (.there (.there (.there .here))) rfl) (.simple (.lit 0 rfl))))
      (.simple (.lit 1 rfl))))) .nil)

def allocation : CompiledProg 1 (Frag.init []) allocate := (compileProg 1 _ allocate).get (by decide +kernel)
def producer : Calls.Program 1 allocation.frag call := (Calls.compile 1 _ call).get (by decide +kernel)
theorem push_free : Evm.Prog.pushes call = 0 := by decide +kernel
def checked : Compilation 1 allocation.frag call := .memoryCalls producer push_free
def consumer : CompiledProg 1 producer.frag consume := (compileProg 1 _ consume).get (by decide +kernel)

theorem public_recognizer : (Compiler.compile 1 allocation.frag call).map (·.isMemoryCalls) = some true := by
  decide +kernel

theorem actual_public : Compiler.compile 1 allocation.frag call = some checked := by
  have hm : Memory.compileProg 1 allocation.frag call = none :=
    Option.isNone_iff_eq_none.mp (by decide +kernel)
  have hr : Memory.ReferenceArrays.compileProg 1 allocation.frag call = none :=
    Option.isNone_iff_eq_none.mp (by decide +kernel)
  have ho : Memory.Objects.compileProg 1 allocation.frag call = none :=
    Option.isNone_iff_eq_none.mp (by decide +kernel)
  have hn : Memory.Construction.compileProg 1 allocation.frag call = none :=
    Option.isNone_iff_eq_none.mp (by decide +kernel)
  have hl : Memory.Loops.compileProg 1 allocation.frag call = none :=
    Option.isNone_iff_eq_none.mp (by decide +kernel)
  have hs : Memory.LoopScopes.compileProg 1 call allocation.frag = none :=
    Option.isNone_iff_eq_none.mp (by decide +kernel)
  have hp : some producer = Calls.compile 1 allocation.frag call := Option.some_get (by decide +kernel)
  simp only [Compiler.compile,hm,hr,ho,hn,hl,hs,dif_pos push_free,← hp,Option.map_some]
  rfl

def initial : State C [] := State.init C
def base : Nat → Fin W := fun _ => wmod 0
def machine : Machine :=
  {Machine.init with mem := fun n => if n = 0 then w[256] else if n = 127 then w[99] else w[0]}
private theorem noRefs {R : RefTy} (r : HRef initial.H R) : False := by cases r.get?

theorem initial_repr : StateRepr 1 1 128 (Frag.init []) initial base machine ∧
    StructAllocatorRepr initial.heap base 128 (wmod 256) machine := by
  have hh : HeapRepr initial.heap base 128 machine :=
    ⟨fun r => (noRefs r).elim,fun r => (noRefs r).elim,fun r => (noRefs r).elim⟩
  have hs : StructHeapRepr initial.heap base 128 machine :=
    ⟨fun r => (noRefs r).elim,fun r => (noRefs r).elim,fun r => (noRefs r).elim⟩
  have hx : StructArraySeparated initial.heap base := fun _ r => (noRefs r).elim
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨⟨?_,hh,?_,by decide,hs,hx,?_⟩,⟨⟨hh,?_,fun r => (noRefs r).elim⟩,hs,hx,fun r => (noRefs r).elim⟩⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    all_goals intro p i; nomatch i
  · intro R i; nomatch i
  · intro s f R r hf; exact (noRefs r).elim
  · refine ⟨by decide,by decide,rfl,?_⟩
    intro addr ha
    change 256 ≤ addr at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl

private theorem first_some : (allocate.run initial).toOption.isSome = true := by decide +kernel
noncomputable def first : Solidity.Out C initial.H Before := (allocate.run initial).toOption.get first_some
private theorem second_some : (call.run first.st).toOption.isSome = true := by decide +kernel
noncomputable def second : Solidity.Out C first.st.H After := (call.run first.st).toOption.get second_some
private theorem final_some : (consume.run second.st).toOption.isSome = true := by decide +kernel
noncomputable def final : Solidity.Out C second.st.H After := (consume.run second.st).toOption.get final_some

private theorem source_get {Γ Δ : Ctx} {σ : State C Γ} {P : Prog C Γ Δ}
    {o : Solidity.Out C σ.H Δ} (hx : some o = (P.run σ).toOption) : P.run σ = .ok o := by
  cases hs : P.run σ with
  | ok value => rw [hs] at hx; exact congrArg Except.ok (Option.some.inj hx).symm
  | error e => rw [hs] at hx; cases hx

theorem first_source : allocate.run initial = .ok first := source_get (Option.some_get first_some)
theorem second_source : call.run first.st = .ok second := source_get (Option.some_get second_some)
theorem final_source : consume.run second.st = .ok final := source_get (Option.some_get final_some)

theorem costs : allocation.cert.cost initial = 2 ∧ producer.cost first.st = 6 ∧
    Memory.allocationCostProg call first.st = 0 ∧ Memory.hasAllocation consume = false := by decide +kernel

theorem frame_difference : Memory.frameNeedProg call < producer.need ∧ 1 + producer.need ≤ 128 := by decide +kernel

theorem input : (Compilation.memory allocation).Input 1 128 base initial machine :=
  ⟨initial_repr.1,by decide +kernel,.inr ⟨by decide,wmod 256,initial_repr.2,by decide +kernel⟩⟩

end Solidity.Backend.Passes.MemoryCallControls
