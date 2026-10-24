import Solidity.Evm.MemoryCompile
import Solidity.Evm.Correct
import Solidity.Evm.Compiler

/-! Concrete source programs through the memory compiler, with two aliases,
an independent object and an actual populated state-representation witness. -/
namespace Solidity.Evm.Memory.CompileExamples

def C : Contract := contract!{ }
def H : HTy := [.array (.prim .uint), .array (.prim .uint)]
def r0 : HRef H (.array (.prim .uint)) := ⟨0, rfl⟩
def r1 : HRef H (.array (.prim .uint)) := ⟨1, rfl⟩
def base (id : Nat) : Fin W := if id = 0 then ⟨16, by decide⟩ else ⟨20, by decide⟩
def uint (n : Nat) (h : n < W) : PrimTy.uint.Denote := indexValue ⟨n, h⟩
def hp : Heap H :=
  (⟨[uint 7 (by decide), uint 9 (by decide)], by decide⟩,
    ⟨[uint 4 (by decide)], by decide⟩, ())
def Γ : Ctx := [.val .uint, .mem (.array (.prim .uint)),
  .mem (.array (.prim .uint)), .mem (.array (.prim .uint))]
def σ : State C Γ :=
  { storage := Storage.init C, H := H, heap := hp,
    env := (uint 0 W_pos, some r0, some r0, some r1, ()) }
def machine : Machine :=
  { Machine.init with mem := fun a =>
    if a = 0 then w[20] else if a = 1 then w[16] else if a = 2 then w[16]
    else if a = 16 then w[2] else if a = 17 then w[7] else if a = 18 then w[9]
    else if a = 20 then w[1] else if a = 21 then w[4] else w[0] }

theorem array0_repr : ArrayRepr hp r0 (base 0) machine := by
  constructor
  · change 16 + 1 + hp.len r0 .dyn ≤ W
    simp only [Heap.len, hp, r0, H, Heap.get, Objs.get, MObj.elems_dyn,
      List.length_cons, List.length_nil]
    decide +kernel
  · change machine.mem 16 = .val (wmod (hp.len r0 .dyn))
    simp only [Heap.len, hp, r0, H, Heap.get, Objs.get, MObj.elems_dyn,
      List.length_cons, List.length_nil]
    rfl
  · intro i v hv
    simp only [hp, r0, H, Heap.get, Objs.get, MObj.elems_dyn] at hv
    cases i with
    | zero => cases hv; exact ⟨⟨7, by decide⟩, rfl, rfl⟩
    | succ i =>
      cases i with
      | zero => cases hv; exact ⟨⟨9, by decide⟩, rfl, rfl⟩
      | succ i => cases hv

theorem array1_repr : ArrayRepr hp r1 (base 1) machine := by
  constructor
  · change 20 + 1 + hp.len r1 .dyn ≤ W
    simp only [Heap.len, hp, r1, H, Heap.get, Objs.get, MObj.elems_dyn,
      List.length_cons, List.length_nil]
    decide +kernel
  · simp only [Heap.len, hp, r1, H, Heap.get, Objs.get, MObj.elems_dyn,
      List.length_cons, List.length_nil]
    rfl
  · intro i v hv
    simp only [hp, r1, H, Heap.get, Objs.get, MObj.elems_dyn] at hv
    cases i with
    | zero => cases hv; exact ⟨⟨4, by decide⟩, rfl, rfl⟩
    | succ i => cases hv

private theorem ref_cases {p : PrimTy} (r : HRef H (.array (.prim p))) :
    p = .uint ∧ (HEq r r0 ∨ HEq r r1) := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi; exact ⟨rfl, .inl HEq.rfl⟩
  | succ i =>
    cases i with
    | zero => cases hi; exact ⟨rfl, .inr HEq.rfl⟩
    | succ i => cases hi

theorem heap_repr : HeapRepr hp base 4 machine := by
  constructor
  · intro p r
    rcases ref_cases r with ⟨rfl, hr | hr⟩ <;> cases hr
    · exact array0_repr
    · exact array1_repr
  · intro p r
    rcases ref_cases r with ⟨rfl, hr | hr⟩ <;> cases hr <;> decide +kernel
  · intro p q r s hne
    rcases ref_cases r with ⟨rfl, hr | hr⟩ <;> cases hr <;>
      rcases ref_cases s with ⟨rfl, hs | hs⟩ <;> cases hs
    · exact False.elim (hne rfl)
    · exact .inl (by decide +kernel)
    · exact .inr (by decide +kernel)
    · exact False.elim (hne rfl)

private theorem noStructs {s : Name} (r : HRef H (.struct s)) : False := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases hi

theorem fixture_repr : StateRepr 1 0 4 (Frag.init Γ) σ base machine := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  constructor
  · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    · intro p i
      cases i with
      | here => exact ⟨⟨0, W_pos⟩, rfl, rfl⟩
      | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · exact heap_repr
  · intro p i
    cases i with
    | there i =>
      cases i with
      | here => exact ⟨r0, rfl, rfl⟩
      | there i =>
        cases i with
        | here => exact ⟨r0, rfl, rfl⟩
        | there i =>
          cases i with
          | here => exact ⟨r1, rfl, rfl⟩
          | there i => nomatch i
  · exact Nat.le_refl _
  · exact ⟨fun r => (noStructs r).elim, fun r => (noStructs r).elim, fun r => (noStructs r).elim⟩
  · exact fun _ r => (noStructs r).elim
  · exact RefFieldsRepr.withoutStructs _ _ _ (fun r => noStructs r)

private def zero : Val C Γ .uint := .simple (.lit 0 rfl)
private def five : Val C Γ .uint := .simple (.lit 5 rfl)
private def first : Idx Γ (.mem (.array (.prim .uint))) := .there (.there .here)
private def second : Idx Γ (.mem (.array (.prim .uint))) := .there .here

/-- Write through one alias and read through the other into a value local. -/
def writeAndRead : Prog C Γ Γ :=
  .cons (.assignMem (.index .dyn (.var first rfl) zero) (.val five))
    (.cons (.assignLocal .here (.readMem (.index .dyn (.var second rfl) zero))) .nil)

def compiled : CompiledProg 0 (Frag.init Γ) writeAndRead :=
  (compileProg 0 (Frag.init Γ) writeAndRead).get (by decide +kernel)

/-- The actual compiler result is accepted by the source simulation theorem. -/
theorem compiled_simulates : GrowingResult 1 0 4 (compiled.cert.cost σ) compiled.frag σ base machine
    (writeAndRead.run σ) (run compiled.code machine) :=
  compile_correct rfl fixture_repr (by decide +kernel) (.inl (by decide +kernel))

private def sourceValue (out : TRes (Solidity.Out C H Γ)) : Option Int :=
  match out with
  | .ok o => some (TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).1
  | .error _ => none

private def sourceReverted {α : Type} : TRes α → Bool
  | .error .revert => true
  | _ => false

private theorem sourceReverted_sound {α : Type} {out : TRes α}
    (h : sourceReverted out = true) : out = .error .revert := by
  cases out with
  | ok o => cases h
  | error e => cases e <;> cases h <;> rfl

private def targetCell (a : Nat) (out : Out) : Option Nat :=
  match out with
  | .ok m _ => match m.mem a with | .val x => some x.1 | _ => none
  | _ => none

/-- Source aliasing and compiled pointer aliasing both observe the write. -/
example : sourceValue (writeAndRead.run σ) = some 5 := by decide +kernel
example : targetCell 3 (run compiled.code machine) = some 5 := by decide +kernel
example : targetCell 3 (run compiled.code machine) ≠ some 7 := by decide +kernel

/-- The other element, other object, length cells and pointer locals survive. -/
example : targetCell 18 (run compiled.code machine) = some 9 := by decide +kernel
example : targetCell 21 (run compiled.code machine) = some 4 := by decide +kernel
example : targetCell 16 (run compiled.code machine) = some 2 := by decide +kernel
example : targetCell 20 (run compiled.code machine) = some 1 := by decide +kernel
example : targetCell 0 (run compiled.code machine) = some 20 := by decide +kernel
example : targetCell 1 (run compiled.code machine) = some 16 := by decide +kernel
example : targetCell 2 (run compiled.code machine) = some 16 := by decide +kernel

def outOfBounds : Prog C Γ Γ :=
  .cons (.assignMem (.index .dyn (.var first rfl) (.simple (.lit 2 rfl))) (.val five)) .nil
def rejected : CompiledProg 0 (Frag.init Γ) outOfBounds :=
  (compileProg 0 (Frag.init Γ) outOfBounds).get (by decide +kernel)

/-- The length boundary reverts in the source and in the generated code. -/
example : sourceValue (outOfBounds.run σ) = none := by decide +kernel
example : outOfBounds.run σ = .error .revert := sourceReverted_sound (by decide +kernel)
example : run rejected.code machine = .revert := Out.eq_revert (by decide +kernel)

/-- Unsupported allocation is explicitly refused by this compiler path. -/
example : (compileStmt (C := C) 0 (Frag.init Γ)
    (.declMem (.array (.prim .uint)) (.user "a")
      (some (.newArr (.lit 2 rfl) rfl)) rfl rfl)).isSome = false := by decide +kernel

private abbrev Δ : Ctx := .val .uint :: .mem (.array (.prim .uint)) :: Γ

/-- Declaration reads the original alias's length; rebinding then changes
which object a subsequent element read observes. -/
def declareAndRebind : Prog C Γ Δ :=
  .cons (.declMem (.array (.prim .uint)) (.user "a")
    (some (.alias (.var first rfl))) rfl rfl)
  (.cons (.declLocal .uint (.user "n") (some (.mlen (.var .here rfl) rfl)))
  (.cons (.rebindMem (.there .here)
    (.alias (.var (.there (.there (.there (.there (.there .here))))) rfl)))
  (.cons (.assignLocal (.there (.there .here))
    (.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl))))) .nil)))

def compiledLocals : CompiledProg 0 (Frag.init Γ) declareAndRebind :=
  (compileProg 0 (Frag.init Γ) declareAndRebind).get (by decide +kernel)

theorem fixture_six_cells : StateRepr 1 0 6 (Frag.init Γ) σ base machine := by
  refine ⟨fixture_repr.core, ⟨heap_repr.arrays, ?_, heap_repr.separated⟩,
    fixture_repr.pointers, by decide +kernel,
    ⟨fun r => (noStructs r).elim, fun r => (noStructs r).elim, fun r => (noStructs r).elim⟩,
    fixture_repr.separated, fixture_repr.refs⟩
  intro p r
  rcases ref_cases r with ⟨rfl, hr | hr⟩ <;> cases hr <;> decide +kernel

theorem locals_simulate : GrowingResult 1 0 6 (compiledLocals.cert.cost σ) compiledLocals.frag σ base machine
    (declareAndRebind.run σ) (run compiledLocals.code machine) :=
  compile_correct rfl fixture_six_cells (by decide +kernel) (.inl (by decide +kernel))

private def sourceAt {Ξ : Ctx} (i : Idx Ξ (.val .uint))
    (out : TRes (Solidity.Out C H Ξ)) : Option Int :=
  match out with
  | .ok o => some (TEnv.get i o.st.env).1
  | .error _ => none

example : sourceAt .here (declareAndRebind.run σ) = some 2 := by decide +kernel
example : sourceAt (.there (.there .here)) (declareAndRebind.run σ) = some 4 := by decide +kernel
example : targetCell 5 (run compiledLocals.code machine) = some 2 := by decide +kernel
example : targetCell 3 (run compiledLocals.code machine) = some 4 := by decide +kernel
example : targetCell 4 (run compiledLocals.code machine) = some 20 := by decide +kernel
example : targetCell 17 (run compiledLocals.code machine) = some 7 := by decide +kernel
example : targetCell 1 (run compiledLocals.code machine) = some 16 := by decide +kernel

/-- The post-state cannot claim to fit the old four-cell frame. -/
example (τ : State C Δ) (m : Machine) : ¬ StateRepr 1 0 4 compiledLocals.frag τ base m := by
  intro h
  have hc := h.locals
  change 6 ≤ 4 at hc
  omega

/-- The public entry selects the memory path and retains its full heap relation. -/
def checkedLocals : Compiler.Compilation 0 (Frag.init Γ) declareAndRebind :=
  (Compiler.compile 0 (Frag.init Γ) declareAndRebind).get (by decide +kernel)

example : checkedLocals.isMemory = true := by decide +kernel

theorem checked_locals_simulate : checkedLocals.Agrees 1 6 base σ machine :=
  checkedLocals.correct ⟨fixture_six_cells, by decide +kernel, .inl (by decide +kernel)⟩

def coreAssignment : Prog C Γ Γ := .cons (.assignLocal .here (.simple (.lit 8 rfl))) .nil
def checkedCore : Compiler.Compilation 0 (Frag.init Γ) coreAssignment :=
  (Compiler.compile 0 (Frag.init Γ) coreAssignment).get (by decide +kernel)

example : checkedCore.isMemory = false := by decide +kernel
example : targetCell 3 (run checkedCore.code machine) = some 8 := by decide +kernel

theorem checked_core_simulates : checkedCore.Agrees 1 4 base σ machine :=
  checkedCore.correct ⟨fixture_repr.core, fixture_repr.core.bound⟩

private abbrev Ξ : Ctx := .val .uint :: .val .uint :: Γ
private def firstTwo : Idx Ξ (.mem (.array (.prim .uint))) := .there (.there first)
private def otherTwo : Idx Ξ (.mem (.array (.prim .uint))) :=
  .there (.there (.there (.there (.there .here))))

/-- A default declaration and a core initializer coexist with composed memory
reads: the second write obtains both its index and RHS from array reads. -/
def indirectCopy : Prog C Γ Ξ :=
  .cons (.declLocal .uint (.user "z") none)
  (.cons (.declLocal .uint (.user "y") (some (.simple (.lit 1 rfl))))
  (.cons (.assignMem (.index .dyn (.var firstTwo rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.local .here))))
  (.cons (.assignMem
    (.index .dyn (.var firstTwo rfl)
      (.readMem (.index .dyn (.var firstTwo rfl) (.simple (.lit 0 rfl)))))
    (.val (.readMem (.index .dyn (.var otherTwo rfl) (.simple (.lit 0 rfl))))))
  (.cons (.assignLocal .here (.readMem (.index .dyn (.var firstTwo rfl)
    (.readMem (.index .dyn (.var firstTwo rfl) (.simple (.lit 0 rfl))))))) .nil))))

def checkedIndirect : Compiler.Compilation 0 (Frag.init Γ) indirectCopy :=
  (Compiler.compile 0 (Frag.init Γ) indirectCopy).get (by decide +kernel)

theorem indirect_simulates : checkedIndirect.Agrees 1 6 base σ machine := by
  apply checkedIndirect.correct
  rw [checkedIndirect.memory_input (by decide +kernel)]
  exact ⟨fixture_six_cells, by decide +kernel, .inl (by decide +kernel)⟩

private def sourceElement {Ω : Ctx} (i : Idx Ω (.mem (.array (.prim .uint))))
    (n : Int) (hn : PrimTy.uint.inRange n = true)
    (out : TRes (Solidity.Out C H Ω)) : Option Int :=
  match out with
  | .ok o => match (Val.readMem (.index .dyn (.var i rfl) (.simple (.lit n hn)))).evalT o.st with
    | .ok v => some v.1
    | .error _ => none
  | .error _ => none

example : checkedIndirect.isMemory = true := by decide +kernel
example : sourceAt .here (indirectCopy.run σ) = some 4 := by decide +kernel
example : sourceAt (.there .here) (indirectCopy.run σ) = some 0 := by decide +kernel
example : sourceElement firstTwo 0 rfl (indirectCopy.run σ) = some 1 := by decide +kernel
example : sourceElement firstTwo 1 rfl (indirectCopy.run σ) = some 4 := by decide +kernel
example : targetCell 5 (run checkedIndirect.code machine) = some 4 := by decide +kernel
example : targetCell 4 (run checkedIndirect.code machine) = some 0 := by decide +kernel
example : targetCell 17 (run checkedIndirect.code machine) = some 1 := by decide +kernel
example : targetCell 18 (run checkedIndirect.code machine) = some 4 := by decide +kernel
example : targetCell 21 (run checkedIndirect.code machine) = some 4 := by decide +kernel

def badRhsRead : Prog C Γ Γ :=
  .cons (.assignMem (.index .dyn (.var first rfl) zero)
    (.val (.readMem (.index .dyn (.var (.there (.there (.there .here))) rfl)
      (.simple (.lit 1 rfl)))))) .nil
def checkedBadRhs : Compiler.Compilation 0 (Frag.init Γ) badRhsRead :=
  (Compiler.compile 0 (Frag.init Γ) badRhsRead).get (by decide +kernel)

example : badRhsRead.run σ = .error .revert := sourceReverted_sound (by decide +kernel)
example : run checkedBadRhs.code machine = .revert := Out.eq_revert (by decide +kernel)

def badIndexRead : Prog C Γ Γ :=
  .cons (.assignMem (.index .dyn (.var first rfl)
    (.readMem (.index .dyn (.var (.there (.there (.there .here))) rfl) (.simple (.lit 1 rfl)))))
    (.val five)) .nil
def checkedBadIndex : Compiler.Compilation 0 (Frag.init Γ) badIndexRead :=
  (Compiler.compile 0 (Frag.init Γ) badIndexRead).get (by decide +kernel)

example : badIndexRead.run σ = .error .revert := sourceReverted_sound (by decide +kernel)
example : run checkedBadIndex.code machine = .revert := Out.eq_revert (by decide +kernel)

/-- Guards and arithmetic over memory reads use the memory compiler path. -/
example : (Compiler.compile (C := C) 0 (Frag.init Γ)
    (.cons (.require (.simple (.bool true)))
      (.cons (.assignLocal .here (.mlen (.var first rfl) rfl)) .nil))).isSome = true := by
  decide +kernel
example : (compileVal 0 (Frag.init Γ)
    (.binop .add rfl rfl (.readMem (.index .dyn (.var first rfl) zero))
      (.simple (.lit 1 rfl)))).isSome = true := by
  decide +kernel

end Solidity.Evm.Memory.CompileExamples
