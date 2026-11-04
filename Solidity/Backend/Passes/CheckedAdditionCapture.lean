import Solidity.Backend.PrimitivePackets.CheckedAdd.Agreement
import Solidity.Backend.Passes.MappedTail
import Solidity.Backend.Passes.CapturedValueStability

/-! Checked-add result capture through the actual public compiler. Arithmetic
and guards are owned by PrimitivePackets.CheckedAdd; this adapter retains the
full memory branch, selected maps and shared saved tails. Source declaration
lowering and public failure-byte/session adequacy remain separate obligations. -/
namespace Solidity.Backend.Passes.CheckedAdditionCapture
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets

variable {C : Contract} {Γ : Ctx}

def program (name : Var) (a b : Idx Γ (.val .uint)) : Prog C Γ (.val .uint :: Γ) :=
  .cons (.declLocal .uint name (some (CheckedAdd.value a b))) .nil

def selected (offset : Nat) (F : Frag Γ) (name : Var) (a b : Idx Γ (.val .uint)) :
    CompiledProg offset F (program (C:=C) name a b) :=
  ⟨F.push (.val .uint) .ok,
    ((CheckedAdd.selected (C:=C) offset F a b).code ++ [.mstore (cell (offset+Γ.length))]) ++ [],
    .cons (.declare F name (CheckedAdd.value a b) _ (CheckedAdd.selected offset F a b).cert)
      (.nil (F.push (.val .uint) .ok))⟩

theorem public_selection (offset : Nat) (F : Frag Γ) (name : Var) (a b : Idx Γ (.val .uint)) :
    Memory.compileProg offset F (program (C:=C) name a b) = some (selected (C:=C) offset F name a b) := by
  rfl

theorem capture_after (offset : Nat) (F : Frag Γ) (name : Var)
    (a b : Idx Γ (.val .uint)) (machine : Machine) (word : Word)
    (ran : run (CheckedAdd.selected (C:=C) offset F a b).code machine =
      .ok (machine.push word) 0) :
    run (selected (C:=C) offset F name a b).code machine =
      .ok (writeMachine machine (cell (offset+Γ.length)) word) 0 := by
  have stored : run ((CheckedAdd.selected (C:=C) offset F a b).code ++
      [.mstore (cell (offset+Γ.length))]) machine =
      .ok (writeMachine machine (cell (offset+Γ.length)) word) 0 := by
    rw [run_append_ok ran]
    rfl
  change run ((_ ++ _) ++ []) _ = _
  rw [run_append_ok stored]
  rfl

theorem input {offset L frame : Nat} {F : Frag Γ}
    (name : Var) (a b : Idx Γ (.val .uint))
    {base : Nat → Fin W} {state : State C Γ} {machine : Machine}
    (represented : StateRepr L offset frame F state base machine)
    (capacity : offset + (Γ.length+1) ≤ frame) :
    (Compilation.memory (selected (C:=C) offset F name a b)).Input L frame base state machine := by
  refine ⟨represented,?_,Or.inl rfl⟩
  change offset + max (max Γ.length (max (Γ.length+1) 0)) (Γ.length+1) ≤ frame
  omega

theorem intrinsic_success (name : Var) (a b : Idx Γ (.val .uint))
    (state : State C Γ) (v : PrimTy.uint.Denote)
    (evaluated : (CheckedAdd.value a b).evalT state = .ok v) :
    (program name a b).run state = .ok ⟨state.push (t:=.val .uint) v,List.prefix_refl _⟩ := by
  have declaration : (Stmt.declLocal .uint name (some (CheckedAdd.value a b))).run state =
      .ok ⟨state.push (t:=.val .uint) v,List.prefix_refl _⟩ := by
    change TRun.declLocal .uint (some (CheckedAdd.value a b)) state = _
    simp only [TRun.declLocal,evaluated,bind,Except.bind,pure,Except.pure]
  rw [program,Prog.run_cons_ok declaration]
  rfl

theorem intrinsic_revert (name : Var) (a b : Idx Γ (.val .uint))
    (state : State C Γ) (failed : (CheckedAdd.value a b).evalT state = .error .revert) :
    (program name a b).run state = .error .revert := by
  have declaration : (Stmt.declLocal .uint name (some (CheckedAdd.value a b))).run state = .error .revert := by
    change TRun.declLocal .uint (some (CheckedAdd.value a b)) state = _
    simp only [TRun.declLocal,failed,bind,Except.bind]
  exact Prog.run_cons_error declaration

/-- One source result and one physical captured word work for every saved tail.
The full memory branch retains the original map, heap, aliases and allocator
implication; the actual final machine is a single local write, not merely Rep. -/
theorem success {E : Source.Env} {srcΓ : Source.RCtx} {ι : Type}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int CheckedAdd.U)) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily CheckedAdd.U si ti source.1 target.env)
    (a b : ι) (x y : Int)
    (hx : CheckedAdd.U.lo ≤ x ∧ x ≤ CheckedAdd.U.hi)
    (hy : CheckedAdd.U.lo ≤ y ∧ y ≤ CheckedAdd.U.hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy)
    (fits : CheckedAdd.U.lo ≤ x+y ∧ x+y ≤ CheckedAdd.U.hi)
    {offset L frame : Nat} {F : Frag Γ} (name : Var)
    {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F target base machine)
    (capacity : offset + (Γ.length+1) ≤ frame) :
    Memory.compileProg offset F (program (C:=C) name (ti a) (ti b)) =
      some (selected (C:=C) offset F name (ti a) (ti b)) ∧
    (Source.evalE G {SF with checked := true} (fuel+3)
      (.binary .add (.local (si a)) (.local (si b)))).run source =
      (.ok (.val (.int (x+y) fits)),source) ∧
    (program name (ti a) (ti b)).run target =
      .ok ⟨target.push (t:=.val .uint) (integerValue CheckedAdd.U (x+y) fits),List.prefix_refl _⟩ ∧
    ∃ word, ReprV .uint (integerValue CheckedAdd.U (x+y) fits) word ∧ ∀ tail,
      let after := writeMachine {machine with stack := tail} (cell (offset+Γ.length)) word
      (Compilation.memory (selected (C:=C) offset F name (ti a) (ti b))).Input
        L frame base target {machine with stack := tail} ∧
      run (selected (C:=C) offset F name (ti a) (ti b)).code {machine with stack := tail} = .ok after 0 ∧
      MappedOutput (.memory (selected (C:=C) offset F name (ti a) (ti b))) L frame base target
        {machine with stack := tail} (target.push (t:=.val .uint) (integerValue CheckedAdd.U (x+y) fits)) after base ∧
      run [.mload (cell (offset+Γ.length))] after = .ok (after.push word) 0 := by
  have valueRun := CheckedAdd.value_success target (ti a) (ti b) x y hx hy
    (family.read a x hx readA) (family.read b y hy readB) fits
  obtain ⟨word,wordRepr,valueRuns⟩ := CapturedValueStability.value_shared
    (CheckedAdd.value (ti a) (ti b)) (CheckedAdd.selected offset F (ti a) (ti b))
    represented (integerValue CheckedAdd.U (x+y) fits) valueRun
  refine ⟨public_selection offset F name (ti a) (ti b),
    CheckedAdd.source_success G SF fuel source (si a) (si b) x y hx hy readA readB fits,
    intrinsic_success name (ti a) (ti b) target _ valueRun,word,wordRepr,?_⟩
  intro tail
  let after := writeMachine {machine with stack := tail} (cell (offset+Γ.length)) word
  have captured : run ((CheckedAdd.selected (C:=C) offset F (ti a) (ti b)).code ++
      [.mstore (cell (offset+Γ.length))]) {machine with stack := tail} = .ok after 0 := by
    rw [run_append_ok (valueRuns tail)]
    rfl
  have mapped : MappedOutput (.memory (selected (C:=C) offset F name (ti a) (ti b))) L frame base target
      {machine with stack := tail} (target.push (t:=.val .uint) (integerValue CheckedAdd.U (x+y) fits)) after base := by
    refine ⟨(represented.stack tail).consVal _ word wordRepr capacity,BaseExtends.refl base,?_⟩
    intro cursor positive owner space
    exact owner.localWrite (offset+Γ.length) (by omega) (by omega) word
  refine ⟨input name (ti a) (ti b) (represented.stack tail) capacity,?_,mapped,?_⟩
  · change run ((_ ++ _) ++ []) _ = _
    rw [run_append_ok captured]
    rfl
  · change Evm.Out.ok (after.push (after.mem (cell (offset+Γ.length)))) 0 = _
    have read : after.mem (cell (offset+Γ.length)) = word := upd_same _ _ _
    rw [read]

/-- Checked arithmetic panic bytes stay on the Source side; the selected
capture code has only the existing coarse revert, with no invented final state. -/
theorem overflow {E : Source.Env} {srcΓ : Source.RCtx} {ι : Type}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int CheckedAdd.U)) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily CheckedAdd.U si ti source.1 target.env)
    (a b : ι) (x y : Int)
    (hx : CheckedAdd.U.lo ≤ x ∧ x ≤ CheckedAdd.U.hi)
    (hy : CheckedAdd.U.lo ≤ y ∧ y ≤ CheckedAdd.U.hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy)
    (outside : ¬ (CheckedAdd.U.lo ≤ x+y ∧ x+y ≤ CheckedAdd.U.hi))
    {offset L frame : Nat} {F : Frag Γ} (name : Var)
    {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F target base machine)
    (capacity : offset + (Γ.length+1) ≤ frame) :
    Memory.compileProg offset F (program (C:=C) name (ti a) (ti b)) =
      some (selected (C:=C) offset F name (ti a) (ti b)) ∧
    (Source.evalE G {SF with checked := true} (fuel+3)
      (.binary .add (.local (si a)) (.local (si b)))).run source =
      (.error (.revert (Source.panicData .arithmetic)),source) ∧
    (program name (ti a) (ti b)).run target = .error .revert ∧
    ∀ tail, (Compilation.memory (selected (C:=C) offset F name (ti a) (ti b))).Input
      L frame base target {machine with stack := tail} ∧ run (selected (C:=C) offset F name (ti a) (ti b)).code {machine with stack := tail} = .revert := by
  refine ⟨public_selection offset F name (ti a) (ti b),
    CheckedAdd.source_overflow G SF fuel source (si a) (si b) x y hx hy readA readB outside,
    intrinsic_revert name (ti a) (ti b) target
      (CheckedAdd.value_overflow target (ti a) (ti b) x y hx hy
        (family.read a x hx readA) (family.read b y hy readB) outside),?_⟩
  intro tail
  refine ⟨input name (ti a) (ti b) (represented.stack tail) capacity,?_⟩
  have failed := CheckedAdd.target_overflow target (ti a) (ti b) x y hx hy
    (family.read a x hx readA) (family.read b y hy readB) outside represented tail
  change run ((_ ++ _) ++ []) _ = _
  exact run_append_revert (run_append_revert failed)

#print axioms success
#print axioms overflow
end Solidity.Backend.Passes.CheckedAdditionCapture
