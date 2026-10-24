import Solidity.Evm.MemoryAllocSource
import Solidity.Evm.Compiler

/-! Public allocation from a concrete typed state: local lengths, distinct
primitive arrays, allocating rebinding and retained old aliases/objects. -/
namespace Solidity.Evm.Memory.AllocSourceExamples

private def C : Contract := contract!{ }
private def size : Fin W := ⟨2, by decide⟩
private def cursor : Fin W := ⟨16, by decide⟩
private def Γ : Ctx := [.val .uint]
private def σ : State C Γ := (State.init C).push (t := .val .uint) (indexValue size)
private def n : Simple C Γ .uint := .local .here
private def bases : Nat → Fin W := fun _ => ⟨0, W_pos⟩
private def machine : Machine :=
  { Machine.init with mem := fun a =>
      if a = 0 then w[16] else if a = 1 then w[2] else if a = 5 then w[99] else w[0] }

/-- Both the scopedProgram state and allocator premises have an actual shared witness. -/
theorem initial_repr : StateRepr 1 1 6 (Frag.init Γ) σ bases machine ∧
    StructAllocatorRepr σ.heap bases 6 cursor machine := by
  have hn {R : RefTy} (r : HRef [] R) : False := by
    simpa only [List.getElem?_nil, reduceCtorEq] using r.get?
  have hh : HeapRepr σ.heap bases 6 machine :=
    ⟨fun r => (hn r).elim, fun r => (hn r).elim, fun r _ _ => (hn r).elim⟩
  constructor
  · refine ⟨?_, hh, ?_, by decide,
      ⟨fun r => (hn r).elim, fun r => (hn r).elim, fun r => (hn r).elim⟩,
      (fun _ r => (hn r).elim), RefFieldsRepr.withoutStructs _ _ _ (fun r => hn r)⟩
    · have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
      refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
      · intro p i
        cases i with
        | here => exact ReprV.uint_of rfl
        | there i => nomatch i
      · intro R i hi
        cases i with | there i => nomatch i
      · intro R i hi
        cases i with | there i => nomatch i
    · intro p i
      cases i with | there i => nomatch i
  · refine AllocatorRepr.withoutStructs ?_ (fun r => hn r)
    refine ⟨hh, ?_, fun r => (hn r).elim⟩
    refine ⟨by decide, by decide, rfl, ?_⟩
    intro addr ha
    change 16 ≤ addr at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · split <;> rename_i he
        · omega
        · rfl

private def σ1 := σ.allocPush (defaultArray .int size)
private def bases1 : Nat → Fin W := upd bases 0 cursor
private def machine1 : Machine := writeMachine (allocateMachine machine cursor size) 2 w[16]
private def cursor1 : Fin W := ⟨19, by decide⟩
private def frag1 : Frag (.mem (.array (.prim .int)) :: Γ) :=
  (Frag.init Γ).push (.mem (.array (.prim .int))) .ok

/-- The first real source declaration is simulated using its local length. -/
theorem first_repr : StateRepr 1 1 6 frag1 σ1 bases1 machine1 ∧
    StructAllocatorRepr σ1.heap bases1 6 cursor1 machine1 := by
  have h := newArray_correct initial_repr.1 initial_repr.2 (by decide)
    .int n rfl size rfl (by decide) (by decide)
  exact ⟨h.2.2.1, h.2.2.2.1⟩

private def zero : Simple C (.mem (.array (.prim .int)) :: Γ) .uint := .lit 0 (by decide)
private def σ2 := σ1.allocPush (defaultArray .bool ⟨0, W_pos⟩)
private def bases2 : Nat → Fin W := upd bases1 1 cursor1
private def machine2 : Machine := writeMachine (allocateMachine machine1 cursor1 ⟨0, W_pos⟩) 3 w[19]
private def frag2 := frag1.push (.mem (.array (.prim .bool))) .ok

/-- A second typed source allocation retains the older pointer and local value. -/
theorem second_repr : StateRepr 1 1 6 frag2 σ2 bases2 machine2 ∧
    StructAllocatorRepr σ2.heap bases2 6 ⟨20, by decide⟩ machine2 := by
  have h := newArray_correct first_repr.1 first_repr.2 (by decide)
    .bool zero rfl ⟨0, W_pos⟩ rfl (by decide) (by decide)
  exact ⟨h.2.2.1, h.2.2.2.1⟩

private def Δ : Ctx := [.mem (.array (.prim .bool)), .mem (.array (.prim .int)), .val .uint]
private def program : Prog C Γ Δ :=
  .cons (.declMem (.array (.prim .int)) (.user "xs") (some (.newArr n rfl)) rfl rfl)
    (.cons (.declMem (.array (.prim .bool)) (.user "empty") (some (.newArr zero rfl)) rfl rfl) .nil)

private def compiled : Compiler.Compilation 1 (Frag.init Γ) program :=
  (Compiler.compile 1 (Frag.init Γ) program).get (by decide +kernel)

/-- The public compiler accepts the declarations and proves their common agreement. -/
theorem compiled_simulates : compiled.Agrees 1 6 bases σ machine :=
  compiled.correct ⟨initial_repr.1, by decide,
    .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩⟩

example : compiled.isMemory = true := by decide +kernel

private def sourceObserve : TRes (Solidity.Out C σ.H Δ) → Option (List Nat)
  | .error _ => none
  | .ok o => do
    let empty ← o.st.env.1
    let signed ← o.st.env.2.1
    pure [o.st.H.length, empty.id, signed.id, o.st.heap.len empty .dyn,
      o.st.heap.len signed .dyn, o.st.env.2.2.1.val.toNat]

private def code : List Instr := compiled.code
private def wordValue : Word → Option Nat
  | .val v => some v.val
  | .slot _ => none
private def targetObserve : Out → Option (List Nat)
  | .ok m _ => do
    let cells ← [0, 1, 2, 3, 5, 16, 17, 18, 19].mapM (fun a => wordValue (m.mem a))
    pure (m.stack.length :: cells)
  | _ => none
private def reverted : Out → Bool
  | .revert => true
  | _ => false
private def top : Out → Option Nat
  | .ok m _ => m.stack.head?.bind wordValue
  | _ => none

/-- Actual source execution creates two typed identities with the expected lengths. -/
theorem source_run : sourceObserve (program.run σ) = some [2, 1, 0, 0, 2, 2] := by
  decide +kernel

/-- Actual target execution retains the local length and sentinel, and stores both pointers. -/
theorem target_run : targetObserve (run code machine) = some [0, 20, 2, 16, 19, 99, 2, 0, 0, 0] := by
  decide +kernel

/-- The signed array's first element is the represented integer default. -/
theorem default_read : top (run (code ++ [.mload 2, .push w[0]] ++ readArrayStackCode) machine) = some 0 := by
  decide +kernel

/-- Reading the fresh empty array through its actual local pointer reverts. -/
theorem empty_reverts : reverted (run (code ++ [.mload 3, .push w[0]] ++ readArrayStackCode) machine) = true := by
  decide +kernel

private def Ω : Ctx := [.mem (.array (.prim .bool)), .mem (.array (.prim .int)),
  .mem (.array (.prim .int)), .val .uint]
private def mixed : Prog C Γ Ω :=
  .cons (.declMem (.array (.prim .int)) (.user "xs") (some (.newArr n rfl)) rfl rfl)
  (.cons (.declMem (.array (.prim .int)) (.user "alias")
    (some (.alias (.var .here rfl))) rfl rfl)
  (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.lit 7 rfl))))
  (.cons (.assignLocal (.there (.there .here)) (.simple (.lit 3 rfl)))
  (.cons (.declMem (.array (.prim .bool)) (.user "flags")
    (some (.newArr (.local (.there (.there .here))) rfl)) rfl rfl)
  (.cons (.require (.binop .eqB rfl rfl
    (.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl))))
    (.simple (.lit 7 rfl)))) .nil)))))

private def compiledMixed : Compiler.Compilation 1 (Frag.init Γ) mixed :=
  (Compiler.compile 1 (Frag.init Γ) mixed).get (by decide +kernel)

/-- Allocations compose through aliases, a nonzero write, a changed length and a later read. -/
theorem mixed_simulates : compiledMixed.Agrees 1 6 bases σ machine := by
  apply compiledMixed.correct
  rw [compiledMixed.memory_input (by decide +kernel)]
  refine ⟨initial_repr.1, ?_, ?_⟩
  · decide +kernel
  · have hcost : allocationCostProg mixed σ = 7 := by decide +kernel
    rw [hcost]
    exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

private def sourceSigned : TRes (Solidity.Out C σ.H Ω) → Option Int
  | .error _ => none
  | .ok o => match (Val.readMem (.index .dyn (.var (.there .here) rfl)
      (.simple (.lit 0 rfl))) : Val C Ω .int).evalT o.st with
    | .ok v => some v.val
    | .error _ => none

/-- An old source alias retains its nonzero element after another allocation. -/
theorem mixed_source : sourceSigned (mixed.run σ) = some 7 := by decide +kernel

/-- The public compiler's old aliases still point to the written array. -/
theorem mixed_target : targetObserve (run compiledMixed.code machine) =
    some [0, 23, 3, 16, 16, 99, 2, 7, 0, 3] := by decide +kernel

/-- The updated local determines the later bool array's bounds and defaults. -/
theorem mixed_default : top (run (compiledMixed.code ++ [.mload 4, .push w[2]] ++
    readArrayStackCode) machine) = some 0 := by decide +kernel

private def maximal : Prog C Γ (.mem (.array (.prim .int)) :: Γ) :=
  .cons (.declMem (.array (.prim .int)) (.user "maximal")
    (some (.newArr (.lit (wMax.val : Int) (PrimTy.inRange_uint_of_lt wMax.isLt)) rfl)) rfl rfl) .nil
private def skipped : Prog C Γ (.mem (.array (.prim .int)) :: Γ) := .cons .revert maximal
private def compiledSkipped : Compiler.Compilation 1 (Frag.init Γ) skipped :=
  (Compiler.compile 1 (Frag.init Γ) skipped).get (by decide +kernel)

/-- A prior revert needs no allocator or space for the unreachable maximal allocation. -/
theorem skipped_simulates : compiledSkipped.Agrees 1 6 bases σ machine :=
  compiledSkipped.correct ⟨initial_repr.1, by decide, .inl (by decide +kernel)⟩

theorem skipped_target : reverted (run compiledSkipped.code machine) = true := by decide +kernel

/-- Reaching a request for the whole address space, including its header, cannot fit. -/
theorem whole_space_rejected : ¬ AllocationInput 1 6 W σ bases machine := by
  intro h
  rcases h with hz | ⟨_, c, _, hs⟩
  · exact (Nat.ne_of_gt W_pos) hz
  · omega

private def compiledMaximal : Compiler.Compilation 1 (Frag.init Γ) maximal :=
  (Compiler.compile 1 (Frag.init Γ) maximal).get (by decide +kernel)

/-- The public capacity input rejects a reached maximal request without constructing its heap. -/
theorem maximal_input_rejected : ¬ compiledMaximal.Input 1 6 bases σ machine := by
  intro h
  have hi : AllocationInput 1 6 (allocationCostProg maximal σ) σ bases machine := h.2.2
  have hc : allocationCostProg maximal σ = W := by
    change wMax.val + 1 = W
    change W - 1 + 1 = W
    have hp : 0 < W := W_pos
    omega
  rw [hc] at hi
  exact whole_space_rejected hi

private def Ρ : Ctx := [.mem (.array (.prim .int)), .mem (.array (.prim .int)), .val .uint]
private def rebindings : Prog C Γ Ρ :=
  .cons (.declMem (.array (.prim .int)) (.user "xs") (some (.newArr n rfl)) rfl rfl)
  (.cons (.declMem (.array (.prim .int)) (.user "old")
    (some (.alias (.var .here rfl))) rfl rfl)
  (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.lit 7 rfl))))
  (.cons (.rebindMem (.there .here) (.newArr (.local (.there (.there .here))) rfl))
  (.cons (.assignMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.lit 9 rfl))))
  (.cons (.require (.binop .eqB rfl rfl
    (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))) (.simple (.lit 7 rfl))))
  (.cons (.require (.binop .eqB rfl rfl
    (.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl)))) (.simple (.lit 9 rfl))))
  (.cons (.rebindMem (.there .here) (.newArr (.lit 0 rfl) rfl)) .nil)))))))

private def compiledRebindings : Compiler.Compilation 1 (Frag.init Γ) rebindings :=
  (Compiler.compile 1 (Frag.init Γ) rebindings).get (by decide +kernel)

/-- Replacing the original twice preserves its older alias and all allocated objects. -/
theorem rebindings_simulate : compiledRebindings.Agrees 1 6 bases σ machine := by
  apply compiledRebindings.correct
  rw [compiledRebindings.memory_input (by decide +kernel)]
  refine ⟨initial_repr.1, ?_, ?_⟩
  · decide +kernel
  · have hcost : allocationCostProg rebindings σ = 7 := by decide +kernel
    rw [hcost]
    exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

private def rebindSource : TRes (Solidity.Out C σ.H Ρ) → Option (List Nat)
  | .error _ => none
  | .ok o => do
    let old ← o.st.env.1
    let fresh ← o.st.env.2.1
    pure [o.st.H.length, old.id, fresh.id, o.st.heap.len old .dyn,
      o.st.heap.len fresh .dyn, o.st.env.2.2.1.val.toNat]

theorem rebindings_source : rebindSource (rebindings.run σ) = some [3, 0, 2, 2, 0, 2] := by
  decide +kernel

theorem rebindings_target : targetObserve (run compiledRebindings.code machine) =
    some [0, 23, 2, 22, 16, 99, 2, 7, 0, 2] := by decide +kernel

/-- The older alias still reads seven after the destination points to the empty third object. -/
theorem rebindings_old_read : top (run (compiledRebindings.code ++ [.mload 3, .push w[0]] ++
    readArrayStackCode) machine) = some 7 := by decide +kernel

/-- The rebound empty destination rejects a read that succeeds through its older alias. -/
theorem rebindings_empty : reverted (run (compiledRebindings.code ++ [.mload 2, .push w[0]] ++
    readArrayStackCode) machine) = true := by decide +kernel

private def retainedSource : TRes (Solidity.Out C σ.H Ρ) → Option Int
  | .error _ => none
  | .ok o => do
    let r ← HRef.ofId? o.st.H (.array (.prim .int)) 1
    let v ← o.st.heap.readAddr (.index r .dyn (indexValue ⟨0, W_pos⟩))
    pure v.val

/-- The intermediate object remains in the actual typed heap after losing its last local. -/
theorem rebindings_retained_source : retainedSource (rebindings.run σ) = some 9 := by
  decide +kernel

private def retainedTarget : Out → Option (List Nat)
  | .ok m _ => [20, 21, 22].mapM (fun a => wordValue (m.mem a))
  | _ => none

theorem rebindings_retained_target : retainedTarget (run compiledRebindings.code machine) =
    some [9, 0, 0] := by decide +kernel

/-- Allocating rebinding cannot overlap the cursor with a base-zero local frame. -/
example : (compileStmt (C := C) 0 frag1
    (.rebindMem .here (.newArr (.lit 0 rfl) rfl))).isSome = false := by decide +kernel

private def maximalRebind : Prog C (.mem (.array (.prim .int)) :: Γ)
    (.mem (.array (.prim .int)) :: Γ) :=
  .cons (.rebindMem .here
    (.newArr (.lit (wMax.val : Int) (PrimTy.inRange_uint_of_lt wMax.isLt)) rfl)) .nil
private def compiledMaximalRebind : Compiler.Compilation 1 frag1 maximalRebind :=
  (Compiler.compile 1 frag1 maximalRebind).get (by decide +kernel)

/-- Allocating rebinding contributes its header and length to the public capacity input. -/
theorem maximal_rebind_rejected : ¬ compiledMaximalRebind.Input 1 6 bases1 σ1 machine1 := by
  intro h
  have hi : AllocationInput 1 6 (allocationCostProg maximalRebind σ1) σ1 bases1 machine1 := h.2.2
  have hc : allocationCostProg maximalRebind σ1 = W := by
    change W - 1 + 1 = W
    have hp : 0 < W := W_pos
    omega
  rw [hc] at hi
  rcases hi with hz | ⟨_, c, _, hs⟩
  · exact (Nat.ne_of_gt W_pos) hz
  · omega

local instance : InContract := ⟨C⟩

private def surface := (sol{
  uint n = 2;
  int[] memory xs = new int[](n);
  int[] memory old = xs;
  old[0] = 7;
  xs = new int[](0);
  require(old[0] == 7);
} : Prog C [] _)

/-- The ordinary Solidity elaborator emits supported declaration and rebinding clauses. -/
theorem surface_accepted : (Compiler.compile 1 (Frag.init []) surface).isSome = true := by
  decide +kernel

private def scopeBody : Prog C Γ [.val .uint, .mem (.array (.prim .int)), .val .uint] :=
  .cons (.declMem (.array (.prim .int)) (.user "temp") (some (.newArr n rfl)) rfl rfl)
  (.cons (.declLocal .uint (.user "local") (some (.simple (.lit 9 rfl))))
  (.cons (.assignLocal (.there (.there .here)) (.simple (.lit 3 rfl)))
  (.cons (.assignMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.lit 7 rfl)))) .nil)))

private def scopes : Prog C Γ Γ := .cons (.block scopeBody) (.cons (.block scopeBody) .nil)
private def compiledScopes : Compiler.Compilation 1 (Frag.init Γ) scopes :=
  (Compiler.compile 1 (Frag.init Γ) scopes).get (by decide +kernel)

/-- Explicit blocks pop locals, retain older updates and reuse cells above the outer frame. -/
theorem scopes_simulate : compiledScopes.Agrees 1 6 bases σ machine := by
  apply compiledScopes.correct
  rw [compiledScopes.memory_input (by decide +kernel)]
  refine ⟨initial_repr.1, by decide +kernel, ?_⟩
  have hc : allocationCostProg scopes σ = 7 := by decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

private def scopeSource (out : TRes (Solidity.Out C [] Γ)) : Option (List Nat) :=
  match out with
  | .error _ => none
  | .ok o => some [o.st.H.length, o.st.env.1.val.toNat]

theorem scopes_source : scopeSource (scopes.run σ) = some [2, 3] := by decide +kernel

private def scopeTarget (out : Out) : Option (List Nat) :=
  match out with
  | .revert | .fault => none
  | .ok m _ => do
    let cells ← [0, 1, 2, 3, 5, 16, 17, 19, 20].mapM (fun a => wordValue (m.mem a))
    pure (m.stack.length :: cells)

theorem scopes_target : scopeTarget (run compiledScopes.code machine) =
    some [0, 23, 3, 19, 9, 99, 2, 7, 3, 7] := by decide +kernel

/-- The final context fits, but temporary block locals still need their own reserved cells. -/
theorem scopes_frame_rejected : ¬ compiledScopes.Input 1 3 bases σ machine := by
  rw [compiledScopes.memory_input (by decide +kernel)]
  intro h
  have hn : frameNeedProg scopes = 3 := by decide +kernel
  have hc := h.2.1
  rw [hn] at hc
  omega

private def branches := (sol{
  int[] memory xs = new int[](1);
  int[] memory old = xs;
  if (true) {
    int[] memory temp = new int[](1);
    temp[0] = 7;
    xs = temp;
  } else {
    xs = new int[](115792089237316195423570985008687907853269984665640564039457584007913129639935);
  }
  require(xs[0] == 7);
  require(old[0] == 0);
  if (true) { bool[] memory reuse = new bool[](0); }
} : Prog C [] _)

private def compiledBranches : Compiler.Compilation 1 (Frag.init []) branches :=
  (Compiler.compile 1 (Frag.init []) branches).get (by decide +kernel)

private theorem empty_repr : StateRepr 1 1 6 (Frag.init []) (State.init C) bases machine :=
  initial_repr.1.drop (.push .refl)

/-- Surface branches escape a live pointer, reuse branch locals and skip an oversized allocation. -/
theorem branches_simulate : compiledBranches.Agrees 1 6 bases (State.init C) machine := by
  apply compiledBranches.correct
  rw [compiledBranches.memory_input (by decide +kernel)]
  refine ⟨empty_repr, by decide +kernel, ?_⟩
  have hc : allocationCostProg branches (State.init C) = 5 := by decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

private def BranchΓ : Ctx := [.mem (.array (.prim .int)), .mem (.array (.prim .int))]
private def branchSource (out : TRes (Solidity.Out C [] BranchΓ)) : Option (List Int) :=
  match out with
  | .error _ => none
  | .ok o => do
    let current ← (Val.readMem (.index .dyn (.var (.there .here) rfl)
      (.simple (.lit 0 rfl))) : Val C BranchΓ .int).evalT o.st |>.toOption
    let old ← (Val.readMem (.index .dyn (.var .here rfl)
      (.simple (.lit 0 rfl))) : Val C BranchΓ .int).evalT o.st |>.toOption
    pure [o.st.H.length, current.val, old.val]

theorem branches_source : branchSource (branches.run (State.init C)) = some [3, 7, 0] := by
  decide +kernel

private def branchTarget (out : Out) : Option (List Nat) :=
  match out with
  | .revert | .fault => none
  | .ok m _ => do
    let cells ← [0, 1, 2, 3, 5, 16, 17, 18, 19, 20].mapM (fun a => wordValue (m.mem a))
    pure (m.stack.length :: cells)

theorem branches_target : branchTarget (run compiledBranches.code machine) =
    some [0, 21, 18, 16, 20, 99, 1, 0, 1, 7, 0] := by decide +kernel

private def elseBranch := (sol{
  int[] memory xs = new int[](1);
  if (false) {
    xs = new int[](115792089237316195423570985008687907853269984665640564039457584007913129639935);
  } else {
    int[] memory temp = new int[](1);
    temp[0] = 9;
    xs = temp;
  }
  require(xs[0] == 9);
} : Prog C [] _)
private def compiledElse : Compiler.Compilation 1 (Frag.init []) elseBranch :=
  (Compiler.compile 1 (Frag.init []) elseBranch).get (by decide +kernel)

theorem else_simulates : compiledElse.Agrees 1 6 bases (State.init C) machine := by
  apply compiledElse.correct
  rw [compiledElse.memory_input (by decide +kernel)]
  refine ⟨empty_repr, by decide +kernel, ?_⟩
  have hc : allocationCostProg elseBranch (State.init C) = 4 := by decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

theorem else_target : top (run (compiledElse.code ++ [.mload 1, .push w[0]] ++
    readArrayStackCode) machine) = some 9 := by decide +kernel

private def revertBranches (v : Bool) : Prog C Γ Γ :=
  .cons (.ite (.simple (.bool v)) (.cons .revert maximal) (.cons .revert maximal)) .nil
private def compiledRevertBranches (v : Bool) : Compiler.Compilation 1 (Frag.init Γ) (revertBranches v) :=
  (Compiler.compile 1 (Frag.init Γ) (revertBranches v)).get (by cases v <;> decide +kernel)

/-- Either selected branch reverts before its maximal allocation, with no capacity premise. -/
theorem branch_revert_simulates (v : Bool) :
    (compiledRevertBranches v).Agrees 1 6 bases σ machine := by
  apply (compiledRevertBranches v).correct
  rw [(compiledRevertBranches v).memory_input (by cases v <;> decide +kernel)]
  refine ⟨initial_repr.1, ?_, .inl ?_⟩
  · cases v <;> decide +kernel
  · cases v <;> decide +kernel

theorem branch_revert_source (v : Bool) : (revertBranches v).run σ = .error .revert := by
  cases v <;> rfl

theorem branch_revert_target (v : Bool) : reverted (run (compiledRevertBranches v).code machine) = true := by
  cases v <;> decide +kernel

private def badCondition := (sol{
  int[] memory xs = new int[](0);
  if (xs[0] == 0) {
    xs = new int[](115792089237316195423570985008687907853269984665640564039457584007913129639935);
  } else {
    xs = new int[](115792089237316195423570985008687907853269984665640564039457584007913129639935);
  }
} : Prog C [] _)
private def compiledBadCondition : Compiler.Compilation 1 (Frag.init []) badCondition :=
  (Compiler.compile 1 (Frag.init []) badCondition).get (by decide +kernel)

/-- A failed condition allocates only the preceding empty array, never either branch. -/
theorem bad_condition_simulates : compiledBadCondition.Agrees 1 6 bases (State.init C) machine := by
  apply compiledBadCondition.correct
  rw [compiledBadCondition.memory_input (by decide +kernel)]
  refine ⟨empty_repr, by decide +kernel, ?_⟩
  have hc : allocationCostProg badCondition (State.init C) = 1 := by decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

private def sourceReverts {H : HTy} {Γ : Ctx} : TRes (Solidity.Out C H Γ) → Bool
  | .error .revert => true
  | _ => false

theorem bad_condition_source : sourceReverts (badCondition.run (State.init C)) = true := by
  decide +kernel

theorem bad_condition_target : reverted (run compiledBadCondition.code machine) = true := by
  decide +kernel

private def deletions := (sol{
  uint[] memory xs = new uint[](2);
  uint[] memory old = xs;
  xs[0] = 7;
  delete xs[xs[1]];
  require(old[0] == 0);
  xs[1] = 9;
  delete xs;
  require(xs.length == 0);
  require(old.length == 2);
  require(old[1] == 9);
  delete xs;
  require(xs.length == 0);
} : Prog C [] _)
private def compiledDeletions : Compiler.Compilation 1 (Frag.init []) deletions :=
  (Compiler.compile 1 (Frag.init []) deletions).get (by decide +kernel)

/-- Element deletion is shared; local deletion, even of an empty array, allocates. -/
theorem deletions_cost : allocationCostProg deletions (State.init C) = 5 := by
  decide +kernel

theorem deletions_simulate : compiledDeletions.Agrees 1 6 bases (State.init C) machine := by
  apply compiledDeletions.correct
  rw [compiledDeletions.memory_input (by decide +kernel)]
  refine ⟨empty_repr, by decide +kernel, ?_⟩
  rw [deletions_cost]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

private abbrev DeletionΓ : Ctx := [.mem (.array (.prim .uint)), .mem (.array (.prim .uint))]
private def deletionSource (out : TRes (Solidity.Out C [] DeletionΓ)) : Option (List Int) := do
  let o ← out.toOption
  let current ← o.st.env.2.1
  let old ← o.st.env.1
  let first ← (Val.readMem (.index .dyn (.var .here rfl)
    (.simple (.lit 0 rfl))) : Val C DeletionΓ .uint).evalT o.st |>.toOption
  let last ← (Val.readMem (.index .dyn (.var .here rfl)
    (.simple (.lit 1 rfl))) : Val C DeletionΓ .uint).evalT o.st |>.toOption
  pure [o.st.H.length, current.id, old.id, o.st.heap.len current .dyn,
    o.st.heap.len old .dyn, first.val, last.val]

private def deletedCells (out : Out) : Option (List Nat) := do
  let .ok m _ := out | none
  [0, 1, 2, 5, 16, 17, 18, 19, 20].mapM (fun a => wordValue (m.mem a))

/-- The old alias retains the zeroed first element and the later second-element write. -/
theorem deletions_source : deletionSource (deletions.run (State.init C)) =
    some [3, 2, 0, 0, 2, 0, 9] := by
  decide +kernel

/-- Both fresh empty headers coexist with the old populated object and sentinel. -/
theorem deletions_target : deletedCells (run compiledDeletions.code machine) =
    some [21, 20, 16, 99, 2, 0, 9, 0, 0] := by
  decide +kernel

private def typedDeletions := (sol{
  int[] memory signed = new int[](1);
  signed[0] = -7;
  delete signed[0];
  require(signed[0] == 0);
  delete signed;
  require(signed.length == 0);
  bool[] memory flags = new bool[](1);
  flags[0] = true;
  delete flags[0];
  require(!flags[0]);
  delete flags;
  require(flags.length == 0);
} : Prog C [] _)
private def compiledTypedDeletions : Compiler.Compilation 1 (Frag.init []) typedDeletions :=
  (Compiler.compile 1 (Frag.init []) typedDeletions).get (by decide +kernel)

theorem typed_deletions_simulate : compiledTypedDeletions.Agrees 1 6 bases (State.init C) machine := by
  apply compiledTypedDeletions.correct
  rw [compiledTypedDeletions.memory_input (by decide +kernel)]
  refine ⟨empty_repr, by decide +kernel, ?_⟩
  have hc : allocationCostProg typedDeletions (State.init C) = 6 := by decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

theorem typed_deletions_source : (typedDeletions.run (State.init C)).toOption.isSome = true := by
  decide +kernel

private def typedDeletionCells (out : Out) : Option (List Nat) := do
  let .ok m _ := out | none
  [0, 1, 2, 16, 17, 18, 19, 20, 21].mapM (fun a => wordValue (m.mem a))

theorem typed_deletions_target : typedDeletionCells (run compiledTypedDeletions.code machine) =
    some [22, 18, 21, 1, 0, 0, 1, 0, 0] := by
  decide +kernel

private def failedDeletion := (sol{
  uint[] memory xs = new uint[](1);
  delete xs[xs[1]];
  delete xs;
  uint[] memory unreachable = new uint[](115792089237316195423570985008687907853269984665640564039457584007913129639935);
} : Prog C [] _)
private def compiledFailedDeletion : Compiler.Compilation 1 (Frag.init []) failedDeletion :=
  (Compiler.compile 1 (Frag.init []) failedDeletion).get (by decide +kernel)

/-- A failed index read skips the later maximal allocation and needs only two cells. -/
theorem failed_deletion_simulates : compiledFailedDeletion.Agrees 1 6 bases (State.init C) machine := by
  apply compiledFailedDeletion.correct
  rw [compiledFailedDeletion.memory_input (by decide +kernel)]
  refine ⟨empty_repr, by decide +kernel, ?_⟩
  have hc : allocationCostProg failedDeletion (State.init C) = 2 := by decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

theorem failed_deletion_source : sourceReverts (failedDeletion.run (State.init C)) = true := by
  decide +kernel

theorem failed_deletion_target : run compiledFailedDeletion.code machine = .revert :=
  Out.eq_revert (by decide +kernel)

private def boundaryDeletion (empty : Bool) : Prog C [] [.mem (.array (.prim .uint))] :=
  if empty then sol{ uint[] memory xs = new uint[](0); delete xs[0]; }
  else sol{ uint[] memory xs = new uint[](1); delete xs[1]; }
private def compiledBoundaryDeletion (empty : Bool) :
    Compiler.Compilation 1 (Frag.init []) (boundaryDeletion empty) :=
  (Compiler.compile 1 (Frag.init []) (boundaryDeletion empty)).get (by cases empty <;> decide +kernel)

/-- The length boundary fails for both an empty array and a populated array. -/
theorem boundary_deletion_simulates (empty : Bool) :
    (compiledBoundaryDeletion empty).Agrees 1 6 bases (State.init C) machine := by
  apply (compiledBoundaryDeletion empty).correct
  rw [(compiledBoundaryDeletion empty).memory_input (by cases empty <;> decide +kernel)]
  refine ⟨empty_repr, by cases empty <;> decide +kernel, ?_⟩
  have hc : allocationCostProg (boundaryDeletion empty) (State.init C) =
      if empty then 1 else 2 := by cases empty <;> decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by cases empty <;> decide +kernel⟩

theorem boundary_deletion_source (empty : Bool) :
    sourceReverts ((boundaryDeletion empty).run (State.init C)) = true := by
  cases empty <;> decide +kernel

theorem boundary_deletion_target (empty : Bool) :
    run (compiledBoundaryDeletion empty).code machine = .revert := by
  cases empty <;> exact Out.eq_revert (by decide +kernel)

/-- Array-local deletion requires a frame above the allocator cursor cell. -/
example : (Compiler.compile (C := C) 0 (Frag.init [.mem (.array (.prim .uint))])
    (.cons (.deleteMem (.var .here rfl) rfl) .nil)).isNone = true := by
  decide +kernel

private def compoundSigned := (sol{
  int[] memory xs = new int[](1);
  xs[0] = -7;
  xs[0] += -2;
  xs[0] *= 3;
  xs[0] /= 2;
  xs[0] %= 5;
  xs[0] -= 4;
  int total = 0;
  total += xs[0];
  require(total == -7);
} : Prog C [] _)
private def compiledCompoundSigned : Compiler.Compilation 1 (Frag.init []) compoundSigned :=
  (Compiler.compile 1 (Frag.init []) compoundSigned).get (by decide +kernel)

theorem compound_signed_simulates : compiledCompoundSigned.Agrees 1 6 bases (State.init C) machine := by
  apply compiledCompoundSigned.correct
  rw [compiledCompoundSigned.memory_input (by decide +kernel)]
  refine ⟨empty_repr, by decide +kernel, ?_⟩
  have hc : allocationCostProg compoundSigned (State.init C) = 2 := by decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

theorem compound_signed_source : (compoundSigned.run (State.init C)).toOption.isSome = true := by
  decide +kernel

theorem compound_signed_target : top (run (compiledCompoundSigned.code ++ [.mload 2]) machine) =
    some (W - 7) := by
  decide +kernel

private def signedCompoundFailure (division : Bool) : Prog C [] [.mem (.array (.prim .int))] :=
  if division then sol{
    int[] memory xs = new int[](1);
    xs[0] = -57896044618658097711785492504343953926634992332820282019728792003956564819968;
    xs[0] /= -1;
  } else sol{
    int[] memory xs = new int[](1);
    xs[0] = 57896044618658097711785492504343953926634992332820282019728792003956564819967;
    xs[0] += 1;
  }
private def compiledSignedCompoundFailure (division : Bool) :
    Compiler.Compilation 1 (Frag.init []) (signedCompoundFailure division) :=
  (Compiler.compile 1 (Frag.init []) (signedCompoundFailure division)).get
    (by cases division <;> decide +kernel)

/-- Signed range checks reject both the division edge and addition past int256.max. -/
theorem signed_compound_failure_simulates (division : Bool) :
    (compiledSignedCompoundFailure division).Agrees 1 6 bases (State.init C) machine := by
  apply (compiledSignedCompoundFailure division).correct
  rw [(compiledSignedCompoundFailure division).memory_input (by cases division <;> decide +kernel)]
  refine ⟨empty_repr, by cases division <;> decide +kernel, ?_⟩
  have hc : allocationCostProg (signedCompoundFailure division) (State.init C) = 2 := by
    cases division <;> decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

theorem signed_compound_failure_source (division : Bool) :
    sourceReverts ((signedCompoundFailure division).run (State.init C)) = true := by
  cases division <;> decide +kernel

theorem signed_compound_failure_target (division : Bool) :
    run (compiledSignedCompoundFailure division).code machine = .revert := by
  cases division <;> exact Out.eq_revert (by decide +kernel)

private def increments := (sol{
  uint[] memory xs = new uint[](2);
  xs[1] = 1;
  uint[] memory alias = xs;
  ++alias[xs[1]];
  require(xs[1] == 2);
} : Prog C [] _)
private def compiledIncrements : Compiler.Compilation 1 (Frag.init []) increments :=
  (Compiler.compile 1 (Frag.init []) increments).get (by decide +kernel)

/-- The computed index reads the old aliased element before incrementing that element. -/
theorem increments_simulate : compiledIncrements.Agrees 1 6 bases (State.init C) machine := by
  apply compiledIncrements.correct
  rw [compiledIncrements.memory_input (by decide +kernel)]
  refine ⟨empty_repr, by decide +kernel, ?_⟩
  have hc : allocationCostProg increments (State.init C) = 3 := by decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

theorem increments_source : (increments.run (State.init C)).toOption.isSome = true := by
  decide +kernel

private def incrementCells (out : Out) : Option (List Nat) := do
  let .ok m _ := out | none
  [0, 1, 2, 5, 16, 17, 18].mapM (fun a => wordValue (m.mem a))

theorem increments_target : incrementCells (run compiledIncrements.code machine) =
    some [19, 16, 16, 99, 2, 0, 2] := by
  decide +kernel

private def signedIncrements (up : Bool) : Prog C [] [.val .int, .mem (.array (.prim .int))] :=
  if up then sol{
    int[] memory xs = new int[](1);
    xs[0] = -7;
    ++xs[0];
    int total = xs[0];
    ++total;
    require(total == -5);
  } else sol{
    int[] memory xs = new int[](1);
    xs[0] = -7;
    xs[0]−−;
    int total = xs[0];
    total−−;
    require(total == -9);
  }
private def compiledSignedIncrements (up : Bool) :
    Compiler.Compilation 1 (Frag.init []) (signedIncrements up) :=
  (Compiler.compile 1 (Frag.init []) (signedIncrements up)).get (by cases up <;> decide +kernel)

theorem signed_increments_simulate (up : Bool) :
    (compiledSignedIncrements up).Agrees 1 6 bases (State.init C) machine := by
  apply (compiledSignedIncrements up).correct
  rw [(compiledSignedIncrements up).memory_input (by cases up <;> decide +kernel)]
  refine ⟨empty_repr, by cases up <;> decide +kernel, ?_⟩
  have hc : allocationCostProg (signedIncrements up) (State.init C) = 2 := by
    cases up <;> decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by cases up <;> decide +kernel⟩

theorem signed_increments_source (up : Bool) :
    ((signedIncrements up).run (State.init C)).toOption.isSome = true := by
  cases up <;> decide +kernel

theorem signed_increments_target (up : Bool) :
    top (run ((compiledSignedIncrements up).code ++ [.mload 2]) machine) =
      some (if up then W - 5 else W - 9) := by
  cases up <;> decide +kernel

private def signedBumpInit (up : Bool) : Prog C [] [.val .int, .mem (.array (.prim .int))] :=
  if up then sol{
    int[] memory xs = new int[](1);
    int total = 57896044618658097711785492504343953926634992332820282019728792003956564819967;
    xs[0] = total;
  } else sol{
    int[] memory xs = new int[](1);
    int total = -57896044618658097711785492504343953926634992332820282019728792003956564819968;
    xs[0] = total;
  }
private def signedBumpFailure (up localTarget : Bool) :
    Prog C [] [.val .int, .mem (.array (.prim .int))] :=
  (signedBumpInit up).join (.cons (.incDec (if up then .postInc else .preDec) rfl
    (if localTarget then .local .here else .mindex .dyn (.var (.there .here) rfl) (.lit 0 rfl))) .nil)
private def compiledSignedBumpFailure (up localTarget : Bool) :
    Compiler.Compilation 1 (Frag.init []) (signedBumpFailure up localTarget) :=
  (Compiler.compile 1 (Frag.init []) (signedBumpFailure up localTarget)).get
    (by cases up <;> cases localTarget <;> decide +kernel)

/-- Both signed limits fail for both primitive locals and array elements. -/
theorem signed_bump_failure_simulates (up localTarget : Bool) :
    (compiledSignedBumpFailure up localTarget).Agrees 1 6 bases (State.init C) machine := by
  apply (compiledSignedBumpFailure up localTarget).correct
  rw [(compiledSignedBumpFailure up localTarget).memory_input (by cases up <;> cases localTarget <;> decide +kernel)]
  refine ⟨empty_repr, by cases up <;> cases localTarget <;> decide +kernel, ?_⟩
  have hc : allocationCostProg (signedBumpFailure up localTarget) (State.init C) = 2 := by
    cases up <;> cases localTarget <;> decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by cases up <;> cases localTarget <;> decide +kernel⟩

theorem signed_bump_failure_source (up localTarget : Bool) :
    sourceReverts ((signedBumpFailure up localTarget).run (State.init C)) = true := by
  cases up <;> cases localTarget <;> decide +kernel

theorem signed_bump_failure_target (up localTarget : Bool) :
    run (compiledSignedBumpFailure up localTarget).code machine = .revert := by
  cases up <;> cases localTarget <;> exact Out.eq_revert (by decide +kernel)

private def failedIncrement := (sol{
  uint[] memory xs = new uint[](1);
  ++xs[xs[1]];
  uint[] memory unreachable = new uint[](115792089237316195423570985008687907853269984665640564039457584007913129639935);
} : Prog C [] _)
private def compiledFailedIncrement : Compiler.Compilation 1 (Frag.init []) failedIncrement :=
  (Compiler.compile 1 (Frag.init []) failedIncrement).get (by decide +kernel)

/-- A failed computed index needs only the reached allocation prefix. -/
theorem failed_increment_simulates : compiledFailedIncrement.Agrees 1 6 bases (State.init C) machine := by
  apply compiledFailedIncrement.correct
  rw [compiledFailedIncrement.memory_input (by decide +kernel)]
  refine ⟨empty_repr, by decide +kernel, ?_⟩
  have hc : allocationCostProg failedIncrement (State.init C) = 2 := by decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

theorem failed_increment_source : sourceReverts (failedIncrement.run (State.init C)) = true := by
  decide +kernel

theorem failed_increment_target : run compiledFailedIncrement.code machine = .revert := by
  have h : reverted (run compiledFailedIncrement.code machine) = true := by decide +kernel
  cases he : run compiledFailedIncrement.code machine <;>
    simp only [he, reverted, Bool.false_eq_true] at h <;> rfl

private def capturedMemory (signed : Bool) :=
  if signed then (sol{
    int[] memory xs = new int[](1);
    xs[0] = -7;
    int old = xs[0]−−;
    int now = −−xs[0];
    require(old == -7 && now == -9 && xs[0] == -9);
  } : Prog C [] [.val .int, .val .int, .val .int, .val .int, .mem (.array (.prim .int))])
  else (sol{
    int[] memory xs = new int[](1);
    xs[0] = 7;
    int old = xs[0]++;
    int now = ++xs[0];
    require(old == 7 && now == 9 && xs[0] == 9);
  } : Prog C [] [.val .int, .val .int, .val .int, .val .int, .mem (.array (.prim .int))])
private def compiledCapturedMemory (signed : Bool) :
    Compiler.Compilation 1 (Frag.init []) (capturedMemory signed) :=
  (Compiler.compile 1 (Frag.init []) (capturedMemory signed)).get (by cases signed <;> decide +kernel)

/-- Surface prefix/postfix captures retain signed old values and checked new values. -/
theorem captured_memory_simulates (signed : Bool) :
    (compiledCapturedMemory signed).Agrees 1 6 bases (State.init C) machine := by
  apply (compiledCapturedMemory signed).correct
  rw [(compiledCapturedMemory signed).memory_input (by cases signed <;> decide +kernel)]
  refine ⟨empty_repr, by cases signed <;> decide +kernel, ?_⟩
  have hc : allocationCostProg (capturedMemory signed) (State.init C) = 2 := by
    cases signed <;> decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by cases signed <;> decide +kernel⟩

theorem captured_memory_source (signed : Bool) :
    ((capturedMemory signed).run (State.init C)).toOption.isSome = true := by
  cases signed <;> decide +kernel

theorem captured_memory_target (signed : Bool) :
    top (run ((compiledCapturedMemory signed).code ++ [.mload 5]) machine) =
      some (if signed then W - 9 else 9) := by
  cases signed <;> decide +kernel

private def captureSum := (sol{
  uint[] memory xs = new uint[](1);
  xs[0] = 7;
  uint total = xs[0]++ + xs[0]++;
  require(total == 15 && xs[0] == 9);
} : Prog C [] _)
private def compiledCaptureSum : Compiler.Compilation 1 (Frag.init []) captureSum :=
  (Compiler.compile 1 (Frag.init []) captureSum).get (by decide +kernel)

/-- Hoisted expression effects capture seven and eight in the source evaluation order. -/
theorem capture_sum_simulates : compiledCaptureSum.Agrees 1 6 bases (State.init C) machine := by
  apply compiledCaptureSum.correct
  rw [compiledCaptureSum.memory_input (by decide +kernel)]
  refine ⟨empty_repr, by decide +kernel, ?_⟩
  have hc : allocationCostProg captureSum (State.init C) = 2 := by decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

theorem capture_sum_source : (captureSum.run (State.init C)).toOption.isSome = true := by
  decide +kernel

theorem capture_sum_target : top (run (compiledCaptureSum.code ++ [.mload 4]) machine) = some 15 := by
  decide +kernel

private def signedCaptureFailure (up localTarget : Bool) :
    Prog C [] [.val .int, .mem (.array (.prim .int))] :=
  (signedBumpInit up).join (.cons (.assignIncDec .here (if up then .postInc else .preDec) rfl
    (if localTarget then .local .here else .mindex .dyn (.var (.there .here) rfl) (.lit 0 rfl))
    (by cases localTarget <;> rfl)) .nil)
private def compiledSignedCaptureFailure (up localTarget : Bool) :
    Compiler.Compilation 1 (Frag.init []) (signedCaptureFailure up localTarget) :=
  (Compiler.compile 1 (Frag.init []) (signedCaptureFailure up localTarget)).get
    (by cases up <;> cases localTarget <;> decide +kernel)

theorem signed_capture_failure_simulates (up localTarget : Bool) :
    (compiledSignedCaptureFailure up localTarget).Agrees 1 6 bases (State.init C) machine := by
  apply (compiledSignedCaptureFailure up localTarget).correct
  rw [(compiledSignedCaptureFailure up localTarget).memory_input
    (by cases up <;> cases localTarget <;> decide +kernel)]
  refine ⟨empty_repr, by cases up <;> cases localTarget <;> decide +kernel, ?_⟩
  have hc : allocationCostProg (signedCaptureFailure up localTarget) (State.init C) = 2 := by
    cases up <;> cases localTarget <;> decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by cases up <;> cases localTarget <;> decide +kernel⟩

theorem signed_capture_failure_source (up localTarget : Bool) :
    sourceReverts ((signedCaptureFailure up localTarget).run (State.init C)) = true := by
  cases up <;> cases localTarget <;> decide +kernel

theorem signed_capture_failure_target (up localTarget : Bool) :
    run (compiledSignedCaptureFailure up localTarget).code machine = .revert := by
  cases up <;> cases localTarget <;> exact Out.eq_revert (by decide +kernel)

private def failedCapture := (sol{
  uint[] memory xs = new uint[](1);
  uint old = xs[xs[1]]++;
  uint[] memory unreachable = new uint[](115792089237316195423570985008687907853269984665640564039457584007913129639935);
} : Prog C [] _)
private def compiledFailedCapture : Compiler.Compilation 1 (Frag.init []) failedCapture :=
  (Compiler.compile 1 (Frag.init []) failedCapture).get (by decide +kernel)

theorem failed_capture_simulates : compiledFailedCapture.Agrees 1 6 bases (State.init C) machine := by
  apply compiledFailedCapture.correct
  rw [compiledFailedCapture.memory_input (by decide +kernel)]
  refine ⟨empty_repr, by decide +kernel, ?_⟩
  have hc : allocationCostProg failedCapture (State.init C) = 2 := by decide +kernel
  rw [hc]
  exact .inr ⟨by decide, cursor, initial_repr.2, by decide +kernel⟩

theorem failed_capture_source : sourceReverts (failedCapture.run (State.init C)) = true := by
  decide +kernel

theorem failed_capture_target : run compiledFailedCapture.code machine = .revert := by
  have h : reverted (run compiledFailedCapture.code machine) = true := by decide +kernel
  cases he : run compiledFailedCapture.code machine <;>
    simp only [he, reverted, Bool.false_eq_true] at h <;> rfl

end Solidity.Evm.Memory.AllocSourceExamples
