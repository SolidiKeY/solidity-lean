import Solidity.Backend.CalldataPackets.RawUint.Execution

/-! Raw byte-derived uintN copies for every valid ABI unsigned width below 256.
The existing Source operation decodes before allocation; dirty words revert,
never mask high bits. No decoded payload or successful execution is assumed. -/
namespace Solidity.Backend.CalldataPackets.RawUintN
open Solidity.Backend.MemoryOps

structure Width where
  bits : Nat
  aligned : bits % 8 = 0
  lower : 8 ≤ bits
  narrow : bits < 256

def Width.intTy (n : Width) : Source.IntTy :=
  ⟨false, n.bits, n.aligned, n.lower, Nat.le_of_lt n.narrow⟩
abbrev ArrayTy (n : Width) : Source.STy := .array .memory (.int n.intTy) none

/-- The value is constructed only after the exact unsigned range test. -/
def element (D : Source.Layout) (n : Width) (w : Nat) :
    Source.R (Source.Val D (.int n.intTy)) :=
  if h : n.intTy.lo ≤ (w : Int) ∧ (w : Int) ≤ n.intTy.hi then
    .ok (.int w h)
  else .error (.revert [])

theorem range_iff (n : Width) (w : Nat) :
    (n.intTy.lo ≤ (w : Int) ∧ (w : Int) ≤ n.intTy.hi) ↔ w < 2^n.bits := by
  first
  | (simp only [Width.intTy, Source.IntTy.lo, Source.IntTy.hi]; omega)
  | have positive : 0 < 2^n.bits := Nat.pow_pos (by decide)
    change (0 ≤ (w : Int) ∧ (w : Int) ≤ ((2^n.bits-1 : Nat) : Int)) ↔ _
    omega

theorem decode_raw (D : Source.Layout) (n : Width) (F : Source.Fr) (off : Nat) :
    Source.decodeWord D (Source.cdWordAt F off) (.int n.intTy) =
      element D n (Source.cdWordAt F off) := by
  have exactWord : (Source.toWord (Source.cdWordAt F off)).val = Source.cdWordAt F off :=
    Nat.mod_eq_of_lt (RawUint.raw_word_bound F off)
  change (match Source.readInt n.intTy (Source.toWord (Source.cdWordAt F off)) with
    | some v => Source.mkInt n.intTy v
    | none => .error (.revert [])) = _
  have wordInt : Source.wordInt n.intTy (Source.toWord (Source.cdWordAt F off)) =
      (Source.cdWordAt F off : Int) := by
    simp only [Source.wordInt, Width.intTy, Bool.false_eq_true, false_and, if_false, exactWord]
  rw [Source.readInt, wordInt]
  by_cases h : n.intTy.lo ≤ (Source.cdWordAt F off : Int) ∧
      (Source.cdWordAt F off : Int) ≤ n.intTy.hi
  · simp only [Source.mkInt, element, if_pos h, dif_pos h]
    rfl
  · rw [if_neg h, element, dif_neg h]

def values (D : Source.Layout) (n : Width) (F : Source.Fr) (off len : Nat) :
    Source.R (List (Source.Val D (.int n.intTy))) :=
  (List.range len).mapM fun j => element D n (Source.cdWordAt F (off+32*j))

def memory (D : Source.Layout) (n : Width)
    (xs : List (Source.Val D (.int n.intTy))) : Source.Data D (ArrayTy n) :=
  .array xs.length (fun _ h => nomatch h) (fun k => .val (xs.get k))

/-- Exact complete result, including all failure states, at every runtime length. -/
theorem copy_run {E : Source.Env} {Γ : Source.RCtx}
    (n : Width) (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F (ArrayTy n) off len).run y =
      match values E.layout n F off len with
      | .error e => (.error e,y)
      | .ok xs => (.ok (.val (.memRef rfl y.2.heap.next)),
          (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy n,memory E.layout n xs⟩).1})) := by
  simp only [Source.cdToMem,ArrayTy,Source.STy.loc?,Option.some.injEq,reduceCtorEq,dite_false]
  rw [Source.Hoare.run_bind,source_mapM_lift_run]
  have same : (List.range len).mapM (fun j =>
      Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) (.int n.intTy)) =
      values E.layout n F off len := by
    simp only [values, decode_raw]
  rw [same]
  cases values E.layout n F off len <;> rfl

private theorem dirty_indices (D : Source.Layout) (n : Width) (F : Source.Fr)
    (off : Nat) (indices : List Nat) (j : Nat) (member : j ∈ indices)
    (dirty : 2^n.bits ≤ Source.cdWordAt F (off+32*j)) :
    indices.mapM (fun k => element D n (Source.cdWordAt F (off+32*k))) =
      .error (.revert []) := by
  induction indices with
  | nil => cases member
  | cons k ks ih =>
    rw [List.mapM_cons]
    by_cases clean : n.intTy.lo ≤ (Source.cdWordAt F (off+32*k) : Int) ∧
        (Source.cdWordAt F (off+32*k) : Int) ≤ n.intTy.hi
    · have tail : j ∈ ks := by
        rcases List.mem_cons.mp member with same | rest
        · subst k
          have := (range_iff n _).mp clean
          omega
        · exact rest
      rw [element, dif_pos clean]
      simp only [bind, Except.bind]
      rw [ih tail]
    · simp only [element, dif_neg clean, bind, Except.bind]

/-- A dirty word anywhere in the requested span refuses with no allocation,
preserving the whole initial state, not only the heap or its old prefix. -/
theorem dirty_copy {E : Source.Env} {Γ : Source.RCtx}
    (n : Width) (F : Source.Fr) (off len j : Nat) (within : j < len)
    (dirty : 2^n.bits ≤ Source.cdWordAt F (off+32*j)) (y : Source.EMState E Γ) :
    (Source.cdToMem F (ArrayTy n) off len).run y = (.error (.revert []),y) := by
  rw [copy_run]
  have bad := dirty_indices E.layout n F off (List.range len) j (List.mem_range.mpr within) dirty
  change (List.range len).mapM _ = _ at bad
  rw [show values E.layout n F off len = .error (.revert []) from bad]

private theorem clean_indices (D : Source.Layout) (n : Width) (F : Source.Fr)
    (off : Nat) (indices : List Nat)
    (clean : ∀ j ∈ indices, Source.cdWordAt F (off+32*j) < 2^n.bits) :
    ∃ xs, indices.mapM (fun j => element D n (Source.cdWordAt F (off+32*j))) = .ok xs := by
  induction indices with
  | nil => exact ⟨[],rfl⟩
  | cons j js ih =>
    obtain ⟨xs, tail⟩ := ih (fun k member => clean k (List.mem_cons_of_mem _ member))
    have head := (range_iff n _).mpr (clean j (List.mem_cons_self))
    refine ⟨.int (Source.cdWordAt F (off+32*j)) head :: xs, ?_⟩
    rw [List.mapM_cons, element, dif_pos head]
    simp only [bind, Except.bind]
    rw [tail]
    rfl

/-- Exact admission classification: success iff EVERY requested raw word fits.
The payload and successful state are computed by Source, not input premises. -/
theorem copy_success_iff {E : Source.Env} {Γ : Source.RCtx}
    (n : Width) (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    (∃ v z, (Source.cdToMem F (ArrayTy n) off len).run y = (.ok v,z)) ↔
      ∀ j, j < len → Source.cdWordAt F (off+32*j) < 2^n.bits := by
  constructor
  · rintro ⟨v,z,success⟩ j within
    by_cases clean : Source.cdWordAt F (off+32*j) < 2^n.bits
    · exact clean
    · have failure := dirty_copy n F off len j within (Nat.le_of_not_gt clean) y
      rw [failure] at success
      cases success
  · intro clean
    obtain ⟨xs,valid⟩ := clean_indices E.layout n F off (List.range len)
      (fun j member => clean j (List.mem_range.mp member))
    refine ⟨.val (.memRef rfl y.2.heap.next),
      (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy n,memory E.layout n xs⟩).1}), ?_⟩
    rw [copy_run, show values E.layout n F off len = .ok xs from valid]

/-- Success and refusal both preserve locals and every non-heap state field. -/
theorem copy_state {E : Source.Env} {Γ : Source.RCtx}
    (n : Width) (F : Source.Fr) (off len : Nat) (y : Source.EMState E Γ) :
    let z := (Source.cdToMem F (ArrayTy n) off len).run y |>.2
    z.1 = y.1 ∧ {z.2 with heap := y.2.heap} = y.2 ∧
      (∀ a, a ≠ y.2.heap.next → z.2.heap.get a = y.2.heap.get a) := by
  rw [copy_run]
  cases values E.layout n F off len with
  | error e =>
    dsimp only
    refine ⟨rfl, ?_, fun _ _ => rfl⟩
    cases y.2
    rfl
  | ok xs =>
    dsimp only
    refine ⟨rfl, ?_, ?_⟩
    · cases y.2
      rfl
    · intro a different
      exact Source.Heap.alloc_other _ _ different

/-- Entry validation is the unchanged Source guard, before any element decode. -/
theorem guarded_run {E : Source.Env} {Γ : Source.RCtx}
    (n : Width) (data : List UInt8) (i : Nat) (F : Source.Fr) (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p =>
      Source.cdToMem F (ArrayTy n) p.1 p.2).run y =
      match Source.cdTail data i 32 with
      | .error e => (.error e,y)
      | .ok (off,len) => (Source.cdToMem F (ArrayTy n) off len).run y := by
  rw [Source.Hoare.run_bind]
  cases Source.cdTail data i 32 <;> rfl

theorem implicit_copy (n : Width) (isBase : Source.DeclName → Source.DeclName → Bool) (mapFree : Source.DeclName → Bool) :
    Source.STy.implicit isBase mapFree (.array .calldata (.int n.intTy) none) (ArrayTy n) = true := by
  change ((Source.STy.int n.intTy).same (.int n.intTy) && true && true && _) = true
  rw [Source.STy.same_refl]
  rfl

/-- The actual resolved implicit conversion, not a supplied successful run. -/
def copyExpr {E : Source.Env} {Γ : Source.RCtx} (n : Width)
    (i : Source.Idx Γ (.array .calldata (.int n.intTy) none)) : Source.RExpr E Γ (ArrayTy n) :=
  .conv (.local i) (.inl (implicit_copy n E.isBase E.mapFree))

theorem eval_copy {E : Source.Env} {Γ : Source.RCtx}
    (n : Width) (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (i : Source.Idx Γ (.array .calldata (.int n.intTy) none)) (off len : Nat)
    (localRef : y.1.get i = .cdRef rfl off len) :
    (Source.evalE G F (fuel+2) (copyExpr n i)).run y =
      (Source.cdToMem F (ArrayTy n) off len).run y := by
  rw [copyExpr, Source.evalE, Source.Hoare.run_bind,
    source_local_value_run G F fuel y i _ localRef]
  change (Source.convRV F (fuel+1) (ArrayTy n)
    (.val (.cdRef rfl off len) : Source.RVal E.layout (.array .calldata (.int n.intTy) none))).run y = _
  unfold Source.convRV
  rw [dif_neg (show (Source.STy.array .calldata (.int n.intTy) none) ≠ ArrayTy n from by intro h; cases h)]
  rfl

theorem empty_copy {E : Source.Env} {Γ : Source.RCtx}
    (n : Width) (F : Source.Fr) (off : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F (ArrayTy n) off 0).run y =
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy n,memory E.layout n []⟩).1})) := by
  rw [copy_run]
  rfl

/-- info: 'Solidity.Backend.CalldataPackets.RawUintN.copy_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_success_iff
/-- info: 'Solidity.Backend.CalldataPackets.RawUintN.decode_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_raw
/-- info: 'Solidity.Backend.CalldataPackets.RawUintN.copy_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_run
/-- info: 'Solidity.Backend.CalldataPackets.RawUintN.dirty_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawUintN.copy_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_state
/-- info: 'Solidity.Backend.CalldataPackets.RawUintN.guarded_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms guarded_run
/-- info: 'Solidity.Backend.CalldataPackets.RawUintN.eval_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_copy
end Solidity.Backend.CalldataPackets.RawUintN
