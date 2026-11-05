import Solidity.Backend.PrimitivePackets.UnsignedDiv.Composition

/-! An inhabited initial representation for arbitrary unsigned operand locals
and arbitrary saved physical stack. This is an auxiliary machine constructor,
not a deployment, source-layout or native fixture claim. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedDiv

open Evm Evm.Memory

def localState (C : Contract) (a d : Uint) : State C (modelContext []) :=
  ((State.init C).push (t := .val .uint) d).push (t := .val .uint) a

def localWord (v : Uint) : Fin W := ⟨v.val.toNat, by
  have h : 0 ≤ v.val ∧ v.val < ((2 ^ 256 : Nat) : Int) := Scalar.uint_range v
  change v.val.toNat < 2 ^ 256
  omega⟩

private theorem local_word_repr (v : Uint) : ReprV .uint v (.val (localWord v)) := by
  apply ReprV.uint_of
  have h : 0 ≤ v.val ∧ v.val < ((2 ^ 256 : Nat) : Int) := Scalar.uint_range v
  change v.val = (v.val.toNat : Int)
  omega

def localMachine (a d : Uint) (saved : List Word) : Machine :=
  { Machine.init with stack := saved, mem := fun i =>
      if i = 2 then .val (localWord a)
      else if i = 1 then .val (localWord d) else w[0] }

def localBases : Nat → Fin W := fun _ => ⟨0, W_pos⟩

theorem local_repr (C : Contract) (a d : Uint) (saved : List Word) :
    StateRepr 1 1 4 (Frag.init (modelContext [])) (localState C a d)
      localBases (localMachine a d saved) := by
  have hn {R : RefTy} (r : HRef [] R) : False := by
    simpa only [List.getElem?_nil, reduceCtorEq] using r.get?
  refine ⟨?_, ?_, ?_, by decide,
    ⟨fun r => (hn r).elim, fun r => (hn r).elim, fun r => (hn r).elim⟩,
    (fun _ r => (hn r).elim), RefFieldsRepr.withoutStructs _ _ _ (fun r => hn r)⟩
  · refine ⟨initStorage_repr C Nat.one_pos, ?_, ?_, ?_, rfl,
      by unfold Lmax; decide, ?_, ⟨rfl, rfl, rfl, rfl⟩, rfl,
      fun _ _ _ _ _ _ => rfl⟩
    · intro p i
      cases i with
      | here => exact local_word_repr _
      | there i =>
        cases i with
        | here => exact local_word_repr _
        | there i => nomatch i
    · intro R i hi
      cases i with
      | there i => cases i with | there i => nomatch i
    · intro addr _
      rfl
    · intro R i hi
      cases i with
      | there i => cases i with | there i => nomatch i
  · exact ⟨fun r => (hn r).elim, fun r => (hn r).elim, fun r _ _ => (hn r).elim⟩
  · intro p i
    cases i with
    | there i => cases i with | there i => nomatch i

/-- A nonzero client discharges the complete initial-machine representation;
its saved tail need not be empty and no execution is assumed. -/
theorem witnessed_division (C : Contract) (a d : Uint) (saved : List Word)
    (G : Source.Glob E) (fr : Source.Fr) (n : Nat)
    (tail : Source.Locals E.layout Δ) (s : Source.St E) (hd : d.val ≠ 0) :
    ∃ v : Uint, ∃ w, v.val = a.val.tdiv d.val ∧
      (Source.evalE G fr (n + 3) (sourceDiv E Δ)).run (sourceLocals a d tail, s) =
        (.ok (.val (sourceUInt E.layout v)), (sourceLocals a d tail, s)) ∧
      ReprV .uint v w ∧
      run (selectedDiv (C := C) 1 (Frag.init (modelContext []))).code
        (localMachine a d saved) = .ok ((localMachine a d saved).push w) 0 := by
  exact (division_packet (local_repr C a d saved) G fr n tail s hd).2

theorem witnessed_remainder (C : Contract) (a d : Uint) (saved : List Word)
    (G : Source.Glob E) (fr : Source.Fr) (n : Nat)
    (tail : Source.Locals E.layout Δ) (s : Source.St E) (hd : d.val ≠ 0) :
    ∃ v : Uint, ∃ w, v.val = a.val.tmod d.val ∧
      (Source.evalE G fr (n + 3) (sourceMod E Δ)).run (sourceLocals a d tail, s) =
        (.ok (.val (sourceUInt E.layout v)), (sourceLocals a d tail, s)) ∧
      ReprV .uint v w ∧
      run (selectedMod (C := C) 1 (Frag.init (modelContext []))).code
        (localMachine a d saved) = .ok ((localMachine a d saved).push w) 0 := by
  exact (remainder_packet (local_repr C a d saved) G fr n tail s hd).2

/-- Zero refusal has an actual initial representation too; it is not a
successful execution witness or a target panic-payload theorem. -/
theorem witnessed_zero_division (C : Contract) (a d : Uint) (saved : List Word)
    (G : Source.Glob E) (fr : Source.Fr) (n : Nat)
    (tail : Source.Locals E.layout Δ) (s : Source.St E) (hd : d.val = 0) :
    (Source.evalE G fr (n + 3) (sourceDiv E Δ)).run (sourceLocals a d tail, s) =
      (.error (.revert (Source.panicData .divZero)), (sourceLocals a d tail, s)) ∧
    Memory.compileVal 1 (Frag.init (modelContext [])) (modelDiv C []) =
      some (selectedDiv 1 (Frag.init (modelContext []))) ∧
    run (selectedDiv (C := C) 1 (Frag.init (modelContext []))).code
      (localMachine a d saved) = .revert := by
  exact division_zero_packet (local_repr C a d saved) G fr n tail s hd

end Solidity.Backend.PrimitivePackets.UnsignedDiv
