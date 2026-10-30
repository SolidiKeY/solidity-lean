import Solidity.Backend.Failure.Correct

/-! Backfill B: both nonterminal write blocks may execute; separated payload
regions retain their original immutable input bytes. Complete emitters halt,
so arbitrary concatenated suffixes cannot interfere. -/
namespace Solidity.Backend.Failure
open Slice

theorem run_two_writes (a b : Nat) (xs ys : List UInt8) (p : Program) (s : Machine)
    (hx : a + xs.length ≤ wordLimit) (hy : b + ys.length ≤ wordLimit) :
    run ((writes a xs ++ writes b ys) ++ p) s =
      run p { s with memory := putBytes (putBytes s.memory a xs) b ys } := by
  rw [List.append_assoc, run_writes a xs _ s hx, run_writes b ys _ _ hy]

theorem disjoint_payloads (m : Memory) (a b : Nat) (xs ys : List UInt8)
    (hd : a + xs.length ≤ b ∨ b + ys.length ≤ a) :
    getBytes (putBytes (putBytes m a xs) b ys) a xs.length = xs ∧
    getBytes (putBytes (putBytes m a xs) b ys) b ys.length = ys := by
  constructor
  · calc
      getBytes (putBytes (putBytes m a xs) b ys) a xs.length =
          getBytes (putBytes m a xs) a xs.length := by
        apply getBytes_congr
        intro x hx hx'
        apply putBytes_frame
        omega
      _ = xs := getBytes_putBytes m a xs
  · exact getBytes_putBytes (putBytes m a xs) b ys

/-- Every completed emitter's suffix is unobservable, including another
emitter with overlapping addresses and a different payload/class. -/
theorem concatenated_emitters (a b : Nat) (i j : Input) (s : Machine)
    (hf : Fits a i.bytes) (hs : s.stack.length + 2 ≤ 1024) :
    checkedRun (emit a i ++ emit b j) s =
      some ({ s with memory := putBytes s.memory a i.bytes }, some i.observation) :=
  checkedRun_emit_suffix a i (emit b j) s hf hs

theorem return_revert_execution_distinct (a : Nat) (bs : List UInt8) (s : Machine)
    (hf : Fits a bs) (hs : s.stack.length + 2 ≤ 1024) :
    checkedRun (emit a (.returned bs)) s ≠ checkedRun (emit a (.custom bs)) s := by
  have hr := checkedRun_emit_suffix a (.returned bs) [] s hf hs
  have hv := checkedRun_emit_suffix a (.custom bs) [] s hf hs
  simp only [List.append_nil] at hr hv
  rw [hr, hv]
  intro h
  cases h

end Solidity.Backend.Failure
