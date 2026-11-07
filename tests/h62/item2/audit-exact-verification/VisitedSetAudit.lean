import Solidity.Calculus.VisitedSet

/-!
Additive witnesses for the frozen visited-set interface. These certify concrete
joint input bundles. They do not certify any other module or the full census.
The nonempty closed walk processes a real node; the refuted control rejects one.
-/
namespace Solidity.H62.ExactAudit.VisitedSet

open Solidity.Linear

/-- Shared inhabited element/state/node/cache type: Nat; an actual stored node. -/
def seen : HSet Nat := .node .leaf 0 [0] .leaf

/-- All inputs of HSet.mem_toList at one nonempty tree. -/
theorem mem_toList_inputs : ∃ (a : Nat) (t : HSet Nat), t.Mem a :=
  ⟨0, seen, .inr (.inl (.head []))⟩

/-- The complete success hypothesis of HSet.find?_some. -/
theorem find_some_inputs : ∃ (k a : Nat) (p : Nat → Bool) (t : HSet Nat),
    t.find? k p = some a := ⟨0, 0, fun _ => true, seen, rfl⟩

/-- The complete success hypothesis of HSet.mem_of_contains. -/
theorem contains_inputs : ∃ (k a : Nat) (t : HSet Nat), t.contains k a = true :=
  ⟨0, 0, seen, rfl⟩

/-- A simultaneous nonempty insertion/membership input for HSet.mem_insert. -/
theorem insert_inputs : ∃ (k a x : Nat) (t : HSet Nat), (t.insert k a).Mem x :=
  ⟨0, 0, 0, seen, .inr (.inl (.head [0]))⟩

/-- pushNew_spec has no additional logical premise: all functions and lists
are instantiated together and a fresh state is actually queued. -/
theorem push_inputs : ∃ (st : Nat → Nat) (hash : Nat → Nat)
    (cs : List Nat) (V : HSet Nat) (W : List Nat),
    (pushNew st hash cs V W).2 = [0] :=
  ⟨id, fun _ => 0, [0], .leaf, [], rfl⟩

/-- walkInv_initial: the same node witnesses the functions and input. -/
theorem initial_inputs : ∃ (st : Nat → Nat) (hash : Nat → Nat)
    (kids : Nat → List Nat) (ok : Nat → Bool) (n : Nat),
    WalkInv st kids ok (HSet.leaf.insert (hash (st n)) (st n)) [n] :=
  ⟨id, fun _ => 0, fun _ => [], fun _ => true, 0,
    walkInv_initial id (fun _ => 0) (fun _ => []) (fun _ => true) 0⟩

/-- walk_closed: its result equation and invariant hold at the same nonempty
worklist, state tree and fuel; no separate-assumption shortcut is used. -/
theorem closed_inputs : ∃ (st : Nat → Nat) (hash : Nat → Nat)
    (kids : Nat → List Nat) (ok : Nat → Bool) (fuel : Nat)
    (V V' : HSet Nat) (W : List Nat),
    walk st hash kids ok fuel V W = .closed V' ∧ WalkInv st kids ok V W := by
  refine ⟨id, fun _ => 0, fun _ => [], fun _ => true, 2, seen, seen, [0], rfl, ?_⟩
  exact walkInv_initial id (fun _ => 0) (fun _ => []) (fun _ => true) 0

/-- walk_refuted: an observed refusal, with all frozen input functions fixed. -/
theorem refuted_inputs : ∃ (st : Nat → Nat) (hash : Nat → Nat)
    (kids : Nat → List Nat) (ok : Nat → Bool) (fuel : Nat)
    (V : HSet Nat) (W : List Nat) (r : Nat),
    walk st hash kids ok fuel V W = .refuted r :=
  ⟨id, fun _ => 0, fun _ => [], fun _ => false, 1, seen, [0], 0, rfl⟩

/-- walkC_eq: one inhabited global cache contract AND its feasible input.
Good restricts the cache to zero, and okC preserves that same cache. -/
theorem cache_inputs : ∃ (st : Nat → Nat) (hash : Nat → Nat)
    (kids : Nat → List Nat) (ok : Nat → Bool) (okC : Nat → Nat → Bool × Nat)
    (Good : Nat → Prop) (fuel c : Nat) (V : HSet Nat) (W : List Nat),
    (∀ c n, Good c → (okC c n).1 = ok n ∧ Good (okC c n).2) ∧ Good c ∧
    walkC st hash kids okC fuel c V W = walk st hash kids ok fuel V W := by
  refine ⟨id, fun _ => 0, fun _ => [], fun _ => true, fun c _ => (true, c),
    fun c => c = 0, 2, 0, seen, [0], (fun _ _ h => ⟨rfl, h⟩), rfl, ?_⟩
  exact walkC_eq id (fun _ => 0) (fun _ => []) (fun _ => true)
    (fun c _ => (true, c)) (fun c => c = 0) (fun _ _ h => ⟨rfl, h⟩) 2 0 seen [0] rfl

/-- Positive totality control: an accepted node with no children closes with
fuel two, and its stored state remains observable. -/
theorem supported_node_closes :
    walk id (fun _ : Nat => 0) (fun _ => []) (fun _ => true) 2 seen [0] = .closed seen := rfl

/-- A reject-all checker cannot satisfy that same success observation. -/
theorem reject_all_does_not_close :
    walk id (fun _ : Nat => 0) (fun _ => []) (fun _ => false) 2 seen [0] ≠ .closed seen := by
  intro h
  cases h

/-- Fuel zero is observably out, even for an otherwise supported node. -/
theorem zero_fuel_is_out :
    walk id (fun _ : Nat => 0) (fun _ => []) (fun _ => true) 0 seen [0] = .out := rfl

-- Frozen declarations are printed directly from the unchanged imported interface.
#check @HSet.mem_toList
#check @HSet.find?_some
#check @HSet.mem_of_contains
#check @HSet.mem_insert
#check @pushNew_spec
#check @walkInv_initial
#check @walk_closed
#check @walk_refuted
#check @walkC_eq

#print axioms mem_toList_inputs
#print axioms find_some_inputs
#print axioms contains_inputs
#print axioms insert_inputs
#print axioms push_inputs
#print axioms initial_inputs
#print axioms refuted_inputs
#print axioms closed_inputs
#print axioms cache_inputs
#print axioms supported_node_closes
#print axioms reject_all_does_not_close
#print axioms zero_fuel_is_out

end Solidity.H62.ExactAudit.VisitedSet
