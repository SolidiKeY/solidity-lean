import Solidity.Hash.CompilerCorrect

namespace Solidity.Goals

/--
info: open Solidity.Goals.compilerCorrectCollisionFree ← Solidity.Hash.compiler_correct_collisionFree plan e4-hash-bridge
-/
#guard_msgs in
#roadmap_goal compilerCorrectCollisionFree

open HashContract Solidity.Evm

/-- Skipping a KECCAK instruction does not invent a runtime hash query. -/
example (m : Numeric) : queriesAt (.running [.keccakArr] 1 [] m) = [] := rfl

/-- The exact write event retains its numeric address and value. -/
example (m : Numeric) (a v : Fin W) :
    numericAccessAt (.running [.sstore] 0 [] { m with stack := [a, v] }) =
      [.write a v] := rfl

/-- A loop body's pending jump faults instead of escaping to its continuation. -/
example (F : Roadmap.Fixed) (m : Numeric) (c b rest : List Instr) :
    tick (numericAtom F) numericTest (.running [] 1 [.body c b rest] m) =
      .halted .fault := rfl

/-- A finished prefix cannot emit another query through terminal stuttering. -/
example (F : Roadmap.Fixed) (r : Result Numeric) :
    queriesAt (tick (numericAtom F) numericTest (.halted r)) = [] := rfl

/-- Collision freedom cannot erase the independent one-query root-hit event. -/
example :
    (Hash.tuples 2 1).countP
      (Hash.CollisionBridge.eagerPremiseFails (fun _ => (0 : Nat)) [0] 2 1 [0] 1) = 1 :=
  Hash.CollisionBridge.one_query_root_hit

open Solidity.Hash.CompilerCorrect

/-- A producer satisfying E4A cannot select a different ideal or numeric history. -/
example (E : Producer) (h : Produces E) (F : Roadmap.Fixed) (n : Nat)
    (c : List Instr) (m : Machine) (v : Numeric) :
    E.ideal n c m = producer.ideal n c m ∧
    E.numeric F n c v = producer.numeric F n c v :=
  ⟨ideal_unique E h n c m, numeric_unique E h F n c v⟩

/-- An executed hash before a revert remains in the actual producer's transcript. -/
example (F : Roadmap.Fixed) (m : Numeric) (s : Fin W) (tail : List (Fin W)) :
    queries producer F 3 [.keccakArr, .revert] { m with stack := s :: tail } =
      [encoded (.data s.val)] := rfl

/-- The limit convention has one outcome even for an unfinished infinite run. -/
example (F : Roadmap.Fixed) (c : List Instr) (m : Numeric) :
    ∃ r, Limit (fun n => producer.numeric F n c m) r ∧
      ∀ t, Limit (fun n => producer.numeric F n c m) t → t = r := by
  obtain ⟨r, hr⟩ := prefix_limit_exists (numericAtom F) numericTest (.running c 0 [] m)
  exact ⟨r, hr, fun t ht =>
    prefix_limit_unique (numericAtom F) numericTest (.running c 0 [] m) ht hr⟩

/-- Distinct word-domain preimages cannot be identified by byte conversion. -/
example (p q : Storage.Pre) (hp : p.Words) (hq : q.Words) (hne : p ≠ q) :
    encoded p ≠ encoded q := fun h => hne (encoded_inj hp hq h)

/-- The frozen run premises separate every pair in the entire reached footprint. -/
example (E : Producer) (F : Roadmap.Fixed) (n : Nat) (c : List Instr)
    (m : Machine) (v : Numeric) (observed : List Slot)
    (ready : Ready E F n c m v observed) (premise : HashContract.Premise E F n c m v observed)
    {s t : Slot} (hs : s ∈ locations E n c m observed)
    (ht : t ∈ locations E n c m observed) (he : address F s = address F t) : s = t :=
  address_injective_on F _ ready.1 ready.2.1 ready.2.2.1 premise.2 hs ht he

/-- The actual write preserves the other requested cell and the complete reached footprint. -/
example (F : Roadmap.Fixed) (m : Machine) (v : Numeric) (s t : Slot) (a : Fin W)
    (tail : List Word) (shape : m.stack = .slot s :: .val a :: tail)
    (ready : Ready producer F 1 [.sstore] m v [s, t])
    (premise : HashContract.Premise producer F 1 [.sstore] m v [s, t]) :
    ResultRelated F (locations producer 1 [.sstore] m [s, t])
      (idealResult (Instr.sstore.step m)) (numericAtom F .sstore v) :=
  sstore_related F _ ready.1 ready.2.1 ready.2.2.1 premise.2 m v ready.2.2.2
    s a tail shape (List.mem_append.mpr (Or.inl (List.mem_cons_self ..)))

/-- The actual read uses initial footprint agreement, without a storage simulation premise. -/
example (F : Roadmap.Fixed) (m : Machine) (v : Numeric) (s : Slot) (tail : List Word)
    (shape : m.stack = .slot s :: tail) (ready : Ready producer F 1 [.sload] m v [s]) :
    ResultRelated F (locations producer 1 [.sload] m [s])
      (idealResult (Instr.sload.step m)) (numericAtom F .sload v) :=
  sload_related F _ m v ready.2.2.2 s tail shape
    (List.mem_append.mpr (Or.inl (List.mem_cons_self ..)))

/-- Both actual KECCAK forms preserve representation for arbitrary symbolic parents. -/
example (F : Roadmap.Fixed) (slots : List Slot) (m : Machine) (v : Numeric)
    (rep : Represents F slots m v) (k : Fin W) (s : Slot) (tail : List Word) :
    (m.stack = .val k :: .slot s :: tail →
      ResultRelated F slots (idealResult (Instr.keccakMap.step m)) (numericAtom F .keccakMap v)) ∧
    (m.stack = .slot s :: tail →
      ResultRelated F slots (idealResult (Instr.keccakArr.step m)) (numericAtom F .keccakArr v)) :=
  ⟨keccakMap_related F slots m v rep k s tail, keccakArr_related F slots m v rep s tail⟩

/-- Both legal slot-offset operand orders use modular address arithmetic. -/
example (F : Roadmap.Fixed) (slots : List Slot) (m : Machine) (v : Numeric)
    (rep : Represents F slots m v) (s : Slot) (i : Fin W) (tail : List Word)
    (shape : m.stack = .val i :: .slot s :: tail ∨ m.stack = .slot s :: .val i :: tail) :
    ResultRelated F slots (idealResult (Instr.add.step m)) (numericAtom F .add v) :=
  add_slot_related F slots m v rep s i tail shape

/-- A full word-period offset wraps even for a nested symbolic slot. -/
example (F : Roadmap.Fixed) (s : Slot) : address F (s.add W) = address F s := by
  rw [address_add]
  apply Fin.ext
  simp only [wmod, Nat.add_mod, Nat.mod_self, Nat.add_zero,
    Nat.mod_eq_of_lt (address F s).isLt]

/-- The access list records the write value as well as its interpreted address. -/
example (F : Roadmap.Fixed) (slots : List Slot) (m : Machine) (v : Numeric)
    (rep : Represents F slots m v) (s : Slot) (a : Fin W) (tail : List Word)
    (shape : m.stack = .slot s :: .val a :: tail) :
    (idealAccessAt (.running [.sstore] 0 [] m)).map (mapAccess (address F)) =
      numericAccessAt (.running [.sstore] 0 [] v) :=
  sstore_access_agrees F slots m v rep s a tail shape [] []

/-- Reads are retained as events even though they do not change the store. -/
example (F : Roadmap.Fixed) (slots : List Slot) (m : Machine) (v : Numeric)
    (rep : Represents F slots m v) (s : Slot) (tail : List Word)
    (shape : m.stack = .slot s :: tail) :
    (idealAccessAt (.running [.sload] 0 [] m)).map (mapAccess (address F)) =
      numericAccessAt (.running [.sload] 0 [] v) :=
  sload_access_agrees F slots m v rep s tail shape [] []

/-- An actual empty-stack SSTORE prefix faults in both machines. -/
example (F : Roadmap.Fixed) (slots : List Slot) (m : Machine) (v : Numeric)
    (rep : Represents F slots m v) (shape : m.stack = []) :
    ResultRelated F slots (idealResult (Instr.sstore.step m)) (numericAtom F .sstore v) :=
  empty_stack_fault_related F slots m v rep shape .sstore (by simp)

end Solidity.Goals
