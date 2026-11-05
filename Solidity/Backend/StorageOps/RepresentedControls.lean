import Solidity.Backend.StorageOps.RepresentedOperations

/-! Inhabited PUBLIC-representation applications and real symbolic/numeric
word changes. This is an operation bridge, not a Source/bytecode simulation. -/
namespace Solidity.Backend.StorageOps.RepresentedControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def z : Fin 1 := ⟨0, by decide⟩
private def fields : List (Name × TypeGraph.Ty 1) := [("dst", .prim .bool), ("src", .prim .bool)]
private def graph : Schema 1 where
  origin := "v10-represented-operation-controls"
  declId := fun _ => 0
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "Pair"
  fields := fun _ => fields
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f hf
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact Nat.zero_lt_succ 0
private abbrev Pair := Value graph (.node z)
private def pairFields : TypeGraph.Fields graph fields := fun p => match p with
  | .here => .prim true
  | .there .here => .prim false
  | .there (.there q) => nomatch q
private def root : Pair := .node pairFields
private def after : Pair := .node (TypeGraph.Fields.set pairFields .here (.prim false))
private def dst : TypeGraph.Path graph (.node z) (.prim .bool) := .cons (.field .here) .nil
private def src : TypeGraph.Path graph (.node z) (.prim .bool) := .cons (.field (.there .here)) .nil
private def base : Solidity.Storage.Loc := .root 0
private def zero : Semantics.Word := PrimTy.toWord (p := .bool) false
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def seven : Semantics.Word := ⟨7, by decide⟩
private def store : Store := fun x => if x = .root 0 then one else if x = .root 2 then seven else zero
private def machine : WordStore := fun x => if x = 0 then one else if x = 2 then seven else zero
private def hash : Solidity.Storage.Pre → Nat := fun _ => 0
private def locations : List Solidity.Storage.Loc := [.root 0, .root 1]
private def queries : List (Query graph (.node z)) := [.word src]

private theorem supported : PathSupported dst := ⟨True.intro, True.intro⟩
private theorem apart : ∀ q ∈ queries, q.apart dst := by
  intro q member
  simp only [queries, List.mem_singleton] at member
  subst q
  exact Apart.fork (G := graph) (StepApart.field (G := graph) (i := z)
    (.here : Field fields (.prim .bool)) (.there .here : Field fields (.prim .bool)) (by decide)) .nil .nil
private theorem nonalias : ∀ q ∈ queries, q.location base ≠ pathLoc dst base := by
  intro q member
  simp only [queries, List.mem_singleton] at member
  subst q
  change Solidity.Storage.Loc.root 1 ≠ .root 0
  decide
private theorem represented : Represented root queries base store := by
  intro q member
  simp only [queries, List.mem_singleton] at member
  subst q
  refine ⟨⟨True.intro, True.intro⟩, True.intro, ?_⟩
  intro value observed
  change some zero = some value at observed
  cases observed
  rfl
private theorem run : FiniteRun 8 2 2 hash [] locations := by
  constructor
  · intro p; change 0 < 8; decide
  · decide
  · decide
  · exact Solidity.Hash.RegionsDisjoint.nil
  · intro l member
    simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member p preimage
    simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> cases preimage
private theorem transport : Transport 8 hash locations store machine := by
  intro l member
  simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

/-- Actual copy changes dst, retains src, and consumes the owner's relation. -/
theorem copy_represented : Represented after (.word dst :: queries) base
    (write store (pathLoc dst base) zero) :=
  RepresentedOperations.copyAt_scalar root after dst src false rfl rfl queries base store represented supported apart nonalias

theorem delete_represented : Represented after (.word dst :: queries) base
    (write store (pathLoc dst base) zero) :=
  RepresentedOperations.deleteAt_scalar root after dst rfl queries base store represented supported apart nonalias

theorem effect_represented : ∃ before new : PrimTy.bool.Denote,
    root.find dst = some (.prim before) ∧
    (some (.prim false) : Option (Value graph (.prim .bool))) = some (.prim new) ∧
    Represented after (.word dst :: queries) base (write store (pathLoc dst base) (PrimTy.toWord new)) :=
  RepresentedOperations.modifyAt_scalar root after dst (fun _ => some (.prim false)) rfl
    queries base store represented supported apart nonalias

private noncomputable def afterMachine := RepresentedOperations.numericCopy machine ((pathLoc dst base).word 8 hash) ((pathLoc src base).word 8 hash)

private theorem beforeBoth : Represented root (.word src :: queries) base store := by
  intro q member
  rcases List.mem_cons.mp member with equal | later
  · subst q; exact represented (.word src) List.mem_cons_self
  · exact represented q later

/-- Actual source-word read supplies the numeric copy's value; every output
query is covered and its word agreement follows, including the framed source. -/
theorem numeric_copy_certificate :
    Represented after (.word dst :: queries) base (write store (pathLoc dst base) zero) ∧
    Transport 8 hash locations (write store (pathLoc dst base) zero) afterMachine ∧
    ∀ q ∈ (.word dst :: queries), ∀ word, q.read after = some word →
      afterMachine ((q.location base).word 8 hash) = word := by
  apply RepresentedOperations.copyAt_scalar_numeric run store machine transport root after dst src false rfl rfl queries base
    beforeBoth supported apart nonalias
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_self
  · intro q member
    simp only [queries, List.mem_singleton] at member
    subst q
    exact List.mem_cons_of_mem _ List.mem_cons_self

theorem numeric_transport : Transport 8 hash locations (write store (pathLoc dst base) zero) afterMachine :=
  numeric_copy_certificate.2.1

/-- Full bounded fixture observations: before/after BOTH graph reads, both
covered words and an outside sentinel. Target changes1→0, frames retain0/7. -/
theorem ordered_words :
    (root.observe dst, root.observe src, (recursiveCopyAt root dst src).map
      (fun v => (v.observe dst, v.observe src)), machine 0, machine 1, machine 2,
      afterMachine 0, afterMachine 1, afterMachine 2) =
    (some true, some false, some (some false, some false), one, zero, seven, zero, zero, seven) := rfl

/-- Keeping the OLD numeric/symbolic word cannot represent the new graph. -/
theorem stale_word_negative : ¬ Represented after [.word dst] base store := by
  intro h
  have bad := (h (.word dst) (by exact List.mem_cons_self)).2.2 zero rfl
  change one = zero at bad
  exact (by decide : one ≠ zero) bad

theorem hash_not_injective : hash (.entry 0 0) = hash (.entry 1 7) ∧
    (Solidity.Storage.Pre.entry 0 0) ≠ .entry 1 7 := by constructor; rfl; decide

/-- info: 'Solidity.Backend.StorageOps.RepresentedControls.copy_represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_represented
/-- info: 'Solidity.Backend.StorageOps.RepresentedControls.numeric_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_transport
/-- info: 'Solidity.Backend.StorageOps.RepresentedControls.stale_word_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stale_word_negative
end Solidity.Backend.StorageOps.RepresentedControls
