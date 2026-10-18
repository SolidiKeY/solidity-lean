import Solidity.Calculus.LinearDecision

/-!
# Countermodels from the finite derivative graph

The arithmetic decision's negative answer guarantees a false zero test in
its reachable graph. This module retains a reconstruction function with
each discovered node, so that a false test gives an assignment to the
original formula directly. It does not enumerate natural assignments or
search again with an unrelated bound.
-/

namespace Solidity.Linear

namespace AFml

/-- A reachable derivative together with its assignment reconstruction.
The proof fields are erased; computation keeps the formula and function. -/
structure Node (root : AFml) where
  formula : AFml
  embed : (Nat → Nat) → (Nat → Nat)
  width : formula.width ≤ root.width
  correct : ∀ x, root.holds (embed x) ↔ formula.holds x

namespace Node

variable {root : AFml}

/-- The starting formula needs no bits put back. -/
def initial (root : AFml) : Node root := ⟨root, id, Nat.le_refl _, fun _ => Iff.rfl⟩

/-- Reading a vector of low bits extends the concrete reconstruction. -/
def child (node : Node root) (v : List Bool) (hv : v.length = root.width) : Node root where
  formula := node.formula.deriv v
  embed := fun x => node.embed (withBits v x)
  width := Nat.le_trans
    (width_of_mem_universe node.formula _
      (deriv_mem_universe v node.formula _ (self_mem_universe node.formula))) node.width
  correct := by
    intro x
    have h := holds_deriv v.length (withBits v x) node.formula (hv ▸ node.width)
    rw [lowBits_withBits, halve_withBits] at h
    exact (node.correct _).trans h

/-- Every possible bit successor, with its reconstruction retained. -/
def children (node : Node root) : List (Node root) :=
  (vecs root.width).attach.map fun v => node.child v.val (length_of_mem_vecs v.property)

theorem children_map (node : Node root) :
    node.children.map Node.formula = node.formula.succs (vecs root.width) := by
  simp only [children, List.map_map, child, AFml.succs]
  exact List.attach_map_val (f := fun v => node.formula.deriv v)

/-- Deduplicate by formula, retaining the first reconstruction discovered. -/
def addNew (seen : List AFml) : List (Node root) → List (Node root) → List (Node root)
  | acc, [] => acc
  | acc, node :: nodes =>
    if node.formula ∈ seen ∨ node.formula ∈ acc.map Node.formula then addNew seen acc nodes
    else addNew seen (node :: acc) nodes

theorem addNew_map (seen : List AFml) (acc nodes : List (Node root)) :
    (addNew seen acc nodes).map Node.formula =
      Linear.addNew seen (acc.map Node.formula) (nodes.map Node.formula) := by
  induction nodes generalizing acc with
  | nil => rfl
  | cons node nodes ih =>
    simp only [addNew, Linear.addNew, List.map_cons]
    split <;> exact ih _

/-- The same breadth-first graph exploration as the decision, retaining
each node's concrete assignment reconstruction. -/
def explore : Nat → List (Node root) → List (Node root) → Option (List (Node root))
  | 0, _, _ => none
  | _ + 1, seen, [] => some seen
  | fuel + 1, seen, node :: nodes =>
    let new := addNew (seen.map Node.formula) [] ((node :: nodes).flatMap children)
    explore fuel (new ++ seen) new

/-- Forgetting reconstructions gives exactly the graph used by the
complete arithmetic decision, with the same fuel and duplicate policy. -/
theorem explore_map (fuel : Nat) (seen frontier : List (Node root)) :
    (explore fuel seen frontier).map (List.map Node.formula) =
      Linear.explore (vecs root.width) fuel (seen.map Node.formula) (frontier.map Node.formula) := by
  induction fuel generalizing seen frontier with
  | zero => rfl
  | succ fuel ih =>
    cases frontier with
    | nil => rfl
    | cons node nodes =>
      simp only [explore, Linear.explore, List.map_cons, ih, List.map_append, addNew_map,
        List.map_nil, List.map_flatMap, children_map, List.flatMap_cons, List.flatMap_map]

end Node

/-- The traced graph also finishes at the proved arithmetic bound. -/
theorem nodes_isSome (F : AFml) :
    (Node.explore (F.count + 1) [Node.initial F] [Node.initial F]).isSome = true := by
  have h := congrArg Option.isSome
    (Node.explore_map (F.count + 1) [Node.initial F] [Node.initial F])
  simp only [Option.isSome_map, List.map_cons, List.map_nil, Node.initial] at h
  exact h.trans (exploration_isSome F)

/-- Every node used by the decision, retaining a valid reconstruction. -/
def nodes (F : AFml) : List (Node F) :=
  (Node.explore (F.count + 1) [Node.initial F] [Node.initial F]).get (nodes_isSome F)

/-- Forgetting the total traced graph returns the original successful
exploration, not a separately bounded or heuristic traversal. -/
theorem nodes_spec (F : AFml) :
    Linear.explore (vecs F.width) (F.count + 1) [F] [F] = some (F.nodes.map Node.formula) := by
  have h := Node.explore_map (F.count + 1) [Node.initial F] [Node.initial F]
  rw [Option.eq_some_iff_get_eq.mpr ⟨nodes_isSome F, rfl⟩] at h
  exact h.symm

/-- The decision checks precisely the nodes whose reconstructions are
retained by the traced exploration. -/
theorem search_nodes (F : AFml) : F.search = F.nodes.all (fun node => node.formula.atZero) := by
  simp only [AFml.search, nodes_spec, List.all_map, Function.comp_def]

/-- A negative search has an actual false node in its traced graph. -/
theorem falseNode_isSome (F : AFml) (h : F.search = false) :
    (F.nodes.find? (fun node => !node.formula.atZero)).isSome = true := by
  rw [search_nodes] at h
  rw [List.find?_isSome]
  simp only [Bool.not_eq_true', Bool.eq_false_iff]
  exact List.all_eq_false.1 h

/-- Select a false zero test from the decision's own successful graph. -/
def falseNode (F : AFml) (h : F.search = false) : Node F :=
  (F.nodes.find? (fun node => !node.formula.atZero)).get (falseNode_isSome F h)

theorem falseNode_spec (F : AFml) (h : F.search = false) : (F.falseNode h).formula.atZero = false := by
  have hp := List.find?_some (Option.some_get (falseNode_isSome F h)).symm
  simpa only [Bool.not_eq_true'] using hp

/-- A false node reconstructs a concrete assignment to the starting formula. -/
def searchCountermodel (F : AFml) (h : F.search = false) :
    { x : Nat → Nat // ¬ F.holds x } :=
  let node := F.falseNode h
  ⟨node.embed (fun _ => 0), fun hv =>
    Bool.noConfusion ((F.falseNode_spec h).symm.trans
      ((holds_zero (fun _ => 0) node.formula (fun _ _ => rfl)).1 ((node.correct _).1 hv)))⟩

/-- Every negative arithmetic decision produces a counterassignment.
Reconstruction terminates by the same proved finite graph bound as the
decision; it has no guessed assignment-size bound or small-value pool. -/
def countermodel (F : AFml) (h : F.decide = false) :
    { x : Nat → Nat // ¬ F.holds x } :=
  let cm := F.simp.searchCountermodel h
  ⟨cm.val, fun hv => cm.property ((holds_simp cm.val F).2 hv)⟩

/-- Proof or counterassignment from one traced graph traversal, with no
unsupported or exhausted branch inside the stated arithmetic language. -/
def verify (F : AFml) : Sum (PLift F.Valid) { x : Nat → Nat // ¬ F.holds x } :=
  let states := F.simp.nodes
  match h : states.find? (fun node => !node.formula.atZero) with
  | some node => .inr ⟨node.embed (fun _ => 0), by
      intro hv
      have hn : node.formula.atZero = false := by
        simpa only [Bool.not_eq_true'] using List.find?_some h
      have ht := (holds_zero (fun _ => 0) node.formula (fun _ _ => rfl)).1
        ((node.correct _).1 ((holds_simp _ F).2 hv))
      exact Bool.noConfusion (hn.symm.trans ht)⟩
  | none => .inl ⟨by
      apply (decide_iff F).1
      show F.simp.search = true
      rw [search_nodes]
      apply List.all_eq_true.2
      intro node hn
      have hx := List.find?_eq_none.1 h node hn
      cases he : node.formula.atZero with
      | true => rfl
      | false => exact (hx (by rw [he]; rfl)).elim⟩

/-- Independent direct evaluation at a reconstructed assignment. -/
def check (F : AFml) (x : Nat → Nat) : Bool :=
  match F with
  | .tt => true
  | .ff => false
  | .eq a c => Decidable.decide (a.eval x = c)
  | .le a c => Decidable.decide (a.eval x ≤ c)
  | .not F => !F.check x
  | .and F G => F.check x && G.check x
  | .imp F G => !F.check x || G.check x

theorem check_iff (F : AFml) (x : Nat → Nat) : F.check x = true ↔ F.holds x := by
  induction F with
  | tt | ff | eq | le => simp only [check, holds, decide_eq_true_eq, Bool.false_eq_true]
  | not F ih =>
    simp only [check, holds, Bool.not_eq_true', Bool.eq_false_iff]
    exact not_congr ih
  | and F G ihF ihG => simp only [check, holds, Bool.and_eq_true, ihF, ihG]
  | imp F G ihF ihG =>
    simp only [check, holds, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ihG]
    grind

/-- Direct evaluation rejects every extracted assignment. -/
theorem countermodel_check (F : AFml) (h : F.decide = false) :
    F.check (F.countermodel h).val = false :=
  Bool.eq_false_iff.2 (fun hc => (F.countermodel h).property ((check_iff _ _).1 hc))

/-- Linear forms observe only the finite prefix given by their length. -/
theorem _root_.Solidity.Linear.Lin.eval_agree (a : Lin) (x y : Nat → Nat)
    (h : ∀ i < a.length, x i = y i) : a.eval x = a.eval y := by
  induction a generalizing x y with
  | nil => rfl
  | cons a as ih =>
    rw [Lin.eval, Lin.eval, h 0 (Nat.zero_lt_succ _)]
    exact congrArg (fun z : Int => a * (y 0 : Int) + z)
      (ih (shift x) (shift y) (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)))

/-- The decision's width is exactly a sufficient finite assignment prefix. -/
theorem holds_agree (F : AFml) (x y : Nat → Nat)
    (h : ∀ i < F.width, x i = y i) : F.holds x ↔ F.holds y := by
  induction F with
  | tt | ff => exact Iff.rfl
  | eq a c => rw [holds, holds, Lin.eval_agree a x y h]
  | le a c => rw [holds, holds, Lin.eval_agree a x y h]
  | not F ih => exact not_congr (ih h)
  | and F G ihF ihG =>
    exact and_congr (ihF (fun i hi => h i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))))
      (ihG (fun i hi => h i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))))
  | imp F G ihF ihG =>
    exact imp_congr (ihF (fun i hi => h i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))))
      (ihG (fun i hi => h i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))))

/-- Store a guaranteed counterassignment as a finite list of numbers. -/
def countermodelValues (F : AFml) (h : F.decide = false) : List Nat :=
  let x := (F.countermodel h).val
  List.ofFn (fun i : Fin F.width => x i.val)

theorem countermodelValues_get (F : AFml) (h : F.decide = false) (i : Nat) (hi : i < F.width) :
    (F.countermodelValues h).getD i 0 = (F.countermodel h).val i := by
  simp only [countermodelValues, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi,
    ↓reduceDIte, Option.getD_some]

/-- Padding the finite returned list with zeros still falsifies the
original arithmetic formula; no hidden infinite assignment is required. -/
theorem countermodelValues_check (F : AFml) (h : F.decide = false) :
    F.check (fun i => (F.countermodelValues h).getD i 0) = false := by
  apply Bool.eq_false_iff.2
  intro hc
  exact (F.countermodel h).property ((F.holds_agree _ _
    (fun i hi => (F.countermodelValues_get h i hi).symm)).2 ((F.check_iff _).1 hc))

end AFml

end Solidity.Linear
