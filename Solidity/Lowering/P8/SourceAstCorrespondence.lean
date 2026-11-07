import Solidity.Lowering.P8.SourceAstUnit

/-! Ordered, child-by-child conversion correspondence.
Regression purpose: successful containers must retain every child in order;
length equality alone cannot justify dropping/replacing statements. This is
syntax conversion correspondence, not Source meaning, origin or admission. -/
namespace Solidity.Lowering.P8.SourceAstCorrespondence
open Lean Solidity.Source
open SourceAstParameters

/-- A relational list correspondence, independent of the traversal algorithm.
It is a proposition about existing lists, not a parallel syntax representation. -/
inductive Each {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Each R [] []
  | cons {x : α} {y : β} {xs : List α} {ys : List β} :
      R x y → Each R xs ys → Each R (x :: xs) (y :: ys)

theorem Each.length_eq {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : Each R xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem Each.mapM_ok {α β ε : Type} {read : α → Except ε β}
    {xs : List α} {ys : List β} (h : Each (fun x y => read x = .ok y) xs ys) :
    xs.mapM read = .ok ys := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    rw [List.mapM_cons, head, ih]
    rfl

theorem each_of_mapM_ok {α β ε : Type} {read : α → Except ε β}
    {xs : List α} {ys : List β} (h : xs.mapM read = .ok ys) :
    Each (fun x y => read x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil =>
    change Except.ok [] = Except.ok ys at h
    cases h
    exact .nil
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : read x with
    | error message =>
      rw [hx] at h
      cases h
    | ok y =>
      rw [hx] at h
      cases ht : xs.mapM read with
      | error message =>
        rw [ht] at h
        cases h
      | ok values =>
        rw [ht] at h
        change Except.ok (y :: values) = Except.ok ys at h
        cases h
        exact .cons hx (ih ht)

theorem mapM_ok_iff_each {α β ε : Type} (read : α → Except ε β)
    (xs : List α) (ys : List β) :
    xs.mapM read = .ok ys ↔ Each (fun x y => read x = .ok y) xs ys :=
  ⟨each_of_mapM_ok, Each.mapM_ok⟩

/-- A fallible container finish cannot discard child conversion obligations. -/
theorem bind_ok_iff_each {α β γ ε : Type} (read : α → Except ε β)
    (finish : List β → Except ε γ) (xs : List α) (out : γ) :
    (do let ys ← xs.mapM read; finish ys) = .ok out ↔
      ∃ ys, Each (fun x y => read x = .ok y) xs ys ∧ finish ys = .ok out := by
  cases hm : xs.mapM read with
  | error message =>
    constructor
    · intro h; cases h
    · intro ⟨ys, hy, _⟩
      have bad := hy.mapM_ok
      rw [hm] at bad
      cases bad
  | ok values =>
    constructor
    · intro h
      exact ⟨values, each_of_mapM_ok hm, h⟩
    · intro ⟨ys, hy, result⟩
      have same := hy.mapM_ok
      rw [hm] at same
      cases same
      exact result

/-- Building a typed container after traversal does not alter child accounting. -/
theorem build_ok_iff_each {α β γ ε : Type} (read : α → Except ε β)
    (build : List β → γ) (xs : List α) (out : γ) :
    (do return build (← xs.mapM read)) = (Except.ok out : Except ε γ) ↔
      ∃ ys, Each (fun x y => read x = .ok y) xs ys ∧ out = build ys := by
  cases hm : xs.mapM read with
  | error message =>
    constructor
    · intro h
      cases h
    · intro ⟨ys, hy, _⟩
      have bad := hy.mapM_ok
      rw [hm] at bad
      cases bad
  | ok values =>
    constructor
    · intro h
      change Except.ok (build values) = Except.ok out at h
      cases h
      exact ⟨values, each_of_mapM_ok hm, rfl⟩
    · intro ⟨ys, hy, eq⟩
      have same := hy.mapM_ok
      rw [hm] at same
      cases same
      cases eq
      rfl

/-- Shared nonempty-container law for tuple and struct syntax. -/
theorem nonempty_build_ok_iff_each {α β γ ε : Type} (read : α → Except ε β)
    (build : β → List β → γ) (message : ε) (xs : List α) (out : γ) :
    (do
      let values ← xs.mapM read
      match values with
      | [] => throw message
      | head :: tail => pure (build head tail)) = (Except.ok out : Except ε γ) ↔
      ∃ head tail, Each (fun x y => read x = .ok y) xs (head :: tail) ∧ out = build head tail := by
  cases hm : xs.mapM read with
  | error error =>
    constructor
    · intro bad
      cases bad
    · intro ⟨head, tail, each, _⟩
      have bad := each.mapM_ok
      rw [hm] at bad
      cases bad
  | ok values =>
    cases values with
    | nil =>
      constructor
      · intro bad
        cases bad
      · intro ⟨head, tail, each, _⟩
        have bad := each.mapM_ok
        rw [hm] at bad
        cases bad
    | cons head tail =>
      constructor
      · intro same
        change Except.ok (build head tail) = Except.ok out at same
        cases same
        exact ⟨head, tail, each_of_mapM_ok hm, rfl⟩
      · intro ⟨other, rest, each, same⟩
        have eq := each.mapM_ok
        rw [hm] at eq
        cases eq
        cases same
        rfl

/-- Exact children and their order for the existing block reader. The node
field hypotheses expose the input container, not a Source acceptance filter. -/
theorem block_ok_iff_each (read : Json → Except String (Syn (.stmt .body)))
    (node : Json) (children : Array Json) (out : Syn (.block .body))
    (kind : node.getObjValAs? String "nodeType" = .ok "Block")
    (fields : node.getObjValAs? (Array Json) "statements" = .ok children) :
    SourceAstStatements.blockWith read node = .ok out ↔
      ∃ statements, Each (fun child stmt => read child = .ok stmt) children.toList statements ∧
        out = .block (syntaxList (statements.map Syn.stmtItem)) := by
  unfold SourceAstStatements.blockWith
  simp only [kind, fields]
  exact build_ok_iff_each read (fun statements => .block (syntaxList (statements.map Syn.stmtItem)))
    children.toList out

/-- Exact top-level syntax correspondence; this does not prove Source meaning. -/
theorem unit_ok_iff_each (fuel : Nat) (node : Json) (children : Array Json)
    (out : Syn .unit)
    (kind : node.getObjValAs? String "nodeType" = .ok "SourceUnit")
    (fields : node.getObjValAs? (Array Json) "nodes" = .ok children) :
    SourceAstUnit.unit fuel node = .ok out ↔
      ∃ tops, Each (fun child top => SourceAstUnit.top fuel child = .ok top) children.toList tops ∧
        out = .unit (syntaxList tops) := by
  unfold SourceAstUnit.unit
  simp only [kind, fields]
  exact build_ok_iff_each (SourceAstUnit.top fuel) (fun tops => .unit (syntaxList tops))
    children.toList out

/-- info: 'Solidity.Lowering.P8.SourceAstCorrespondence.Each.length_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Each.length_eq
/-- info: 'Solidity.Lowering.P8.SourceAstCorrespondence.Each.mapM_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Each.mapM_ok
/-- info: 'Solidity.Lowering.P8.SourceAstCorrespondence.each_of_mapM_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms each_of_mapM_ok
/-- info: 'Solidity.Lowering.P8.SourceAstCorrespondence.mapM_ok_iff_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapM_ok_iff_each
/-- info: 'Solidity.Lowering.P8.SourceAstCorrespondence.build_ok_iff_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms build_ok_iff_each
/-- info: 'Solidity.Lowering.P8.SourceAstCorrespondence.block_ok_iff_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms block_ok_iff_each
/-- info: 'Solidity.Lowering.P8.SourceAstCorrespondence.unit_ok_iff_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unit_ok_iff_each
/-- info: 'Solidity.Lowering.P8.SourceAstCorrespondence.nonempty_build_ok_iff_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_build_ok_iff_each
/-- info: 'Solidity.Lowering.P8.SourceAstCorrespondence.bind_ok_iff_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bind_ok_iff_each
end Solidity.Lowering.P8.SourceAstCorrespondence
