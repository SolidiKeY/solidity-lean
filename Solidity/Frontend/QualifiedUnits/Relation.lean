import Solidity.Source.Units

/-!
# Independent qualified declaration paths

The specification uses the existing source syntax and identities. Imports
are the existing least-fixpoint `Sees` relation. A declaration can be a
namespace only when its actual node is a contract, interface, or library;
its children retain their positions in the original unit declaration graph.
This static relation does not assign types or evaluate expressions.
-/
namespace Solidity.Frontend.QualifiedUnits
open Solidity.Source

/-- The declaration kinds that introduce declaration namespaces. -/
def Container (k : DeclKind) : Prop :=
  k = .contract ∨ k = .interface ∨ k = .library

instance instDecidableContainer (k : DeclKind) : Decidable (Container k) := by
  unfold Container
  infer_instance

/-- Number of direct graph nodes following a container in source order.
The count comes from that owner's actual intrinsic body. -/
def memberCount (d : Decl) : Nat :=
  match d.kind, d.top, d.node with
  | .contract, _, .contract _ n _ _ body => (body.collect (some n)).length
  | .interface, _, .interface n _ body => (body.collect (some n)).length
  | .library, _, .library n body => (body.collect (some n)).length
  | _, _, _ => 0

/-- A named declaration directly inside the identified declaration's scope.
Both identities are checked against the original unit, never against a
flattened or renamed copy. Struct fields and enum values are not graph
nodes (`Syn.collect`); this relation resolves declarations only. -/
inductive Member (P : UnitSet) : DeclId → String → DeclId → Prop where
  | intro {owner child : DeclId} {d e : Decl} {x : String} :
      P.decl? owner = some d → Container d.kind →
      P.decl? child = some e → child.unit = owner.unit →
      e.scope = some d.name → e.name = x → x ≠ "" →
      owner.idx < child.idx → child.idx ≤ owner.idx + memberCount d →
      Member P owner x child

/-- One namespace component, independently of any executable lookup. -/
inductive Step (P : UnitSet) (R : List Remapping) : Sym → String → Sym → Prop where
  | unit {u x : String} {s : Sym} : Sees P R u x s → Step P R (.unit u) x s
  | decl {i j : DeclId} {x : String} : Member P i x j → Step P R (.decl i) x (.decl j)

/-- A finite suffix through namespace symbols. Import cycles occur inside
`Sees`; the number of qualified components is arbitrary and finite. -/
inductive Through (P : UnitSet) (R : List Remapping) : Sym → List String → Sym → Prop where
  | done (s : Sym) : Through P R s [] s
  | next {a b c : Sym} {x : String} {xs : List String} :
      Step P R a x b → Through P R b xs c → Through P R a (x :: xs) c

/-- Resolution of an existing nonempty source identifier path. -/
def Qualified (P : UnitSet) (R : List Remapping) (u : String) (p : IdPath) (s : Sym) : Prop :=
  ∃ first, Sees P R u p.head first ∧ Through P R first p.tail s

/-- Path composition does not change declaration identities. -/
theorem Through.append {P : UnitSet} {R : List Remapping} {a b c : Sym}
    {xs ys : List String} (h : Through P R a xs b) (k : Through P R b ys c) :
    Through P R a (xs ++ ys) c := by
  induction h with
  | done => exact k
  | next hs _ ih => exact .next hs (ih k)

/-- A declaration reached through a nonempty path is an actual graph node. -/
theorem Step.decl_exists {P : UnitSet} {R : List Remapping} {a : Sym}
    {x : String} {i : DeclId} (h : Step P R a x (.decl i)) :
    ∃ d, P.decl? i = some d := by
  cases h with
  | unit hs =>
    generalize e : Sym.decl i = s at hs
    induction hs with
    | @own u x s j d hu hd _ _ _ =>
      cases e
      refine ⟨d, ?_⟩
      simp only [UnitSet.decl?, hu, Option.bind_some]
      exact hd
    | ns _ _ => cases e
    | all _ _ _ ih => exact ih e
    | sym _ _ _ ih => exact ih e
  | decl hm => cases hm with
    | intro _ _ hd _ _ _ _ _ _ => exact ⟨_, hd⟩

end Solidity.Frontend.QualifiedUnits
