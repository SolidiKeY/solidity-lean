import Solidity.Frontend.C3Exactness.Identity
import Solidity.Frontend.C3Exactness.OrderObstruction

/-!
# Inhabited exact-graph, identity, obstruction and constructor-sequence controls

These are intrinsic S00 units with empty bodies. Kernel checks concern the
existing C3/sequence producer and independent derivations, not execution of
constructor bodies. Compiler fixtures cross-check these same inheritance shapes.
-/
namespace Solidity.Frontend.C3Exactness
open Solidity.Source

/-- Intrinsic inheritance specifiers for the graph-control units. -/
def graphSpecs (bs : List String) : Syn (.list .inherit) :=
  bs.foldr (fun b acc => .cons (.inherit ⟨b, []⟩ .none) acc) .nil

/-- Intrinsic source-unit constructor; every position is an actual contract declaration. -/
def graphUnit (specs : List (String × List String)) : Syn .unit :=
  .unit (specs.foldr (fun spec acc =>
    .cons (.contract false spec.1 .none (graphSpecs spec.2) .nil) acc) .nil)

def graphDiamond : Syn .unit := graphUnit
  [("A", []), ("B", ["A"]), ("C", ["A"]), ("D", ["B", "C"])]

theorem graphDiamond_admitted : graphDiamond.env.basesOK = true := rfl

theorem graphDiamond_public :
    graphDiamond.env.linearize "D" = some ["D", "C", "B", "A"] := rfl

theorem graphDiamond_exact : ExactLin graphDiamond.env "D" ["D", "C", "B", "A"] :=
  (linearize_exact_iff graphDiamond_admitted _ _).mp graphDiamond_public

theorem graphDiamond_constructors : graphDiamond.env.ctorOrder "D" = ["A", "B", "C", "D"] := rfl

theorem graphDiamond_identities : IdentityLin graphDiamond.env 3 [3, 2, 1, 0] :=
  (linearize_identity_iff graphDiamond_admitted "D" (by decide) _).mp (by decide)

theorem graphDiamond_graph_nodes : ∀ j ∈ ([3, 2, 1, 0] : List Nat),
    ∃ d, (j, d) ∈ graphDiamond.graph :=
  IdentityLin.graph_nodes (u := graphDiamond) graphDiamond_identities graphDiamond_admitted

theorem graphDiamond_identity_order_refused : ¬ IdentityLin graphDiamond.env 3 [3, 1, 2, 0] := by
  intro ht
  have he := graphDiamond_identities.unique ht graphDiamond_admitted
  exact (by decide : ([3, 2, 1, 0] : List Nat) ≠ [3, 1, 2, 0]) he

/-- Two diamonds sharing multiple complete ancestor sequences. -/
def graphShared : Syn .unit := graphUnit
  [("A", []), ("B", ["A"]), ("C", ["A"]), ("D", ["B", "C"]),
    ("E", ["B", "C"]), ("F", ["D", "E"])]

theorem graphShared_admitted : graphShared.env.basesOK = true := rfl

theorem graphShared_public :
    graphShared.env.linearize "F" = some ["F", "E", "D", "C", "B", "A"] := rfl

theorem graphShared_exact : ExactLin graphShared.env "F" ["F", "E", "D", "C", "B", "A"] :=
  (linearize_exact_iff graphShared_admitted _ _).mp graphShared_public

theorem graphShared_constructor_nodup : (graphShared.env.ctorOrder "F").Nodup :=
  ctor_nodup graphShared_admitted graphShared_public

theorem graphShared_constructors :
    graphShared.env.ctorOrder "F" = ["A", "B", "C", "D", "E", "F"] := rfl

/-- An ancestor may be both a direct and an indirect base without being repeated in output. -/
def graphRedundant : Syn .unit := graphUnit
  [("A", []), ("B", ["A"]), ("C", ["A", "B"])]

theorem graphRedundant_admitted : graphRedundant.env.basesOK = true := rfl

theorem graphRedundant_public : graphRedundant.env.linearize "C" = some ["C", "B", "A"] := rfl

theorem graphRedundant_constructors : graphRedundant.env.ctorOrder "C" = ["A", "B", "C"] := rfl

/-- An admitted acyclic graph with incompatible local orders; W inherits the obstruction. -/
def graphBad : Syn .unit := graphUnit
  [("A", []), ("B", []), ("X", ["A", "B"]), ("Y", ["B", "A"]),
    ("Z", ["X", "Y"]), ("W", ["Z"])]

theorem graphBad_admitted : graphBad.env.basesOK = true := rfl

/-- Actual independent merge certificate after two successful choices. -/
theorem graphBad_merge_stuck : Stuck [["Y", "A", "B"], ["X", "B", "A"], ["Y", "X"]] :=
  Stuck.step (h := "Y") (by decide) (Stuck.step (h := "X") (by decide) (.here (by unfold Obstruction; constructor <;> decide)))

theorem graphBad_certificate : GraphBlocked graphBad.env "Z" := by
  have hm : (graphBad.env.bases "Z").reverse.mapM graphBad.env.linearize =
      some [["Y", "A", "B"], ["X", "B", "A"]] := rfl
  obtain ⟨hlen, hpt⟩ := Solidity.Frontend.Static.mapM_spec hm
  exact .merge hlen (fun i b Lb hb hLb =>
    linearizeF_exact_sound _ b Lb (hpt i b Lb hb hLb)) graphBad_merge_stuck

theorem graphBad_all_fuel (n : Nat) : graphBad.env.linearizeF n "Z" = none :=
  graphBad_certificate.linearizeF_none n

theorem graphBad_public_refused : graphBad.env.linearize "Z" = none := graphBad_all_fuel _

/-- The base-propagation constructor is inhabited by a concrete source-unit edge. -/
theorem graphBad_inherited_certificate : GraphBlocked graphBad.env "W" :=
  .base (by decide) graphBad_certificate

theorem graphBad_inherited_all_fuel (n : Nat) : graphBad.env.linearizeF n "W" = none :=
  graphBad_inherited_certificate.linearizeF_none n

/-- The same concrete obstruction transports to actual declaration-position identities. -/
theorem graphBad_identity_stuck : Stuck ([[3, 0, 1], [2, 1, 0], [3, 2]] : List (List Nat)) := by
  have hm : (graphBad.env.bases "Z").reverse.mapM graphBad.env.linearize =
      some [["Y", "A", "B"], ["X", "B", "A"]] := rfl
  obtain ⟨hlen, hpt⟩ := Solidity.Frontend.Static.mapM_spec hm
  exact graphBad_merge_stuck.rename (rank_injects graphBad.env)
    (merge_input_known graphBad_admitted hlen (fun i b Lb hb hLb =>
      linearizeF_exact_sound _ b Lb (hpt i b Lb hb hLb)))

def graphSelfCycle : Syn .unit := graphUnit [("S", ["S"])]

theorem graphSelfCycle_not_admitted : graphSelfCycle.env.basesOK = false := rfl

theorem graphSelfCycle_path : CyclePath graphSelfCycle.env "S" "S" := .direct (by decide)

theorem graphSelfCycle_all_fuel (n : Nat) : graphSelfCycle.env.linearizeF n "S" = none :=
  graphSelfCycle_path.linearizeF_none n

def graphMutualCycle : Syn .unit := graphUnit [("P", ["Q"]), ("Q", ["P"])]

theorem graphMutualCycle_not_admitted : graphMutualCycle.env.basesOK = false := rfl

theorem graphMutualCycle_path : CyclePath graphMutualCycle.env "P" "P" :=
  .step (b := "Q") (by decide) (.direct (by decide))

theorem graphMutualCycle_all_fuel (n : Nat) : graphMutualCycle.env.linearizeF n "P" = none :=
  graphMutualCycle_path.linearizeF_none n

/-- The fallback sequence of a refused graph is not a successful C3 result. -/
theorem graphMutualCycle_fallback : graphMutualCycle.env.ctorOrder "P" = ["P"] := rfl

def graphEmpty : Syn .unit := graphUnit []

theorem graphEmpty_admitted : graphEmpty.env.basesOK = true := rfl

/-- The existing API accepts an undeclared root as a leaf, outside resolved-root identity claims. -/
theorem graphUnknown_public : graphEmpty.env.linearize "missing" = some ["missing"] := rfl

theorem graphUnknown_identity_refused : ¬ IdentityLin graphEmpty.env 0 [0] := by
  intro ht
  have hbad : 0 < 0 := (ht.known graphEmpty_admitted 0 List.mem_cons_self).1
  exact Nat.lt_irrefl _ hbad

/-- Undeclared sentinels genuinely collide; support-local injection is essential. -/
theorem graphSentinel_not_global_injective :
    ¬ InjectsOn (fun _ : String => True) (rank graphEmpty.env) := by
  intro hf
  have he : "a" = "b" := hf "a" "b" True.intro True.intro rfl
  exact (by decide : "a" ≠ "b") he

/-- Both reachability constructors are inhabited by the actual diamond graph. -/
theorem graphDiamond_refl : Reaches graphDiamond.env "D" "D" := .refl

theorem graphDiamond_reaches : Reaches graphDiamond.env "D" "A" :=
  .step (b := "C") (by decide) (.step (b := "A") (by decide) .refl)

theorem graphDiamond_C_public : graphDiamond.env.linearize "C" = some ["C", "A"] := rfl

/-- Complete inherited constructor subsequences are retained in the descendant's sequence. -/
theorem graphDiamond_constructor_subsequence :
    (graphDiamond.env.ctorOrder "C").Sublist (graphDiamond.env.ctorOrder "D").dropLast :=
  ctor_monotone graphDiamond_public (by decide) graphDiamond_C_public

/-- Interface units exercise the producer's separate interface-node branch. -/
def graphInterfaceUnit (specs : List (String × List String)) : Syn .unit :=
  .unit (specs.foldr (fun spec acc =>
    .cons (.interface spec.1 (graphSpecs spec.2) .nil) acc) .nil)

def graphInterfaceDiamond : Syn .unit := graphInterfaceUnit
  [("IA", []), ("IB", ["IA"]), ("IC", ["IA"]), ("ID", ["IB", "IC"])]

theorem graphInterfaceDiamond_admitted : graphInterfaceDiamond.env.basesOK = true := rfl

theorem graphInterfaceDiamond_public :
    graphInterfaceDiamond.env.linearize "ID" = some ["ID", "IC", "IB", "IA"] := rfl

/-- Intrinsic unit membership discharges the identity-root evidence, without an extra caller premise. -/
theorem graphInterfaceDiamond_identities : IdentityLin graphInterfaceDiamond.env 3 [3, 2, 1, 0] :=
  (unit_identity_iff graphInterfaceDiamond graphInterfaceDiamond_admitted "ID" (by decide) _).mp (by decide)

def graphMixed : Syn .unit := .unit
  (.cons (.interface "IA" .nil .nil)
    (.cons (.interface "IB" (graphSpecs ["IA"]) .nil)
      (.cons (.contract false "C" .none (graphSpecs ["IB"]) .nil) .nil)))

theorem graphMixed_admitted : graphMixed.env.basesOK = true := rfl

theorem graphMixed_public : graphMixed.env.linearize "C" = some ["C", "IB", "IA"] := rfl

def graphBadInterface : Syn .unit := .unit
  (.cons (.contract false "A" .none .nil .nil)
    (.cons (.interface "I" (graphSpecs ["A"]) .nil) .nil))

/-- Existing admission refuses an interface inheriting a contract, independently of merge success. -/
theorem graphBadInterface_not_admitted : graphBadInterface.env.basesOK = false := rfl

theorem graphBadInterface_merge_only : graphBadInterface.env.linearize "I" = some ["I", "A"] := rfl

/-- Duplicate declaration occurrences are not asserted to form a name-to-all-positions bijection. -/
def graphDuplicate : Syn .unit := graphUnit [("A", []), ("A", ["A"])]

theorem graphDuplicate_first_selected : rank graphDuplicate.env "A" = 0 := rfl

theorem graphDuplicate_public_first : graphDuplicate.env.linearize "A" = some ["A"] := rfl

theorem graphDuplicate_unselected : ¬ GoodId graphDuplicate.env 1 := by unfold GoodId; decide

/-- The duplicate-source control remains outside the existing no-clash admission. -/
theorem graphDuplicate_clashes :
    ¬ graphDuplicate.decls.Pairwise (fun d d' => d.clash graphDuplicate.env d' = false) := by decide

def graphSettings : Settings := ⟨.legacy, []⟩
def graphResolution : Resolution := resolveUnit graphSettings graphDiamond

theorem graphResolution_resolves : Resolves' graphSettings graphDiamond graphResolution := ⟨rfl, rfl⟩

/-- The actual existing resolution relation supplies the final positional-C3 interface. -/
theorem graphResolution_identities : IdentityLin graphResolution.env 3 [3, 2, 1, 0] :=
  (resolved_identity_iff graphResolution_resolves graphDiamond_admitted "D" (by decide) _).mp (by decide)

/-- The actual incompatible base sequences have no duplicate-free common order. -/
theorem graphBad_merge_no_order :
    ∀ out, ¬ CommonOrder [["Y", "A", "B"], ["X", "B", "A"], ["Y", "X"]] out :=
  graphBad_merge_stuck.not_common_order

/-- The same obstruction is semantic over actual declaration-position identities. -/
theorem graphBad_identity_no_order :
    ∀ out, ¬ CommonOrder ([[3, 0, 1], [2, 1, 0], [3, 2]] : List (List Nat)) out :=
  graphBad_identity_stuck.not_common_order

end Solidity.Frontend.C3Exactness
