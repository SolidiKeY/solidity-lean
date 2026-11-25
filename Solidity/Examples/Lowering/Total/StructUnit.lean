import Solidity.Correctness.Lowering.Total.StructUnit
import Solidity.Examples.Lowering.Total.ReferenceStatePlacement

/-! Struct declarations, reference roots, the constructor and functions in one unit:
the declaration table of a mixed unit, a struct root that resolves there, the implicit
constructor, a repeated struct name and a root carrying a struct name (both unresolved),
and each component refusal. Execution is not checked. -/
namespace Solidity.Examples.Lowering.Total.StructUnit

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.StructUnit
open Solidity.Examples.Lowering.Total.ReferenceStatePlacement (ctor get mixed)
open ReferenceDecode (Resolved)

/-- `function get() internal view returns (uint r) { return n; }` -/
def fs : List (Name × FunDecl) := [("get", { get with body := [.ret (some (.name "n"))] })]
/-- `struct Pair { uint a; uint8 b; } struct Tag { address t; }
uint8 n = 1; Pair p; constructor() payable { n = 2; }` -/
def full : Contract :=
  { vars := [("n", .uint), ("p", .ref (.struct "Pair{a:uint;b:uint8}"))], widths := [("n", 8)],
    structs := [("Pair", "Pair{a:uint;b:uint8}"), ("Tag", "Tag{t:address}")],
    inits := [("n", .num 1)], ctor := some ctor }
/-- `full` with the implicit constructor. -/
def implicit : Contract := { full with ctor := none }

def unitOf (C : Contract) (fs : List (Name × FunDecl)) : Option (Source.Syn .unit) :=
  (build tablesS [] C "C" fs).toOption
def table (C : Contract) (fs : List (Name × FunDecl)) :=
  (unitOf C fs).map fun u => u.decls.map fun d => (d.kind, d.name, d.scope)
def envOf (C : Contract) (fs : List (Name × FunDecl)) : Source.Env :=
  ((unitOf C fs).map Source.Syn.env).getD ⟨[]⟩

/-! The mixed unit, evaluated; the theorems below are the general facts. -/

-- The contract, the structs in table order, the constructor, the roots, the function.
#guard table full fs == some [(.contract, "C", none), (.struct, "Pair", some "C"),
    (.struct, "Tag", some "C"), (.constructor, "", some "C"), (.stateVar, "n", some "C"),
    (.stateVar, "p", some "C"), (.function, "get", some "C")]
-- The implicit constructor: the same table less the constructor.
#guard table implicit fs == (table full fs).map (·.erase (.constructor, "", some "C"))
-- The struct root's declared type resolves in this unit (it did not without the structs).
#guard (((envOf full fs).stateVarsOf "C").map (·.varTy (envOf full fs))).map Option.isSome ==
    [true, true]
#guard Source.elaborates (envOf full fs)

/-! The exported facts. -/

theorem apart (w : Name) (hw : w ≠ "n" ∧ w ≠ "p" ∧ w ≠ "get") : Apart full fs w := by
  refine ⟨fun v mv => ?_, fun f mf src hs => ?_⟩
  · simp only [full, List.mem_cons, List.not_mem_nil, or_false] at mv
    rcases mv with rfl | rfl <;> exact fun e => by simp_all
  · simp only [fs, List.mem_singleton] at mf
    subst mf; cases hs; exact fun e => hw.2.2 e.symm

example {u} (h : build tablesS [] full "C" fs = .ok u) :=
  And.intro (build_decls h) (And.intro (build_structs h) (And.intro (build_functions h)
    (And.intro (build_owned h) (And.intro (build_roots h) (build_ctor_explicit h rfl)))))
example {u} (h : build tablesS [] implicit "C" fs = .ok u) := build_ctor_implicit h rfl
example {u} (h : build tablesS [] full "C" fs = .ok u) (hE : Source.elaborates u.env = true) :=
  build_inits h hE
/-- `Pair` is declared once and carried by no root or function: it resolves. -/
example {u} (h : build tablesS [] full "C" fs = .ok u) :
    Resolved u.env (some "C") "Pair" ⟨some "C", "Pair"⟩ :=
  (build_resolved h (by decide) (apart _ (by decide))).choose_spec.choose_spec.2.2.2
/-- The reference root `Pair p` is typed in the unit: its obligation is discharged. -/
example {u} (h : build tablesS [] full "C" fs = .ok u) :=
  build_typed h fun v mv s ms w hw => by
    simp only [full, List.mem_cons, List.not_mem_nil, or_false] at mv
    rcases mv with rfl | rfl
    · simp [ReferenceDecode.structsTy] at ms
    · simp [ReferenceDecode.structsTy, ReferenceDecode.structsRef] at ms
      subst ms
      have : ReferenceDecode.written? full "Pair{a:uint;b:uint8}" = some "Pair" := by decide
      rw [this, Option.some.injEq] at hw
      subst hw
      exact ⟨by decide, apart _ (by decide)⟩

/-- `Pair`'s Source fields in the unit, every declared name `Apart`. -/
example {u} (h : build tablesS [] full "C" fs = .ok u) := by
  refine build_structFields h (fun w e hl => apart w ?_) (w := "Pair") rfl (by decide) .storage
    fun _ _ => .inl rfl
  simp only [full, Solidity.Semantics.lookupBy] at hl; repeat' split at hl
  all_goals simp_all

/-! Boundaries: names that do not resolve. -/

/-- `struct Pair` written twice: both are declared, and `Pair` resolves to neither. -/
def twice : Contract :=
  { full with structs := [("Pair", "Pair{a:uint;b:uint8}"), ("Pair", "Pair{x:address}")] }
#guard (table twice fs).map (·.filter (·.1 == .struct)) ==
    some [(.struct, "Pair", some "C"), (.struct, "Pair", some "C")]
example {u} (h : build tablesS [] twice "C" fs = .ok u) :
    ¬ ∃ d, Resolved u.env (some "C") "Pair" d := fun r => by
  have two := (build_resolved_only h (by decide) r).1
  revert two; decide
/-- A root named `Tag`: the struct name is carried by a state variable, so ambiguous. -/
def clash : Contract := { full with vars := full.vars ++ [("Tag", .uint)] }
#guard (table clash fs).isSome
example {u} (h : build tablesS [] clash "C" fs = .ok u) :
    ¬ ∃ d, Resolved u.env (some "C") "Tag" d := fun r =>
  (build_resolved_only h (by decide) r).2.1 ("Tag", .uint) (by decide) rfl

/-! Component refusals: each is named, nothing is dropped. -/

/-- A table entry without members, after a good one: its position is named. -/
example : build tablesS [] { full with structs := full.structs ++ [("T", "Nope")] } "C" fs =
    .error (.structs (.noMembers 2 "T" "Nope")) := build_structs_error rfl
/-- A constructor with no retained header. -/
example : build tablesS [] { full with ctor := some { ctor with sourceDecl := none } } "C" fs =
    .error (.placement .constructor) := build_placement_error rfl rfl
/-- A function entry with no retained header. -/
example : build tablesS [] full "C" [("get", { get with sourceDecl := none })] =
    .error .functions := build_functions_error rfl rfl rfl
/-- With no struct entry the unit is `assemble`'s. -/
example {u} (h : ReferenceStatePlacement.assemble tablesS [] mixed "C" fs = .ok u) :
    build tablesS [] mixed "C" fs = .ok u := build_of_assemble rfl h

end Solidity.Examples.Lowering.Total.StructUnit
