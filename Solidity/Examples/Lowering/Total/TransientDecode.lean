import Solidity.Correctness.Lowering.Total.TransientDecode

/-! Checks of the transient declaration component: transient roots are
declared `transient` at their marked type and width, persistent variables are
not, order is kept, and a variable with no Source reading is an error naming
it, not a dropped declaration. -/
namespace Solidity.Examples.Lowering.Total.TransientDecode

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.TransientDecode

/-- `uint8 a; bool transient t; address transient o; bytes2 b;`. -/
def mixed : Contract where
  vars := [("a", .prim .uint), ("t", .prim .bool), ("o", .prim .uint), ("b", .prim .uint)]
  transientRoots := ["t", "o"]
  widths := [("a", 8), ("o#address", 20), ("b", 16), ("b#bytes", 2)]

/-- Each variable at its marked type and width, transient exactly at the roots,
in declaration order. -/
theorem mixed_decls : decls mixed = .ok
    (.cons (stateVarDecl (.int false 8 (by decide)) false "a")
    (.cons (stateVarDecl .bool true "t")
    (.cons (stateVarDecl .address true "o")
    (.cons (stateVarDecl (.fixedBytes 2 (by decide)) false "b") .nil)))) := rfl

/-- Persistent storage does not stand in for transient storage. -/
example : decls mixed ≠ .ok
    (.cons (stateVarDecl (.int false 8 (by decide)) false "a")
    (.cons (stateVarDecl .bool false "t")
    (.cons (stateVarDecl .address false "o")
    (.cons (stateVarDecl (.fixedBytes 2 (by decide)) false "b") .nil)))) := by
  intro h
  have flags := (decls_ok_iff.mp h).transient
  simp [stateViews, stateView, stateVarDecl, mixed] at flags

/-- The flags, in order. -/
example : (match decls mixed with
    | .ok parts => (stateViews parts).map (Option.map (·.2.2))
    | .error _ => []) = [some false, some true, some true, some false] := by
  rw [mixed_decls]; simp [stateViews, stateView, stateVarDecl]

/-- A transient root of a narrow integer keeps its width. -/
def narrow : Contract where
  vars := [("n", .prim .int)]
  transientRoots := ["n"]
  widths := [("n", 128)]

example : decls narrow = .ok (.cons (stateVarDecl (.int true 128 (by decide)) true "n") .nil) :=
  rfl

/-- With no roots the component is the marked decoder's state variables. -/
example : (declsT (elemOf mixed) [] mixed.vars).toOption =
    Decode.stateVarsOf (Decode.elemB mixed.widths) mixed.vars :=
  declsT_nil_roots _ _

/-- A reference-typed state variable is an error naming it; the following
transient root is not silently kept with it dropped. -/
def withArray : Contract where
  vars := [("xs", .ref (.array (.prim .uint))), ("t", .prim .uint)]
  transientRoots := ["t"]

example : decls withArray = .error ⟨"xs", .reference⟩ := rfl

/-- A width no integer type has is an error naming the variable, after the
earlier declarations succeed. -/
def badWidth : Contract where
  vars := [("t", .prim .uint), ("w", .prim .uint)]
  transientRoots := ["t"]
  widths := [("w", 7)]

example : decls badWidth = .error ⟨"w", .noElem .uint⟩ := rfl

/-- An address marker on a variable with its own width row is no Source type. -/
def badAddress : Contract where
  vars := [("o", .prim .uint)]
  transientRoots := ["o"]
  widths := [("o", 160), ("o#address", 20)]

example : decls badAddress = .error ⟨"o", .noElem .uint⟩ := rfl

/-- The general statements, instantiated: every transient root of `mixed` is
declared `transient`. -/
example {parts : Source.Syn (.list (.part false))} (h : decls mixed = .ok parts) :
    ∃ p e, Semantics.lookupBy "o" mixed.vars = some (.prim p) ∧ Represents mixed.widths "o" p e ∧
      (parts.collect (some Decode.contractName)).find?
        (fun d => d.kind == .stateVar && d.scope == some Decode.contractName && d.name == "o") =
        some ⟨.stateVar, "o", some Decode.contractName, false, stateVarDecl e true "o"⟩ :=
  decls_root h (by decide)

end Solidity.Examples.Lowering.Total.TransientDecode
