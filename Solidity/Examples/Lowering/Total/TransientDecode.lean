import Solidity.Correctness.Lowering.Total.TransientDecode

/-! Checks of the transient declaration component: roots are declared
`transient` at their marked type and width, other variables are not, order is
kept, and a variable with no Source reading is an error naming it. -/
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

/-- `int128 transient n;` keeps its width. -/
def narrow : Contract where
  vars := [("n", .prim .int)]
  transientRoots := ["n"]
  widths := [("n", 128)]

example : decls narrow = .ok (.cons (stateVarDecl (.int true 128 (by decide)) true "n") .nil) :=
  rfl

/-- `uint[] xs; uint transient t;`: an error naming `xs`, not `t` alone. -/
def withArray : Contract where
  vars := [("xs", .ref (.array (.prim .uint))), ("t", .prim .uint)]
  transientRoots := ["t"]

example : decls withArray = .error ⟨"xs", .reference⟩ := rfl

/-- A width no integer type has is an error naming the variable. -/
def badWidth : Contract where
  vars := [("t", .prim .uint), ("w", .prim .uint)]
  transientRoots := ["t"]
  widths := [("w", 7)]

example : decls badWidth = .error ⟨"w", .noElem .uint⟩ := rfl

/-- The error inversion, instantiated: `t` before `w` has a declaration. -/
example : ∃ pre U post, badWidth.vars = pre ++ ("w", U) :: post ∧
    ∀ v ∈ pre, ∃ d, declT (elemOf badWidth) badWidth.transientRoots v = .ok d := by
  obtain ⟨pre, U, post, h, hpre, _⟩ := declsT_error badWidth.vars (show decls badWidth = _ from rfl)
  exact ⟨pre, U, post, h, hpre⟩

/-- `State transient s;` (an enum) and a transient function-type variable are
refused, not declared `uint256 transient`. -/
def withEnum : Contract where
  vars := [("s", .prim .uint), ("f", .prim .uint)]
  transientRoots := ["s", "f"]
  enums := [("State", ["Idle", "Busy"])]
  widths := [("s#enum", 1), ("f#function()", 0)]

example : decls withEnum = .error ⟨"s", .noElem .uint⟩ := rfl
example : decls { withEnum with widths := [("f#function()", 0)] } = .error ⟨"f", .noElem .uint⟩ := rfl

/-- Roots change flags, never the domain; with none, the existing decoder's
state variables. -/
example : (∃ parts, declsT (elemOf withArray) ["t"] withArray.vars = .ok parts) ↔
    ∃ parts, declsT (elemOf withArray) [] withArray.vars = .ok parts :=
  declsT_roots_domain _ _ _
example : (declsT (elemOf mixed) [] mixed.vars).toOption =
    Decode.stateVarsOf (Decode.elemB mixed.widths) mixed.vars := declsT_nil_roots _ _

/-- Every transient root of `mixed` is declared `transient`. -/
example {parts : Source.Syn (.list (.part false))} (h : decls mixed = .ok parts) :
    ∃ p e, Semantics.lookupBy "o" mixed.vars = some (.prim p) ∧ Represents mixed.widths "o" p e ∧
      (parts.collect (some Decode.contractName)).find?
        (fun d => d.kind == .stateVar && d.scope == some Decode.contractName && d.name == "o") =
        some ⟨.stateVar, "o", some Decode.contractName, false, stateVarDecl e true "o"⟩ :=
  decls_root h (by decide)

end Solidity.Examples.Lowering.Total.TransientDecode
