import Lean

/-!
# The simp set of `NoPanic`

`simp only [no_panic_simp]` closes `NoPanic (op …)` for every operation of
the interpreter that never panics (`Semantics/NoPanic.lean`).  The lemmas
live in this set rather than the default one, so an unrestricted `simp`
elsewhere does not try them on every `_ = .error .panic` it meets.  A simp
set is usable only in the modules that import the one declaring it, hence
this module.
-/

/-- The `*_noPanic` lemmas: an operation that never panics. -/
register_simp_attr no_panic_simp
