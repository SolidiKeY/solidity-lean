import Solidity.Semantics.Agree

/-!
# The simp sets of the generic term functions

A term is a symbol applied to terms (`Tm`, `Update.lean`), and its reading
is the symbol's reading of its arguments' (`Tm.eval`, then `OpN.eval`).
`simp only [tm_eval]` unfolds both steps at once, and `simp only [tm_denote]`
the same for the Theory reading (`Tm.denote`, `OpN.denote`).  They are
declared here, below `Update.lean`, because a simp set is usable only in the
modules that import the one declaring it.
-/

/-- `Tm.eval` and the symbols' readings `Op0.eval` … `Op3.eval`. -/
register_simp_attr tm_eval

/-- `Tm.denote` and the symbols' denotations `Op0.denote` … `Op3.denote`. -/
register_simp_attr tm_denote
