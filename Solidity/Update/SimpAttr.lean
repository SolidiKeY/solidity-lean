import Lean

/-!
Registers the `upd_merge_set` simp attribute: the reader lemmas that let two
spellings of one accumulated update be proved equal (`Update/Merge.lean`, and
the `upd_merge` tactic of `Examples/Common.lean`).

Its own module for the same reason `Examples/SimpAttr.lean` is: a simp
attribute has to be initialized in a module imported by its users, and the
users here are both a proof module and a tactic module.
-/

register_simp_attr upd_merge_set
