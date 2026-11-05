import Solidity.Frontend.Checked.Print

/-! H28 G09: exact consumption and layout contracts. These statements concern
actual `Syn.yield`, including the unconsumed layout; they do not identify
layout witnesses or infer syntax equality from an observed token equality. -/

namespace Solidity.Frontend.TypeGrammarH28

open Solidity.Source Solidity.Frontend.Checked

/-- Successful exact layout equivalence. Failed yields are not equivalent. -/
def LayoutEquivalent {c : Cat} (t : Syn c) (left right : List Choice) : Prop :=
  ∃ ts : List Tok, t.toks left = some ts ∧ t.toks right = some ts

/-- Equality of successful token observations does not require equal witnesses. -/
theorem layoutEquivalent_symm {c : Cat} {t : Syn c} {left right : List Choice}
    (h : LayoutEquivalent t left right) : LayoutEquivalent t right left := by
  obtain ⟨ts, hl, hr⟩ := h
  exact ⟨ts, hr, hl⟩

theorem layoutEquivalent_trans {c : Cat} {t : Syn c} {a b d : List Choice}
    (hab : LayoutEquivalent t a b) (hbd : LayoutEquivalent t b d) :
    LayoutEquivalent t a d := by
  obtain ⟨ts, ha, hb⟩ := hab
  obtain ⟨us, hb', hd⟩ := hbd
  have he : ts = us := Option.some.inj (hb.symm.trans hb')
  exact ⟨ts, ha, he ▸ hd⟩

/-- An elementary type consumes no layout, even with an arbitrary suffix. -/
theorem elem_yield (e : Elem) (suffix : List Choice) :
    (Syn.elem e).yield suffix = some ([e.toks], suffix) := rfl

/-- A qualified name consumes no layout. -/
theorem userType_yield (p : IdPath) (suffix : List Choice) :
    (Syn.userType p).yield suffix = some ([p.toks], suffix) := rfl

/-- The canonical elementary layout is inhabited for every elementary form. -/
theorem elem_toks (e : Elem) : (Syn.elem e).toks [] = some e.toks := by
  change some (e.toks ++ []) = some e.toks
  simp only [List.append_nil]

/-- The canonical qualified-name layout is inhabited for every path. -/
theorem userType_toks (p : IdPath) : (Syn.userType p).toks [] = some p.toks := by
  change some (p.toks ++ []) = some p.toks
  simp only [List.append_nil]

/-- Exact whole-layout consumption excludes unused choices. -/
theorem elem_no_unused_layout (e : Elem) (choice : Choice) (suffix : List Choice) :
    (Syn.elem e).toks (choice :: suffix) = none := rfl

theorem userType_no_unused_layout (p : IdPath) (choice : Choice) (suffix : List Choice) :
    (Syn.userType p).toks (choice :: suffix) = none := rfl

#print axioms layoutEquivalent_symm
#print axioms layoutEquivalent_trans
#print axioms elem_yield
#print axioms userType_yield
#print axioms elem_toks
#print axioms userType_toks
#print axioms elem_no_unused_layout
#print axioms userType_no_unused_layout

end Solidity.Frontend.TypeGrammarH28
