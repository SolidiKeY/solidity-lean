import Solidity.Frontend.ExpressionUniqueness.AddRoot
import Solidity.Frontend.ExpressionUniqueness.Families

/-!
# Inhabited arbitrary prefix and additive-root controls

The old raw-marker countercontrol is handled by the new unfinished-state scan.
Starting the same prefix at a finished state remains intentionally rejected.
Every additive operator with arbitrarily many right-side prefix minuses has an
exact yield, original precedence certificate and correct outer marker position.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem arbitrary_prefix_addFree (n : Nat) (name : String) : AddFree (negTokens (n + 1) name) :=
  high_expr_derives_addFree (negFamily (n + 1) name) (negTokens (n + 1) name)
    (negFamily_prec (n + 1) name) (by exact (by decide : 10 < 13))
    (negFamily_certified (n + 1) name).1

theorem arbitrary_prefix_lastAdd_none (n : Nat) (name : String) :
    lastAdd (negTokens (n + 1) name) = none :=
  lastAdd_none_of_skip _ ([], true) (arbitrary_prefix_addFree n name)

theorem finished_prefix_is_selected (n : Nat) (name : String) :
    addSkip ([], true) (negTokens (n + 1) name) = none := rfl

theorem add_prec_join (op : AddOp) (a b : Syn .expr) (ha : a.prec = true) (hb : b.prec = true)
    (hla : 10 ≤ a.level) (hlb : 11 ≤ b.level) : (Syn.addSub op a b).prec = true := by
  have hr : (Syn.addSub op a b).precNode = true :=
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true hla, decide_eq_true hlb⟩
  have haa : a.all Syn.precNode = true := (Bool.and_eq_true_iff.mp ha).2
  have hba : b.all Syn.precNode = true := (Bool.and_eq_true_iff.mp hb).2
  simp only [Syn.prec, Syn.all, hr, haa, hba, Bool.true_and]

theorem add_yield_join (op : AddOp) (a b : Syn .expr) (initial middle rest : List Choice)
    (xs ys : List (List Tok)) (ha : a.yield initial = some (xs, middle))
    (hb : b.yield middle = some (ys, rest)) :
    (Syn.addSub op a b).yield initial = some ([xs.flatten ++ pu op.punct ++ ys.flatten], rest) := by
  change ((a.yield initial).bind fun ar => (b.yield ar.2).bind fun br =>
    some ([ar.1.flatten ++ pu op.punct ++ br.1.flatten], br.2)) = _
  rw [ha]
  simp only [Option.bind_some]
  rw [hb]
  rfl

def mixedAddPrefix (op : AddOp) (n : Nat) : Syn .expr :=
  .addSub op (.ident "a") (negFamily (n + 1) "b")

def mixedAddPrefixTokens (op : AddOp) (n : Nat) : List Tok :=
  [.ident "a", .punct op.punct] ++ negTokens (n + 1) "b"

theorem mixedAddPrefix_prec (op : AddOp) (n : Nat) : (mixedAddPrefix op n).prec = true :=
  add_prec_join op (.ident "a") (negFamily (n + 1) "b") rfl (negFamily_prec (n + 1) "b")
    (by exact (by decide : 10 ≤ 16)) (by exact (by decide : 11 ≤ 13))

theorem mixedAddPrefix_yield (op : AddOp) (n : Nat) (rest : List Choice) :
    (mixedAddPrefix op n).yield rest = some ([mixedAddPrefixTokens op n], rest) := by
  simpa only [mixedAddPrefix, mixedAddPrefixTokens, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, pu, List.append_assoc] using
    add_yield_join op (.ident "a") (negFamily (n + 1) "b") rest rest rest
      [[.ident "a"]] [negTokens (n + 1) "b"] rfl (negFamily_yield (n + 1) "b" rest)

theorem mixedAddPrefix_certified (op : AddOp) (n : Nat) :
    (mixedAddPrefix op n).Derives (mixedAddPrefixTokens op n) ∧ (mixedAddPrefix op n).prec = true :=
  ⟨⟨[], (expr_toks_iff _ [] _).mpr (mixedAddPrefix_yield op n [])⟩, mixedAddPrefix_prec op n⟩

theorem mixedAddPrefix_outer_marker (op : AddOp) (n : Nat) :
    lastAdd (mixedAddPrefixTokens op n) = some (1, .punct op.punct) := by
  have hm : modeStep ([], true) (.punct op.punct) = some ([], false) := by cases op <;> rfl
  have hit : addHit ([], true) (.punct op.punct) = true := by cases op <;> rfl
  exact lastAdd_marker [.ident "a"] (negTokens (n + 1) "b") (.punct op.punct)
    (modeDone_idt "a") (arbitrary_prefix_addFree n "b") hm hit

end Solidity.Frontend.ExpressionUniqueness
