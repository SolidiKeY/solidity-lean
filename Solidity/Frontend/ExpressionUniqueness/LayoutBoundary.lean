import Solidity.Frontend.ExpressionUniqueness.YieldSplit
import Solidity.Frontend.ExpressionUniqueness.ExpressionBalance

/-!
# Successful expression layouts extend and trim

The existing printer only pops explicit layout choices. A successful partial
execution can be witnessed by a fully consumed layout, independently of its
original unused suffix. This is a printer-state property, not a new syntax or
producer interface. It applies only to the existing expression category closure.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def LayoutExtend {α : Type} (p : Pr α) : Prop :=
  ∀ initial value rest tail, p initial = some (value, rest) →
    p (initial ++ tail) = some (value, rest ++ tail)

def LayoutTrim {α : Type} (p : Pr α) : Prop :=
  ∀ initial value rest, p initial = some (value, rest) →
    ∃ used, p used = some (value, [])

def LayoutPrinter {α : Type} (p : Pr α) : Prop := LayoutExtend p ∧ LayoutTrim p

theorem layout_pure {α : Type} (value : α) : LayoutPrinter (pure value) := by
  constructor
  · intro initial result rest tail h
    obtain ⟨rfl, rfl⟩ := pure_success_split value result initial rest h
    rfl
  · intro initial result rest h
    obtain ⟨rfl, states⟩ := pure_success_split value result initial rest h
    exact ⟨[], rfl⟩

theorem layout_lift {α : Type} (o : Option α) : LayoutPrinter (Pr.lift o) := by
  cases o with
  | none => constructor <;> intro initial value rest <;> simp only [Pr.lift, Option.map_none] <;> intros <;> contradiction
  | some value => exact layout_pure value

theorem layout_pop : LayoutPrinter Pr.pop := by
  constructor
  · intro initial value rest tail h
    cases initial with
    | nil => cases h
    | cons c cs => cases h; rfl
  · intro initial value rest h
    exact ⟨[value], rfl⟩

theorem layout_bind {α β : Type} (p : Pr α) (k : α → Pr β)
    (hp : LayoutPrinter p) (hk : ∀ value, LayoutPrinter (k value)) : LayoutPrinter (p >>= k) := by
  constructor
  · intro initial value rest tail h
    obtain ⟨x, middle, hx, hkx⟩ := bind_success_split p k initial rest value h
    change (p (initial ++ tail)).bind (fun r => k r.1 r.2) = _
    rw [hp.1 initial x middle tail hx, Option.bind_some]
    exact (hk x).1 middle value rest tail hkx
  · intro initial value rest h
    obtain ⟨x, middle, hx, hkx⟩ := bind_success_split p k initial rest value h
    obtain ⟨left, hl⟩ := hp.2 initial x middle hx
    obtain ⟨right, hr⟩ := (hk x).2 middle value rest hkx
    refine ⟨left ++ right, ?_⟩
    change (p (left ++ right)).bind (fun r => k r.1 r.2) = _
    rw [hp.1 left x [] right hl, List.nil_append, Option.bind_some]
    exact hr

theorem layout_popAttrs : LayoutPrinter popAttrs := by
  apply layout_bind _ _ layout_pop
  intro choice
  cases choice with
  | attrs order => exact layout_pure _
  | frags lengths => exact layout_lift _
  | layoutFirst b => exact layout_lift _

theorem layout_fragsP (mk : Bytes → Tok) (bs : Bytes) : LayoutPrinter (fragsP mk bs) := by
  apply layout_bind _ _ layout_pop
  intro choice
  cases choice with
  | attrs order => exact layout_lift _
  | layoutFirst b => exact layout_lift _
  | frags lengths =>
    cases lengths with
    | nil => exact layout_lift _
    | cons n ns =>
      apply layout_bind _ _ (layout_lift _)
      intro chunks
      exact layout_pure _

theorem layout_litP (l : Lit) : LayoutPrinter (litP l) := by
  cases l with
  | bool value => exact layout_pure _
  | num value => exact layout_pure _
  | str bs => exact layout_fragsP _ _
  | hexStr bs => exact layout_fragsP _ _
  | unicodeStr bs => exact layout_fragsP _ _

theorem layout_attrsP (singles : List (Slot × List Tok)) (mods : List (List Tok)) (order : List Slot) :
    LayoutPrinter (attrsP singles mods order) := layout_lift _

theorem expressionCategory_yield_layout {c : Cat} (e : Syn c) :
    ExpressionCategory c = true → LayoutPrinter e.yield := by
  induction e <;> intro hc
  all_goals first | (cases hc; done) | skip
  all_goals simp only [Syn.yield]
  all_goals repeat first
    | assumption
    | exact layout_pure _
    | exact layout_popAttrs
    | exact layout_litP _
    | exact layout_attrsP _ _ _
    | (apply_assumption; first | assumption | rfl)
    | apply layout_bind
    | intro value

theorem expression_yield_trim (e : Syn .expr) (initial rest : List Choice) (items : List (List Tok))
    (hy : e.yield initial = some (items, rest)) : ∃ used, e.yield used = some (items, []) :=
  (expressionCategory_yield_layout e rfl).2 initial items rest hy

theorem expression_partial_derives (e : Syn .expr) (initial rest : List Choice)
    (items : List (List Tok)) (hy : e.yield initial = some (items, rest)) : e.Derives items.flatten := by
  obtain ⟨used, success⟩ := expression_yield_trim e initial rest items hy
  obtain ⟨word, shape⟩ := expr_yield_single e used items [] success
  subst items
  refine ⟨used, ?_⟩
  apply (expr_toks_iff e used [word].flatten).mpr
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using success

end Solidity.Frontend.ExpressionUniqueness
