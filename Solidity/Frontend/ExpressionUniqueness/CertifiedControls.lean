import Solidity.Frontend.ExpressionUniqueness.Accepted
import Solidity.Frontend.ExpressionUniqueness.ContainerControls

/-!
# Inhabited arbitrary-family controls for the complete theorem

Arbitrary array depth, parameter counts, optional returns and both attribute
orders inhabit a meta-type expression through an array wrapper. The original
DIRECT function-type meta conversion remains refused. Optional tuple holes keep
their commas. Every family compares against any certified expression competitor.
These are intrinsic kernel controls, not new compiler observations.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def typedParameter (n : Nat) : Syn .param := .param (arrayTypeFamily n) none (some "p")

def typedParameterWord (n : Nat) : List Tok := arrayTypeTokens n ++ idt "p"

theorem typedParameter_prec (n : Nat) : (typedParameter n).prec = true := by
  have hall : (arrayTypeFamily n).all Syn.precNode = true := (Bool.and_eq_true_iff.mp (arrayTypeFamily_prec n)).2
  change (true && (true && (arrayTypeFamily n).all Syn.precNode)) = true
  rw [hall]
  rfl

theorem typedParameter_yield (n : Nat) (rest : List Choice) :
    (typedParameter n).yield rest = some ([typedParameterWord n], rest) := by
  change ((arrayTypeFamily n).yield rest).bind
    (fun r => some ([r.1.flatten ++ [] ++ idt "p"], r.2)) = _
  rw [arrayTypeFamily_yield]
  simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

def typedParameters (n : Nat) : Nat → Syn (.list .param)
  | 0 => .nil
  | m + 1 => .cons (typedParameter n) (typedParameters n m)

theorem typedParameters_prec (n m : Nat) : (typedParameters n m).prec = true := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hp : (typedParameter n).all Syn.precNode = true := (Bool.and_eq_true_iff.mp (typedParameter_prec n)).2
    have ht : (typedParameters n m).all Syn.precNode = true := (Bool.and_eq_true_iff.mp ih).2
    change (true && (true && (typedParameter n).all Syn.precNode && (typedParameters n m).all Syn.precNode)) = true
    rw [hp, ht]
    rfl

theorem typedParameters_yield (n m : Nat) (rest : List Choice) :
    (typedParameters n m).yield rest = some (List.replicate m (typedParameterWord n), rest) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change ((typedParameter n).yield rest).bind (fun r =>
      ((typedParameters n m).yield r.2).bind (fun s => some (r.1.flatten :: s.1, s.2))) = _
    rw [typedParameter_yield]
    simp only [Option.bind_some]
    rw [ih]
    simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil, List.replicate_succ]

def functionReturns (n m : Nat) (enabled : Bool) : Syn (.list .param) :=
  if enabled then typedParameters n (m + 1) else .nil

def functionReturnWords (n m : Nat) (enabled : Bool) : List (List Tok) :=
  if enabled then List.replicate (m + 1) (typedParameterWord n) else []

theorem functionReturns_prec (n m : Nat) (enabled : Bool) : (functionReturns n m enabled).prec = true := by
  cases enabled with
  | false => rfl
  | true => exact typedParameters_prec n (m + 1)

theorem functionReturns_yield (n m : Nat) (enabled : Bool) (rest : List Choice) :
    (functionReturns n m enabled).yield rest = some (functionReturnWords n m enabled, rest) := by
  cases enabled with
  | false => rfl
  | true => exact typedParameters_yield n (m + 1) rest

def functionOrder (swap : Bool) : List Slot := if swap then [.mutab, .vis] else [.vis, .mutab]

def functionAttrs (swap : Bool) : List Tok := if swap then [.kw .view, .kw .external] else [.kw .external, .kw .view]

def functionTypeFamily (n m : Nat) (returns : Bool) : Syn .typeName :=
  .fnType (typedParameters n m) (some .external) (some .view) (functionReturns n m returns)

def functionTypeWord (n m : Nat) (returns swap : Bool) : List Tok :=
  tk .function ++ parens (commaSep (List.replicate m (typedParameterWord n))) ++ functionAttrs swap ++
    (if (functionReturnWords n m returns).isEmpty then [] else
      tk .returns ++ parens (commaSep (functionReturnWords n m returns)))

theorem functionTypeFamily_prec (n m : Nat) (returns : Bool) : (functionTypeFamily n m returns).prec = true := by
  have hp : (typedParameters n m).all Syn.precNode = true := (Bool.and_eq_true_iff.mp (typedParameters_prec n m)).2
  have hr : (functionReturns n m returns).all Syn.precNode = true := (Bool.and_eq_true_iff.mp (functionReturns_prec n m returns)).2
  change (true && (true && (typedParameters n m).all Syn.precNode && (functionReturns n m returns).all Syn.precNode)) = true
  rw [hp, hr]
  rfl

theorem functionTypeFamily_yield (n m : Nat) (returns swap : Bool) (rest : List Choice) :
    (functionTypeFamily n m returns).yield (.attrs (functionOrder swap) :: rest) =
      some ([functionTypeWord n m returns swap], rest) := by
  have ho : popAttrs (.attrs (functionOrder swap) :: rest) = some (functionOrder swap, rest) := rfl
  have ha : attrsP (single .vis (optToks Visibility.toks (some .external)) ++
      single .mutab (optToks Mutability.toks (some .view))) [] (functionOrder swap) rest =
      some (functionAttrs swap, rest) := by cases swap <;> rfl
  change (popAttrs (.attrs (functionOrder swap) :: rest)).bind (fun o =>
    ((typedParameters n m).yield o.2).bind (fun ps =>
      (attrsP (single .vis (optToks Visibility.toks (some .external)) ++
        single .mutab (optToks Mutability.toks (some .view))) [] o.1 ps.2).bind (fun attrs =>
        ((functionReturns n m returns).yield attrs.2).bind (fun rs =>
          some ([tk .function ++ parens (commaSep ps.1) ++ attrs.1 ++
            (if rs.1.isEmpty then [] else tk .returns ++ parens (commaSep rs.1))], rs.2))))) = _
  rw [ho]
  simp only [Option.bind_some]
  rw [typedParameters_yield]
  simp only [Option.bind_some]
  rw [ha]
  simp only [Option.bind_some]
  rw [functionReturns_yield]
  rfl

def wrappedFunctionExpr (n m : Nat) (returns : Bool) : Syn .expr :=
  .metaType (.array (functionTypeFamily n m returns) .none)

def wrappedFunctionWord (n m : Nat) (returns swap : Bool) : List Tok :=
  tk .type_ ++ parens (functionTypeWord n m returns swap ++ pu .lbrack ++ pu .rbrack)

theorem wrappedFunctionExpr_prec (n m : Nat) (returns : Bool) : (wrappedFunctionExpr n m returns).prec = true := by
  have hf : (functionTypeFamily n m returns).all Syn.precNode = true := (Bool.and_eq_true_iff.mp (functionTypeFamily_prec n m returns)).2
  have ha : (Syn.array (functionTypeFamily n m returns) Syn.none).all Syn.precNode = true :=
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨rfl, hf⟩, rfl⟩
  exact Bool.and_eq_true_iff.mpr ⟨rfl, Bool.and_eq_true_iff.mpr ⟨rfl, ha⟩⟩

theorem wrappedFunctionExpr_yield (n m : Nat) (returns swap : Bool) (rest : List Choice) :
    (wrappedFunctionExpr n m returns).yield (.attrs (functionOrder swap) :: rest) =
      some ([wrappedFunctionWord n m returns swap], rest) := by
  have arrayYield : (Syn.array (functionTypeFamily n m returns) Syn.none).yield
      (.attrs (functionOrder swap) :: rest) =
      some ([functionTypeWord n m returns swap ++ pu .lbrack ++ [] ++ pu .rbrack], rest) := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
      pair_pure_success_join (functionTypeFamily n m returns).yield (Syn.none (c := .expr)).yield
      (fun xs ys => [xs.flatten ++ pu .lbrack ++ ys.flatten ++ pu .rbrack])
      (.attrs (functionOrder swap) :: rest) rest rest [functionTypeWord n m returns swap] []
      (functionTypeFamily_yield n m returns swap rest) rfl
  change ((Syn.array (functionTypeFamily n m returns) Syn.none).yield
    (.attrs (functionOrder swap) :: rest)).bind (fun r => some ([tk .type_ ++ parens r.1.flatten], r.2)) = _
  rw [arrayYield]
  simp only [Option.bind_some, List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

theorem wrappedFunctionExpr_certified (n m : Nat) (returns swap : Bool) :
    (wrappedFunctionExpr n m returns).Derives (wrappedFunctionWord n m returns swap) ∧
      (wrappedFunctionExpr n m returns).prec = true :=
  ⟨⟨[.attrs (functionOrder swap)], (expr_toks_iff _ _ _).mpr (wrappedFunctionExpr_yield n m returns swap [])⟩,
    wrappedFunctionExpr_prec n m returns⟩

theorem wrappedFunctionExpr_any_competitor (n m : Nat) (returns swap : Bool) (other : Syn .expr)
    (derived : other.Derives (wrappedFunctionWord n m returns swap)) (prec : other.prec = true) :
    wrappedFunctionExpr n m returns = other :=
  certified_expression_yield_unique _ _ _ (wrappedFunctionExpr_certified n m returns swap).1
    (wrappedFunctionExpr_certified n m returns swap).2 derived prec

theorem direct_function_meta_refused (params returns : Syn (.list .param))
    (vis : Option Visibility) (mu : Option Mutability) : (Syn.metaType (.fnType params vis mu returns)).prec = false :=
  refused_of_node_false rfl

theorem attribute_orders_distinct : functionOrder true ≠ functionOrder false := by decide

def holeTuple (n : Nat) : Syn .expr := .tuple Syn.none (optionalHoles n)

def holeTupleWord (n : Nat) : List Tok := parens ((List.replicate n ([] : List Tok)).flatMap (pu .comma ++ ·))

theorem holeTuple_prec (n : Nat) : (holeTuple n).prec = true := by
  have hh : (optionalHoles n).all Syn.precNode = true := (Bool.and_eq_true_iff.mp (optionalHoles_prec n)).2
  change (true && (true && true && (optionalHoles n).all Syn.precNode)) = true
  rw [hh]
  rfl

theorem holeTuple_yield (n : Nat) (rest : List Choice) : (holeTuple n).yield rest = some ([holeTupleWord n], rest) := by
  exact pair_pure_success_join (Syn.none (c := .expr)).yield (optionalHoles n).yield
    (fun xs ys => [parens (xs.flatten ++ ys.flatMap (pu .comma ++ ·))]) rest rest rest []
    (List.replicate n []) rfl (optionalHoles_yield n rest)

theorem holeTuple_certified (n : Nat) : (holeTuple n).Derives (holeTupleWord n) ∧ (holeTuple n).prec = true :=
  ⟨⟨[], (expr_toks_iff _ _ _).mpr (holeTuple_yield n [])⟩, holeTuple_prec n⟩

theorem holeTuple_any_competitor (n : Nat) (other : Syn .expr)
    (derived : other.Derives (holeTupleWord n)) (prec : other.prec = true) : holeTuple n = other :=
  certified_expression_yield_unique _ _ _ (holeTuple_certified n).1 (holeTuple_certified n).2 derived prec

end Solidity.Frontend.ExpressionUniqueness
