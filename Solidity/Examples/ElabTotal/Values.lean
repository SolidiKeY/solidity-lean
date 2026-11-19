import Solidity.Syntax.Elab.Values

/-!
# Checks: the value rewrites' equations

The functions of `Syntax/Elab/Values.lean` checked here are total (other
functions of that file are still `partial`), so each unfolds by its named equations with no
`native_decide`: structural ones (`fnTyOfExpr`, `rawFnTyOfExpr?`, `bytesOf?`)
also reduce in the kernel (`rfl`), the well-founded one (`narrowPure`, through
`List.mapM`) by rewriting. The `#guard`s pin the compiled functions.
-/

namespace Solidity.Examples.ElabTotal.Values

open Solidity Semantics

variable [FreshNames]

private def C0 : Contract := { vars := [] }

/-! ### `bytesOf?`, `fnTyOfExpr`, `rawFnTyOfExpr?`: structural -/

/-- A conditional's `bytesN` is its branches' join, an assignment's its target's. -/
theorem bytesOf?_ternary_assign (C : Contract) (Γ : ECtx) (c l r b : RawExpr) :
    bytesOf? C Γ (.ternary c (.assign l r) b) = joinBytes (bytesOf? C Γ l) (bytesOf? C Γ b) := by
  rw [bytesOf?_ternary, bytesOf?_assign]

/-- No literal, tuple or `.length` is a `bytesN`, whatever the contract. -/
theorem bytesOf?_nones (C : Contract) (Γ : ECtx) (b : RawExpr) :
    bytesOf? C Γ (.binop .bor (.num 1) (.tuple [b])) = none ∧
      bytesOf? C Γ (.field b "length") = none := by
  refine ⟨?_, bytesOf?_field_length C Γ b⟩
  rw [bytesOf?_binop, (bytesOf?_other C Γ).1, (bytesOf?_other C Γ).2.2.2.2.2.2.2.2]
  rfl

/-- The kernel computes through the recursion: `~x` and `c ? x : y` reach the leaves. -/
example (C : Contract) (Γ : ECtx) (c : RawExpr) :
    bytesOf? C Γ (.unop .bnot (.ternary c (.num 1) (.bool true))) = none := rfl

/-- A conditional's function type is its first branch's, at any depth. -/
theorem fnTyOfExpr_ternary₂ (C : Contract) (Γ : ECtx) (c d a b e : RawExpr) :
    fnTyOfExpr C Γ (.ternary c (.ternary d a b) e) = fnTyOfExpr C Γ a := by
  rw [fnTyOfExpr_ternary, fnTyOfExpr_ternary]

/-- A call through a value with no callee has no function type. -/
theorem fnTyOfExpr_callValue_nil (C : Contract) (Γ : ECtx) :
    fnTyOfExpr C Γ (.call callValueName []) = none := by
  rw [fnTyOfExpr_call]; rfl

/-- The raw type of a conditional whose branches are the same expression is
that expression's. -/
theorem rawFnTyOfExpr?_ternary_self (C : Contract) (Γ : ECtx) (c a : RawExpr) :
    rawFnTyOfExpr? C Γ (.ternary c a a) = rawFnTyOfExpr? C Γ a := by
  rw [rawFnTyOfExpr?_ternary]
  cases rawFnTyOfExpr? C Γ a with
  | none => rfl
  | some t => simp [guard]

/-- `~(l ⊕= r)` has `l`'s `bytesN`; an element of a `bytesN` is a `bytes1`;
a conversion's is its type's; an external function's selector is a `bytes4`. -/
theorem bytesOf?_arms (C : Contract) (Γ : ECtx) (op : BinOp) (l r b i f : RawExpr) (g : String)
    (as : List RawExpr) (n : Nat) (rg : RawExpr × String)
    (hb : bytesOf? C Γ b = some n) (hg : bytesTy? g = some n) (hf : extMember? C Γ f = some rg) :
    bytesOf? C Γ (.unop .bnot (.opAssign op l r)) = bytesOf? C Γ l ∧
      bytesOf? C Γ (.index b i) = some 1 ∧ bytesOf? C Γ (.call g as) = some n ∧
      bytesOf? C Γ (.field f "selector") = some 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bytesOf?_unop_bnot, bytesOf?_opAssign]
  · rw [bytesOf?_index, hb]; rfl
  · rw [bytesOf?_call, hg]
  · rw [bytesOf?_field C Γ f "selector" (by decide), hf]; rfl

/-- A name no local binds is a `bytesN` when the contract's table marks it. -/
theorem bytesOf?_name_state (C : Contract) (x : String) :
    bytesOf? C [] (.name x) = lookupBy (x ++ "#bytes") C.widths := by
  rw [bytesOf?_name]; rfl

/-- A conditional's function type is its first branch's: a name's. -/
theorem fnTyOfExpr_ternary_name (C : Contract) (Γ : ECtx) (c b : RawExpr) (x : String) :
    fnTyOfExpr C Γ (.ternary c (.name x) b) =
      (fnTyOf? C Γ x).orElse fun _ =>
        if (lookupBy x Γ).isNone && fnInternal C x then
          (lookupBy x C.funs).bind (FunDecl.sigTy? C)
        else none := by
  rw [fnTyOfExpr_ternary, fnTyOfExpr_name]

/-- A literal is no member `r.g`: its function type is a place's marker, and there is none. -/
theorem fnTyOfExpr_bool (C : Contract) (Γ : ECtx) (b : Bool) :
    fnTyOfExpr C Γ (.bool b) = (do
      let (tb, k, .prim _) ← widthPath? C Γ (.bool b) | none
      (fnRow? tb k).map (canonFnTy (C.enums.map fun (e : Name × List Name) => e.1))) := by
  rw [fnTyOfExpr_other C Γ _ (by intro _ h; cases h) (by intro _ _ _ h; cases h)
    (by intro _ _ h; cases h)]
  rfl

/-- The raw type of a state name, of a call (its arguments are not read) and of a literal. -/
theorem rawFnTyOfExpr?_arms (C : Contract) (Γ : ECtx) (g : String) (as : List RawExpr) (b : Bool) :
    rawFnTyOfExpr? C [] (.name g) = fnRow? C.widths g ∧
      rawFnTyOfExpr? C Γ (.call g as) = rawFnTyOfExpr? C Γ (.call g []) ∧
      rawFnTyOfExpr? C Γ (.bool b) = (do
        let (tb, k, .prim _) ← widthPath? C Γ (.bool b) | none
        fnRow? tb k) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rawFnTyOfExpr?_name]; rfl
  · rw [rawFnTyOfExpr?_call, rawFnTyOfExpr?_call]
  · rw [rawFnTyOfExpr?_other C Γ _ (by intro _ h; cases h) (by intro _ _ _ h; cases h)
      (by intro _ _ h; cases h)]
    rfl

#guard bytesOf? C0 [] (.call "bytes4" [.num 1]) == some 4
#guard bytesOf? C0 [] (.binop .band (.call "bytes4" [.num 1]) (.call "bytes8" [.num 1])) == some 8
#guard bytesOf? C0 [] (.index (.call "bytes4" [.num 1]) (.num 0)) == some 1
#guard bytesOf? C0 [] (.call "keccak256" [.name "x"]) == some 32
#guard bytesOf? C0 [] (.field (.name "x") "length") == none
#guard fnTyOfExpr C0 [] (.call callValueName []) == none
#guard fnTyOfExpr C0 [] (.ternary (.bool true) (.name "f") (.name "g")) == fnTyOfExpr C0 [] (.name "f")
#guard rawFnTyOfExpr? C0 [] (.ternary (.bool true) (.name "f") (.name "g")) == none

/-! ### `narrowPure`: through `List.mapM` -/

/-- A call's arguments are rewritten left to right; leaves stay. -/
theorem narrowPure_call_leaves (C : Contract) (unc : Bool) (Γ : ECtx) (f x : String) (n : Nat) :
    narrowPure C unc Γ (.call f [.name x, .num n]) = pure (.call f [.name x, .num n]) := by
  rw [narrowPure_call, List.mapM_cons, List.mapM_cons, List.mapM_nil,
    (narrowPure_other C unc Γ).2.1, (narrowPure_other C unc Γ).1]
  rfl

/-- A member's base is rewritten, the member kept. -/
theorem narrowPure_field_leaf (C : Contract) (unc : Bool) (Γ : ECtx) (x f : String) :
    narrowPure C unc Γ (.field (.name x) f) = pure (.field (.name x) f) := by
  rw [narrowPure_field, (narrowPure_other C unc Γ).2.1]; rfl

/-- Every arm that only rebuilds its node, on leaves. -/
theorem narrowPure_rebuild (C : Contract) (unc : Bool) (Γ : ECtx) (x : String) (T : RawTy)
    (o : IncDec) (m : ModOp) (ns : List String) :
    narrowPure C unc Γ (.modular m (.incDec o (.name x)) (.newArr T (.name x))
        (.ternary (.name x) (.name x) (.named "f" ns [.name x]))) =
      pure (.modular m (.incDec o (.name x)) (.newArr T (.name x))
        (.ternary (.name x) (.name x) (.named "f" ns [.name x]))) := by
  rw [narrowPure_modular, narrowPure_incDec, narrowPure_newArr, narrowPure_ternary,
    narrowPure_named, List.mapM_cons, List.mapM_nil, (narrowPure_other C unc Γ).2.1]
  rfl

/-- An operator's node is wrapped (`narrowWrapNode`) after its operands; an
index is checked against a narrow mapping key first (`fitCheck`). -/
theorem narrowPure_wrapped (C : Contract) (unc : Bool) (Γ : ECtx) (op : BinOp) (u : UnOp)
    (x : String) (n : Nat) :
    narrowPure C unc Γ (.binop op (.name x) (.num n)) =
        narrowWrapNode C unc Γ (.binop op (.name x) (.num n)) ∧
      narrowPure C unc Γ (.unop u (.name x)) = narrowWrapNode C unc Γ (.unop u (.name x)) ∧
      narrowPure C unc Γ (.index (.name x) (.num n)) = (do
        if let some (tb, key, .ref (.mapping kp _)) := widthPath? C Γ (.name x) then
          if let some w := lookupBy (key ++ "{}") tb then fitCheck C Γ kp w (.num n)
        pure (.index (.name x) (.num n))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [narrowPure_binop, (narrowPure_other C unc Γ).2.1, (narrowPure_other C unc Γ).1]; rfl
  · rw [narrowPure_unop, (narrowPure_other C unc Γ).2.1]; rfl
  · rw [narrowPure_index, (narrowPure_other C unc Γ).2.1, (narrowPure_other C unc Γ).1]; rfl

private def shown (r : Except String RawExpr) : String :=
  match r with
  | .ok e => e.toStr
  | .error m => "error: " ++ m

#guard shown (narrowPure C0 false [] (.call "f" [.name "x", .num 1])) == "f(x, 1)"
-- `~a` at `uint8` is `255 -% a`; a literal out of the type's range is refused
#guard shown (narrowPure C0 false [("a", .val .uint 8 [])] (.unop .bnot (.name "a"))) ==
  shown (.ok (.binop .subW (.num 255) (.name "a")))
#guard (shown (narrowPure C0 false [("a", .val .uint 8 [])]
  (.index (.name "m") (.binop .add (.name "a") (.num 300))))).startsWith "error: 300 does not fit"

end Solidity.Examples.ElabTotal.Values
