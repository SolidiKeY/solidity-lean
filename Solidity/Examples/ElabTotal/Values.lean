import Solidity.Syntax.Elab.Values

/-!
# Checks: the value rewrites' equations

The functions of `Syntax/Elab/Values.lean` checked here are total (`abiTyExpr?`
and `abiFnType` are still `partial`), so each unfolds by its named equations with no
`native_decide`: structural ones (`fnTyOfExpr`, `rawFnTyOfExpr?`, `bytesOf?`)
also reduce in the kernel (`rfl`), the well-founded ones (`narrowPure`, the
three mutual `narrow…?`, `abiTyName`, `bytesPure`, `fnPure`) by rewriting. The `#guard`s pin the
compiled functions.
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

/-! ### `narrowWholeUse?`, `narrowWholeAt?`, `narrowBase?`: mutual, by `(sizeOf e, tag)` -/

/-- A literal names no place, at any of the three. -/
theorem narrow_num (C : Contract) (Γ : ECtx) (n : Nat) :
    narrowWholeUse? C Γ (.num n) = none ∧ narrowBase? C Γ (.num n) = none ∧
      narrowWholeAt? C Γ (.num n) = none := by
  have hu := (narrowWholeUse?_other C Γ).1 n
  have hb : narrowBase? C Γ (.num n) = none := by
    rw [narrowBase?_other C Γ _ (by intro _ _ h; cases h) (by intro _ _ h; cases h)
      (by intro _ h; cases h), hu]
  exact ⟨hu, hb, by rw [narrowWholeAt?_other C Γ _ (by intro _ _ _ h; cases h), hb]⟩

/-- Operators, tuples, constructors and array literals of literals name no place. -/
theorem narrowWholeUse?_literals (C : Contract) (Γ : ECtx) (op : BinOp) (u : UnOp) (o : IncDec)
    (m : ModOp) (T : RawTy) (b : Bool) (k : EnvKey) (f : String) (ns : List String) :
    narrowWholeUse? C Γ (.binop op (.unop u (.num 1)) (.incDec o (.newArr T (.bool b)))) = none ∧
      narrowWholeUse? C Γ (.ternary (.env k) (.opAssign op (.num 1) (.num 2))
        (.tuple [.num 1])) = none ∧
      narrowWholeUse? C Γ (.modular m (.num 1) (.num 2) (.num 3)) = none ∧
      narrowWholeUse? C Γ (.named f ns []) = none ∧
      narrowWholeUse? C Γ (.call "#array" [.num 1]) = none ∧
      narrowWholeUse? C Γ (.assign (.num 1) (.num 2)) = none := by
  have hn := fun n => narrow_num C Γ n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [narrowWholeUse?_binop, narrowWholeUse?_unop, narrowWholeUse?_incDec,
      narrowWholeUse?_newArr, (hn 1).1, (narrowWholeUse?_other C Γ).2.1]; rfl
  · rw [narrowWholeUse?_ternary, narrowWholeUse?_opAssign, narrowWholeUse?_tuple,
      (narrowWholeUse?_other C Γ).2.2, (hn 1).1, (hn 2).1]
    simp only [List.findSome?, (hn 1).1]; rfl
  · rw [narrowWholeUse?_modular]; simp only [List.findSome?, (hn 1).1, (hn 2).1, (hn 3).1]
  · rw [narrowWholeUse?_named]; simp only [List.findSome?, ite_self]
  · rw [narrowWholeUse?_call_array]; simp only [List.findSome?, (hn 1).2.2]
  · rw [narrowWholeUse?_assign, (hn 1).1, (hn 2).1, (hn 1).2.2, (hn 2).2.2]
    simp only [Option.orElse, ite_self]

/-- A call with no argument names no place. -/
theorem narrowWholeUse?_call_nil (C : Contract) (Γ : ECtx) (f : String) (hf : f ≠ "#array") :
    narrowWholeUse? C Γ (.call f []) = none := by
  rw [narrowWholeUse?_call C Γ f [] hf]
  simp only [List.findSome?, List.zipIdx_nil, ite_self]

/-- A name is itself when it has narrow positions; a member or an element of
a name is itself or nothing (a name is no base). -/
theorem narrowWholeUse?_places (C : Contract) (Γ : ECtx) (u : UnOp) (x f : String) (n : Nat) :
    narrowWholeUse? C Γ (.unop u (.name x)) =
        (if narrowWhole C Γ (.name x) then some (.name x) else none) ∧
      narrowWholeUse? C Γ (.field (.name x) f) =
        (if narrowWhole C Γ (.field (.name x) f) then some (.field (.name x) f) else none) ∧
      narrowWholeUse? C Γ (.index (.name x) (.num n)) =
        (if narrowWhole C Γ (.index (.name x) (.num n)) then some (.index (.name x) (.num n))
          else none) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [narrowWholeUse?_unop, narrowWholeUse?_name]
  · rw [narrowWholeUse?_field, narrowBase?_name]
  · rw [narrowWholeUse?_index, narrowBase?_name, (narrow_num C Γ n).1]; rfl

/-- A conditional whose branches' shapes differ is refused whole; a base's
own indices are all that is searched. -/
theorem narrowWholeAt?_base (C : Contract) (Γ : ECtx) (c a b : RawExpr) (x f : String) (n : Nat)
    (h : sameShape (exprShape C Γ a) (exprShape C Γ b) = false) :
    narrowWholeAt? C Γ (.ternary c a b) = some (.ternary c a b) ∧
      narrowBase? C Γ (.index (.field (.name x) f) (.num n)) = none := by
  refine ⟨?_, ?_⟩
  · rw [narrowWholeAt?_ternary, h]; rfl
  · rw [narrowBase?_index, narrowBase?_field, narrowBase?_name, (narrow_num C Γ n).1]; rfl

#guard narrowWholeUse? C0 [("a", .mem (.array .uint) [("[]", 8)])] (.unop .neg (.name "a")) matches
  some (.name "a")
#guard (narrowWholeUse? C0 [("a", .mem (.array .uint) [("[]", 8)])]
  (.index (.name "a") (.num 0))).isNone
#guard (narrowWholeUse? C0 [("a", .mem (.array .uint) [("[]", 8)])]
  (.call "keccak256" [.name "a"])).isNone
#guard (narrowWholeAt? C0 [] (.ternary (.bool true) (.num 1) (.num 2))).isNone

/-! ### `abiTyName`: by the type's rank (`tyRank`), a struct's members below it -/

omit [FreshNames] in
/-- The seven arms: scalars, arrays (the element's key is `k[]`), a struct as
the tuple of its members, no mapping. -/
theorem abiTyName_arms (ws : List (String × Nat)) (k : String) (n w : Nat) (K : PrimTy) (V : Ty)
    (s : Name) (ha : lookupBy (k ++ "#address") ws = some w)
    (hb : (lookupBy (k ++ "[]#bytes") ws == some 1) = false) (hs : structDef s = []) :
    abiTyName ws k (.ref (.fixed (.prim .bool) n)) = some s!"{"bool"}[{n}]" ∧
      abiTyName [] k (.prim .int) = some s!"int{256}" ∧
      abiTyName ws k (.prim .uint) = some "address" ∧
      abiTyName ws k (.ref (.array (.ref (.mapping K V)))) = none ∧
      abiTyName ws k (.ref (.struct s)) = some "()" := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [abiTyName_fixed, abiTyName_bool]; rfl
  · rw [abiTyName_int]; rfl
  · rw [abiTyName_uint, ha]; rfl
  · rw [abiTyName_array, abiTyName_mapping, hb]; rfl
  · rw [abiTyName_struct, hs]; rfl

#guard abiTyName [] "x" (.ref (.struct "Token")) == some "(uint256)"
#guard abiTyName [("x[]", 8)] "x" (.ref (.array (.prim .uint))) == some "uint8[]"
#guard abiTyName [] "x" (.ref (.struct "Wallet")) == none

/-! ### `bytesPure`: by `sizeOf`, through `List.mapM` -/

/-- Every arm that only rebuilds its node, on leaves; an array literal is not entered. -/
theorem bytesPure_rebuild (C : Contract) (Γ : ECtx) (x : String) (T : RawTy) (o : IncDec)
    (m : ModOp) (ns : List String) (as : List RawExpr) :
    bytesPure C Γ (.modular m (.incDec o (.name x)) (.newArr T (.name x))
        (.named "f" ns [.tuple [.name x], .field (.name x) "f", .call "#array" as])) =
      pure (.modular m (.incDec o (.name x)) (.newArr T (.name x))
        (.named "f" ns [.tuple [.name x], .field (.name x) "f", .call "#array" as])) := by
  rw [bytesPure_modular, bytesPure_incDec, bytesPure_newArr, bytesPure_named, List.mapM_cons,
    List.mapM_cons, List.mapM_cons, List.mapM_nil, bytesPure_tuple, List.mapM_cons, List.mapM_nil,
    bytesPure_field C Γ _ "f" (by decide), bytesPure_call_array, (bytesPure_other C Γ).2.1]
  rfl

/-- Operators of literals: no operand is a `bytesN`, so nothing is converted. -/
theorem bytesPure_literals (C : Contract) (Γ : ECtx) (c : Bool) :
    bytesPure C Γ (.binop .add (.num 1) (.num 2)) = pure (.binop .add (.num 1) (.num 2)) ∧
      bytesPure C Γ (.unop .neg (.num 1)) = pure (.unop .neg (.num 1)) ∧
      bytesPure C Γ (.ternary (.bool c) (.num 1) (.num 2)) =
        pure (.ternary (.bool c) (.num 1) (.num 2)) ∧
      bytesPure C Γ (.assign (.num 1) (.num 2)) = pure (.assign (.num 1) (.num 2)) ∧
      bytesPure C Γ (.opAssign .add (.num 1) (.num 2)) =
        pure (.opAssign .add (.num 1) (.num 2)) := by
  have hn := (bytesPure_other C Γ).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [bytesPure_binop, hn, hn]; rfl
  · rw [bytesPure_unop, hn]; rfl
  · rw [bytesPure_ternary, (bytesPure_other C Γ).2.2.1, hn, hn]; rfl
  · rw [bytesPure_assign, hn, hn]; rfl
  · rw [bytesPure_opAssign, hn, hn]; rfl

/-- `x.length` and `x[k]` of a `bytesN` name: the literal `N`, the byte `k` (`bytesAt`). -/
theorem bytesPure_fixed (C : Contract) (Γ : ECtx) (x : String) (n k : Nat)
    (hb : bytesOf? C Γ (.name x) = some n) :
    bytesPure C Γ (.field (.name x) "length") = pure (.num n) ∧
      bytesPure C Γ (.index (.name x) (.num k)) = bytesAt n (.name x) (.num k) := by
  have hx : (RawExpr.name x).hasIncDec = false := by simp [RawExpr.hasIncDec, RawExpr.any]
  have hk : (RawExpr.num k).hasIncDec = false := by simp [RawExpr.hasIncDec, RawExpr.any]
  refine ⟨?_, ?_⟩
  · rw [bytesPure_field_length, hb]; simp only [hx]; rfl
  · rw [bytesPure_index, (bytesPure_other C Γ).2.1, (bytesPure_other C Γ).1, hb]
    simp only [hk, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_pure]

/-- A prefix witness that is no `bytes(…)` conversion is rewritten as it stands. -/
theorem bytesPure_backing_num (C : Contract) (Γ : ECtx) (n : Nat) :
    bytesPure C Γ (match RawExpr.num n with
      | .call "bytes" [value] => value
      | value => value) = pure (.num n) := by
  exact (bytesPure_backing C Γ (.num n)).symm.trans ((bytesPure_other C Γ).1 n)

/-- A fixed byte prefix whose name carries no width is refused before its argument is read. -/
theorem bytesPure_prefix_width (C : Contract) (Γ : ECtx) (f : String) (as : List RawExpr)
    (hf : f ≠ "#array") (hp : (f.startsWith "#bytesPrefix" && (lookupBy f C.funs).isNone) = true)
    (hn : (f.drop 12).toNat? = none) :
    bytesPure C Γ (.call f as) = throw "a fixed byte prefix needs its width" := by
  rw [bytesPure_call C Γ f as hf, if_pos hp, hn]
  rfl

#guard shown (bytesPure C0 [] (.field (.call "bytes4" [.num 1]) "length")) == "4"
#guard shown (bytesPure C0 [] (.call "#array" [.field (.call "bytes4" [.num 1]) "length"])) ==
  shown (.ok (.call "#array" [.field (.call "bytes4" [.num 1]) "length"]))
#guard (shown (bytesPure C0 [] (.index (.call "bytes4" [.name "x"]) (.num 9)))).startsWith
  "error: index 9 out of range"
#guard shown (bytesPure C0 [] (.call "#bytesPrefix" [.name "x"])) ==
  "error: a fixed byte prefix needs its width"

/-! ### `fnPure`: by the node count (`RawExpr.nodes`) -/

/-- Every arm that only rebuilds its node, on leaves. -/
theorem fnPure_rebuild (C : Contract) (Γ : ECtx) (x : String) (T : RawTy) (o : IncDec)
    (m : ModOp) (u : UnOp) (op : BinOp) (ns : List String) :
    fnPure C Γ (.modular m (.incDec o (.name x)) (.newArr T (.name x))
        (.ternary (.name x) (.index (.name x) (.num 1))
          (.named "f" ns [.tuple [.name x], .unop u (.binop op (.name x) (.num 1))]))) =
      pure (.modular m (.incDec o (.name x)) (.newArr T (.name x))
        (.ternary (.name x) (.index (.name x) (.num 1))
          (.named "f" ns [.tuple [.name x], .unop u (.binop op (.name x) (.num 1))]))) := by
  rw [fnPure_modular, fnPure_incDec, fnPure_newArr, fnPure_ternary, fnPure_index, fnPure_named,
    List.mapM_cons, List.mapM_cons, List.mapM_nil, fnPure_tuple, List.mapM_cons, List.mapM_nil,
    fnPure_unop, fnPure_binop, (fnPure_other C Γ).2.1, (fnPure_other C Γ).1]
  rfl

/-- An assignment's target is not entered; a call with no argument is itself. -/
theorem fnPure_targets (C : Contract) (Γ : ECtx) (l : RawExpr) (op : BinOp) (o : IncDec)
    (f : String) :
    fnPure C Γ (.assign l (.num 1)) = pure (.assign l (.num 1)) ∧
      fnPure C Γ (.opAssign op l (.num 1)) = pure (.opAssign op l (.num 1)) ∧
      fnPure C Γ (.incDec o (.call f [])) = pure (.incDec o (.call f [])) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [fnPure_assign, (fnPure_other C Γ).1]; rfl
  · rw [fnPure_opAssign, (fnPure_other C Γ).1]; rfl
  · rw [fnPure_incDec, fnPure_call_nil]; rfl

/-- The first arm's four branches on one literal argument: `abi.encodeCall`
wants a function and a tuple; an encoder, a call through a value and any
other call rebuild the call. -/
theorem fnPure_call_branches (C : Contract) (Γ : ECtx) (f : String) :
    ((f == "abi.encodeCall") = true → fnPure C Γ (.call f [.num 1]) =
        throw "abi.encodeCall takes a function and an argument tuple") ∧
      (¬(f == "abi.encodeCall") = true →
        ¬(encodeBuiltin f && (lookupBy f C.funs).isNone) = true →
        fnPure C Γ (.call f [.num 1]) = pure (.call f [.num 1])) := by
  refine ⟨fun hf => ?_, fun hf hb => ?_⟩
  · rw [fnPure_encodeCall C Γ f _ _ hf, (fnPure_other C Γ).1]; rfl
  · by_cases hv : (f == callValueName) = true
    · rw [fnPure_callValue C Γ f _ _ hf hb hv, (fnPure_other C Γ).1]; rfl
    · rw [fnPure_call_cons C Γ f _ _ hf hb hv, (fnPure_other C Γ).1]; rfl

/-- An encoder's argument that is no function value is lowered and kept. -/
theorem fnPure_encodeBuiltin_num (C : Contract) (Γ : ECtx) (f : String)
    (hf : ¬(f == "abi.encodeCall") = true)
    (hb : (encodeBuiltin f && (lookupBy f C.funs).isNone) = true)
    (hr : rawFnTyOfExpr? C Γ (.num 1) = none) :
    fnPure C Γ (.call f [.num 1]) = pure (.call f [.num 1]) := by
  rw [fnPure_encodeBuiltin C Γ f _ _ hf hb, List.mapM_cons, List.mapM_nil,
    (fnPure_other C Γ).1, hr]
  rfl

/-- A member that is neither `.selector` nor `.address`, of no external
function: the base is lowered, the member kept. -/
theorem fnPure_field_plain (C : Contract) (Γ : ECtx) (x m : String)
    (hm : (m == "selector" || m == "address") = false)
    (he : extMember? C Γ (.field (.name x) m) = none) :
    fnPure C Γ (.field (.name x) m) = pure (.field (.name x) m) := by
  rw [fnPure_field, if_neg (by rw [hm]; exact Bool.false_ne_true), extMember?_match_eq, he,
    (fnPure_other C Γ).2.1]
  rfl

/-- The member arm's test of an external function type is the pattern it
replaced (`fnParts?_any_eq`): on a type that is no function's, the other branch. -/
example (ty : String) (h : fnParts? ty = none) :
    (if (fnParts? ty).any (·.2.2) then 1 else 0) = 0 := by
  rw [fnParts?_any_eq, h]

#guard shown (fnPure C0 [] (.call "f" [.field (.name "a") "b", .num 2])) == "f(a.b, 2)"
#guard shown (fnPure C0 [] (.call "abi.encodeCall" [.num 1])) ==
  "error: abi.encodeCall takes a function and an argument tuple"
#guard shown (fnPure C0 [] (.call "abi.encodeCall" [.name "g", .tuple [.num 1]])) ==
  "error: abi.encodeCall: the function's ABI parameter types are unavailable"
#guard shown (fnPure C0 [] (.call "abi.encode" [.num 1, .name "a"])) == "abi.encode(1, a)"

end Solidity.Examples.ElabTotal.Values
