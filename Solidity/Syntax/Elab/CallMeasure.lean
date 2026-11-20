import Solidity.Syntax.Elab.Measure

/-! Weighted expression heights and local call-expansion decrease lemmas. -/

namespace Solidity.ElabHoist
/-- Constant folding preserves the input or produces a literal. -/
theorem foldConst_same_or_lit (e out : RawExpr) (h : e.foldConst = .ok out) :
    out = e ∨ out.isLit = true := by
  unfold RawExpr.foldConst at h
  split at h
  · cases h; exact Or.inl rfl
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h; exact Or.inr rfl
      · cases h; exact Or.inr rfl
end Solidity.ElabHoist

namespace Solidity.ElabCallHeight
open Semantics

/-- Weight reserved for the direct expression expansion of selected builtins. -/
def cost : String → Nat
  | "#callValue" => 9
  | "erc7201" => 8
  | "ecrecover" => 2
  | "#bytesIndex" => 6
  | "#sliceIndex" => 3
  | "#sliceAt" => 6
  | "#sliceLength" => 2
  | "#sliceDecode" => 5
  | "abi.decode" => 2
  | "abi.encodeWithSignature" => 3
  | "abi.encodeCall" => 4
  | f => if f.startsWith "#bytesPrefix" then 2 else 1

private theorem cost_callValue : cost callValueName = 9 := rfl

private theorem cost_uint : cost "uint256" = 1 := rfl
private theorem cost_hash : cost "keccak256" = 1 := rfl
private theorem cost_encode : cost "abi.encode" = 1 := rfl
private theorem cost_erc : cost "erc7201" = 8 := rfl
private theorem cost_recover : cost "ecrecover" = 2 := rfl
private theorem cost_decode : cost "abi.decode" = 2 := rfl
private theorem cost_internal : cost "#abiDecode" = 1 := rfl
private theorem cost_encodeCall : cost "abi.encodeCall" = 4 := rfl
private theorem cost_signature : cost "abi.encodeWithSignature" = 3 := rfl

mutual
/-- Weighted expression height; duplicated arguments do not increase a list maximum. -/
def height : RawExpr → Nat
  | .field a _ | .unop _ a | .incDec _ a | .newArr _ a => 1 + height a
  | .index a b | .binop _ a b | .assign a b | .opAssign _ a b => 1 + max (height a) (height b)
  | .ternary c a b | .modular _ c a b => 1 + max (height c) (max (height a) (height b))
  | .call f args => cost f + heights args
  | .named f _ args => 2 + cost f + heights args
  | .tuple args => 1 + heights args
  | .num _ | .name _ | .bool _ | .env _ => 1
/-- The maximum weighted height of arguments. -/
def heights : List RawExpr → Nat
  | [] => 0
  | a :: args => max (height a) (heights args)
end

private theorem cost_pos (f : String) : 0 < cost f := by
  unfold cost
  split <;> first | decide | (split <;> decide)

/-- Every expression has positive height. -/
theorem height_pos (e : RawExpr) : 0 < height e := by
  cases e <;> simp only [height] <;> try omega
  rename_i f args
  have := cost_pos f
  omega

/-- An argument is bounded by the list maximum, regardless of duplicates. -/
theorem mem_height_le {a : RawExpr} {args : List RawExpr} (h : a ∈ args) :
    height a ≤ heights args := by
  induction args with
  | nil => cases h
  | cons b args ih =>
    simp only [List.mem_cons] at h
    simp only [heights]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

private theorem heights_le {args : List RawExpr} {n : Nat}
    (h : ∀ a, a ∈ args → height a ≤ n) : heights args ≤ n := by
  induction args with
  | nil => simp only [heights]; omega
  | cons b args ih =>
    have hb := h b (List.mem_cons.mpr (Or.inl rfl))
    have ht := ih (fun a ha => h a (List.mem_cons.mpr (Or.inr ha)))
    simp only [heights]
    omega

/-- Named-argument reordering decreases height even with duplicates, truncated
zips and the arm's numeric default for an absent lookup. -/
theorem named_request_lt (C : Contract) (f : String) (ns : List String) (args : List RawExpr) :
    height (.call f ((C.structFields f).map fun p =>
      (lookupBy p.1 (ns.zip args)).getD (.num 0))) < height (.named f ns args) := by
  have hb : heights ((C.structFields f).map fun p =>
      (lookupBy p.1 (ns.zip args)).getD (.num 0)) ≤ max 1 (heights args) := by
    apply heights_le
    intro a ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
    cases hl : lookupBy p.1 (ns.zip args) with
    | none => simp only [Option.getD_none, height]; omega
    | some e =>
      have hm := mem_height_le (List.of_mem_zip (lookupBy_eq_some_mem hl)).2
      simp only [Option.getD_some]
      omega
  simp only [height]
  omega

/-- The exact ERC expression expansion decreases this local measure. -/
theorem erc_expansion_lt (a : RawExpr) :
    let first : RawExpr := .call "uint256" [.call "keccak256" [a]]
    let before : RawExpr := .binop .subW first (.num 1)
    let second : RawExpr := .call "uint256" [.call "keccak256" [.call "abi.encode" [before]]]
    height (.binop .band second (.num (2 ^ 256 - 256))) < height (.call "erc7201" [a]) := by
  have := height_pos a
  simp only [height, heights, cost_uint, cost_hash, cost_encode, cost_erc]
  omega

/-- ecrecover's four-argument ABI-encoding request is smaller. -/
theorem recover_encoding_lt (a b c d : RawExpr) :
    height (.call "abi.encode" [a,b,c,d]) < height (.call "ecrecover" [a,b,c,d]) := by
  simp only [height, cost_encode, cost_recover]
  omega

/-- Adding the decoder's two numeric indices still decreases height. -/
theorem decode_request_lt (C : Contract) (b T : RawExpr) :
    height (.call abiDecodeName [b,T,.num 0,.num (decodeHeadWords C T)]) <
      height (.call "abi.decode" [b,T]) := by
  have := height_pos b
  have := height_pos T
  simp only [height, heights, abiDecodeName, cost_decode, cost_internal]
  omega

/-- A computed signature selector is smaller than its source encoder call. -/
theorem signature_selector_lt (s : RawExpr) (rest : List RawExpr) :
    height (.binop .shr (.call "keccak256" [s]) (.num 224)) <
      height (.call "abi.encodeWithSignature" (s :: rest)) := by
  have := height_pos s
  simp only [height, heights, cost_hash, cost_signature]
  omega

/-- Extracting a selector from an external function value decreases height. -/
theorem function_selector_lt (g : String) (t : RawExpr) :
    height (.binop .sub (.name g)
      (.binop .mul (.binop .div (.name g) (.num selShift)) (.num selShift))) <
      height (.call "abi.encodeCall" [.name g,t]) := by
  simp only [height, heights, cost_encodeCall]
  omega

private theorem literal_height_le (e : RawExpr) (h : e.isLit = true) : height e ≤ 2 := by
  cases e <;> simp only [RawExpr.isLit, Bool.false_eq_true] at h
  · simp only [height]; omega
  · rename_i op a
    cases op <;> cases a <;> simp_all [height]

/-- Constant folding does not increase the local weighted height. -/
theorem foldConst_height_le (e out : RawExpr) (h : e.foldConst = .ok out) :
    height out ≤ height e := by
  have hb : height out ≤ height e ∨ height out ≤ 2 := by
    rcases ElabHoist.foldConst_same_or_lit e out h with he | hl
    · exact Or.inl (he ▸ Nat.le_refl _)
    · exact Or.inr (literal_height_le out hl)
  cases e with
  | unop op a =>
    have := height_pos a
    simp only [height] at *
    omega
  | binop op a b =>
    have := height_pos a
    simp only [height] at *
    omega
  | num n =>
    simp [RawExpr.foldConst, RawExpr.constRat?] at h
    cases h
    exact Nat.le_refl _
  | _ =>
    simp [RawExpr.foldConst, RawExpr.constRat?] at h
    cases h
    exact Nat.le_refl _

/-- Every argument is strictly below an ordinary call in this measure. -/
theorem argument_lt_call (f : String) {a : RawExpr} {args : List RawExpr} (h : a ∈ args) :
    height a < height (.call f args) := by
  have := mem_height_le h
  have := cost_pos f
  simp only [height]
  omega

/-- A selector actually emitted by the helper is below its source call. -/
theorem selector_height_lt (C : Contract) (Γ : ECtx) (f : String) (args : List RawExpr)
    (sel : RawExpr) (rest : List RawExpr)
    (h : encodeSelector? C Γ f args = .ok (some (sel,rest))) :
    height sel < height (.call f args) := by
  unfold encodeSelector? at h
  split at h
  · cases h
    exact argument_lt_call _ (List.mem_cons.mpr (Or.inl rfl))
  · split at h
    · cases h
      simp only [height, cost_signature]
      omega
    · cases h
      exact signature_selector_lt _ _
  · simp only [pure, Except.pure, bind, Except.bind] at h
    repeat' first
    | split at h
    | (cases h <;> first
        | exact function_selector_lt _ _
        | (simp only [height, cost_encodeCall]; omega))
  · cases h

private theorem tuple_arg_height_le (t a : RawExpr)
    (h : a ∈ (match t with | .tuple args => args | x => [x])) : height a ≤ height t := by
  cases t <;> try (simp only [List.mem_singleton] at h; subst a; exact Nat.le_refl _)
  rename_i args
  change a ∈ args at h
  have := mem_height_le h
  simp only [height]
  omega

private theorem second_tuple_arg_lt (g t a : RawExpr)
    (h : a ∈ (match t with | .tuple args => args | x => [x])) :
    height a < height (.call "abi.encodeCall" [g,t]) := by
  have ha := tuple_arg_height_le t a h
  have ht := argument_lt_call "abi.encodeCall" (a := t) (args := [g,t])
    (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  omega

/-- Every remaining argument actually emitted by selector extraction is smaller. -/
theorem selector_args_height_lt (C : Contract) (Γ : ECtx) (f : String) (args : List RawExpr)
    (sel : RawExpr) (rest : List RawExpr)
    (h : encodeSelector? C Γ f args = .ok (some (sel,rest))) :
    ∀ a, a ∈ rest → height a < height (.call f args) := by
  unfold encodeSelector? at h
  split at h
  · cases h
    intro a ha
    exact argument_lt_call _ (List.mem_cons.mpr (Or.inr ha))
  · split at h <;> cases h <;> intro a ha
    all_goals exact argument_lt_call _ (List.mem_cons.mpr (Or.inr ha))
  · simp only [pure, Except.pure, bind, Except.bind] at h
    repeat' first
    | split at h
    | cases h
    all_goals
      intro a ha
      first
      | exact second_tuple_arg_lt _ _ _ ha
      | simp only [List.mem_singleton] at ha
        subst a
        exact argument_lt_call _ (List.mem_cons.mpr
          (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  · cases h

/-- Removing the encoder's optional one-argument byte marker does not grow height. -/
theorem unmark_height_le (a : RawExpr) :
    height (match a with
      | .call g [x] => if (abiBytesMark? g).isSome then x else a
      | _ => a) ≤ height a := by
  split
  · rename_i g x
    split
    · have := cost_pos g
      simp only [height, heights]
      omega
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- Literal bytes are skipped during argument hoisting using the existing numeric placeholder. -/
theorem bytes_placeholder_height_le (a : RawExpr) :
    height (if a.bytesLit?.isSome then .num 0 else a) ≤ height a := by
  split
  · have := height_pos a
    simp only [height]
    omega
  · exact Nat.le_refl _

/-- Marker stripping and placeholder insertion preserve any strict input bound. -/
theorem encoding_inputs_lt (args : List RawExpr) (n : Nat)
    (bound : ∀ e, e ∈ args → height e < n) (a : RawExpr)
    (h : a ∈ ((args.map fun e => match e with
      | .call g [x] => if (abiBytesMark? g).isSome then x else e
      | _ => e).map fun e => if e.bytesLit?.isSome then .num 0 else e)) :
    height a < n := by
  obtain ⟨b, hbm, hba⟩ := List.mem_map.mp h
  obtain ⟨e, hem, heb⟩ := List.mem_map.mp hbm
  have hp := bytes_placeholder_height_le b
  have hu := unmark_height_le e
  rw [heb] at hu
  rw [← hba]
  exact Nat.lt_of_le_of_lt hp (Nat.lt_of_le_of_lt hu (bound e hem))

/-- Each transformed argument sent to the hoister is below the source call. -/
theorem encoding_arg_height_lt (f : String) (args : List RawExpr) (a : RawExpr)
    (h : a ∈ ((args.map fun e => match e with
      | .call g [x] => if (abiBytesMark? g).isSome then x else e
      | _ => e).map fun e => if e.bytesLit?.isSome then .num 0 else e)) :
    height a < height (.call f args) :=
  encoding_inputs_lt args _ (fun _ he => argument_lt_call f he) a h

/-- The exact selector call's marker-stripped selector decreases. -/
theorem selector_input_lt (C : Contract) (Γ : ECtx) (f : String) (args : List RawExpr)
    (sel : RawExpr) (rest : List RawExpr)
    (h : encodeSelector? C Γ f args = .ok (some (sel,rest))) :
    height ((fun e : RawExpr => match e with
      | .call g [x] => if (abiBytesMark? g).isSome then x else e
      | _ => e) sel) < height (.call f args) :=
  Nat.lt_of_le_of_lt (unmark_height_le sel) (selector_height_lt C Γ f args sel rest h)

/-- The actual selector remainder, transformed exactly as in hoistWith, decreases. -/
theorem selector_encoding_inputs_lt (C : Contract) (Γ : ECtx) (f : String)
    (args : List RawExpr) (sel : RawExpr) (rest : List RawExpr)
    (hs : encodeSelector? C Γ f args = .ok (some (sel,rest))) (a : RawExpr)
    (ha : a ∈ ((rest.map fun e => match e with
      | .call g [x] => if (abiBytesMark? g).isSome then x else e
      | _ => e).map fun e => if e.bytesLit?.isSome then .num 0 else e)) :
    height a < height (.call f args) :=
  encoding_inputs_lt rest _ (selector_args_height_lt C Γ f args sel rest hs) a ha

/-- Evaluating an encodeCall receiver is below its original source call. -/
theorem selector_receiver_lt (r t : RawExpr) (field : String) :
    height r < height (.call "abi.encodeCall" [.field r field, t]) := by
  have hf := argument_lt_call "abi.encodeCall" (a := .field r field)
    (args := [.field r field, t]) (List.mem_cons.mpr (Or.inl rfl))
  simp only [height] at hf ⊢
  omega

/-- Every builtin expansion weight is covered by the function-value dispatch root. -/
private theorem cost_le_callValue (g : String) : cost g ≤ 9 := by
  unfold cost
  split <;> first | decide | (split <;> decide)

/-- A named function-value callee can have any spelling, including #callValue.
Height need not decrease strictly in that case; removing its name node does. -/
theorem named_callee_decreases (g : String) (args : List RawExpr) :
    height (.call g args) ≤ height (.call callValueName (.name g :: args)) ∧
    RawExpr.nodes (.call g args) < RawExpr.nodes (.call callValueName (.name g :: args)) := by
  have hc := cost_le_callValue g
  constructor
  · simp only [height, heights, cost_callValue]
    omega
  · simp only [RawExpr.nodes, RawExpr.nodesList]
    omega

/-- Prefix extraction reserves a step for its generated cast. -/
private theorem cost_prefix (f : String) (h : f.startsWith "#bytesPrefix" = true) :
    2 ≤ cost f := by
  unfold cost
  split <;> try decide
  simp only [h, ite_true]
  decide

/-- The widths accepted by prefix extraction generate ordinary uint casts. -/
private theorem cost_prefix_cast (n : Nat) (hn : n ≤ 32) :
    cost (tyName .uint (8 * n)) = 1 := by
  have table : ∀ k : Fin 33, cost (tyName .uint (8 * k.val)) = 1 := by decide
  exact table ⟨n, by omega⟩

/-- Removing the prefix helper's optional bytes wrapper preserves descent. -/
theorem prefix_input_lt (f : String) (a : RawExpr) :
    height ((fun e : RawExpr => match e with | .call "bytes" [v] => v | _ => e) a) <
      height (.call f [a]) := by
  have ha := argument_lt_call f (a := a) (args := [a]) (List.mem_cons.mpr (Or.inl rfl))
  dsimp only
  split
  · exact Nat.lt_trans (argument_lt_call "bytes" (args := [_])
      (List.mem_cons.mpr (Or.inl rfl))) ha
  · exact ha

/-- The generated cast request is smaller than the original prefix extraction. -/
theorem prefix_cast_lt (f : String) (a : RawExpr) (n : Nat) (w : String)
    (hf : f.startsWith "#bytesPrefix" = true) (hn : n ≤ 32) :
    height (.call (tyName .uint (8 * n)) [.name w]) < height (.call f [a]) := by
  have hc := cost_prefix f hf
  have hw := cost_prefix_cast n hn
  have ha := height_pos a
  simp only [height, heights, hw]
  omega

end Solidity.ElabCallHeight
