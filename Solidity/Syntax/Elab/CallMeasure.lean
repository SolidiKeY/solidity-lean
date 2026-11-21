import Solidity.Syntax.Elab.Measure

/-! Weighted call-expansion decreases and capture, operand, and argument output bounds. -/

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

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract)

/-- ERC-7201 output height is preserved when the expression callback preserves
height on strictly smaller requests. Its literal shortcut needs no callback. -/
theorem erc_output_height
    (H : RawExpr → ElabM (SProg C × RawExpr)) (a : RawExpr)
    (hh : ∀ e, height e < height (.call "erc7201" [a]) →
      Obs (H e) (fun out => height out.2 ≤ height e)) :
    Obs (hoistERC7201With C H [a])
      (fun out => height out.2 ≤ height (.call "erc7201" [a])) := by
  unfold hoistERC7201With
  dsimp only
  split
  · apply obs_pure
    exact height_pos (.call "erc7201" [a])
  · intro sc st m out st' m' h
    have he := erc_expansion_lt a
    exact Nat.le_trans (hh _ he sc st m out st' m' h) (Nat.le_of_lt he)

end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

/-- Operand preparation preserves each position's height whenever expression
hoisting and both capture policies preserve their inputs' heights. -/
theorem pair_output_heights
    (H : RawExpr → ElabM (SProg C × RawExpr)) (a b : RawExpr)
    (ha : Obs (H a) (fun out => height out.2 ≤ height a))
    (hb : Obs (H b) (fun out => height out.2 ≤ height b))
    (hc : ∀ e, Obs (captureExpr C e) (fun out => height out.2 ≤ height e))
    (hd : ∀ e later, Obs (captureBefore C e later) (fun out => height out.2 ≤ height e)) :
    Obs (hoistPairWith C H a b)
      (fun out => height out.2.1 ≤ height a ∧ height out.2.2 ≤ height b) := by
  unfold hoistPairWith
  refine obs_bind ha ?_
  rintro ⟨P, first⟩ hfirst
  apply obs_any
  intro scope
  apply obs_any
  intro context
  extract_lets powerData finish
  have hf : ∀ out : SProg C × RawExpr, height out.2 ≤ height first →
      Obs (finish out) (fun out => height out.2.1 ≤ height a ∧ height out.2.2 ≤ height b) := by
    rintro ⟨Pc, held⟩ hheld
    simp -zeta only [finish]
    apply obs_any
    intro context
    extract_lets tail
    have ht : ∀ out : SProg C × RawExpr, height out.2 ≤ height b →
        Obs (tail out) (fun out => height out.2.1 ≤ height a ∧ height out.2.2 ≤ height b) := by
      rintro ⟨Q, last⟩ hlast
      apply obs_pure
      exact ⟨Nat.le_trans hheld hfirst, hlast⟩
    clear_value tail
    split
    · exact obs_bind hb ht
    · exact obs_bind (obs_pure (Nat.le_refl _)) ht
  clear_value finish
  split
  · exact obs_bind (hc first) hf
  · exact obs_bind (hd first [b]) hf

/-- Binary preparation preserves height in either contract evaluation order. -/
theorem binop_output_height
    (H : RawExpr → ElabM (SProg C × RawExpr)) (op : BinOp) (a b : RawExpr)
    (ha : Obs (H a) (fun out => height out.2 ≤ height a))
    (hb : Obs (H b) (fun out => height out.2 ≤ height b))
    (hc : ∀ e, Obs (captureExpr C e) (fun out => height out.2 ≤ height e))
    (hd : ∀ e later, Obs (captureBefore C e later) (fun out => height out.2 ≤ height e)) :
    Obs (hoistBinopWith C H op a b)
      (fun out => height out.2 ≤ height (.binop op a b)) := by
  unfold hoistBinopWith
  extract_lets ltr finish
  split
  · rename_i he
    refine obs_bind (pair_output_heights C H a b ha hb hc hd) ?_
    rintro ⟨P, first, last⟩ ⟨hf, hl⟩
    simp only [finish, he, ↓reduceIte]
    apply obs_pure
    simp only at hf hl
    simp only [height]
    omega
  · rename_i he
    refine obs_bind (pair_output_heights C H b a hb ha hc hd) ?_
    rintro ⟨P, first, last⟩ ⟨hf, hl⟩
    simp only [finish, he]
    apply obs_pure
    simp only at hf hl
    simp only [Bool.false_eq_true, ↓reduceIte, height]
    omega

end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

omit [FreshNames] in
private theorem capture_shape_height_le (e out : RawExpr)
    (h : out = e ∨ ∃ x, out = .name x) : height out ≤ height e := by
  rcases h with rfl | ⟨x, rfl⟩
  · exact Nat.le_refl _
  · exact height_pos e

/-- The existing capture-shape invariant implies height nonincrease. -/
theorem captureExpr_height_bound (e : RawExpr) :
    Obs (captureExpr C e) (fun out => height out.2 ≤ height e) := by
  intro sc st m out st' m' h
  exact capture_shape_height_le e out.2
    (ElabCallArgsGood.captureExpr_shape C e sc st m out st' m' h)

/-- Effect-aware capture also preserves the input height. -/
theorem captureBefore_height_bound (e : RawExpr) (later : List RawExpr) :
    Obs (captureBefore C e later) (fun out => height out.2 ≤ height e) := by
  intro sc st m out st' m' h
  exact capture_shape_height_le e out.2
    (ElabCallArgsGood.captureBefore_shape C e later sc st m out st' m' h)

/-- Ordered operand bounds require only the two hoist-output bounds. -/
theorem pair_output_heights_of_hoist
    (H : RawExpr → ElabM (SProg C × RawExpr)) (a b : RawExpr)
    (ha : Obs (H a) (fun out => height out.2 ≤ height a))
    (hb : Obs (H b) (fun out => height out.2 ≤ height b)) :
    Obs (hoistPairWith C H a b)
      (fun out => height out.2.1 ≤ height a ∧ height out.2.2 ≤ height b) :=
  pair_output_heights C H a b ha hb (captureExpr_height_bound C) (captureBefore_height_bound C)

/-- Binary height preservation needs no additional capture premise. -/
theorem binop_output_height_of_hoist
    (H : RawExpr → ElabM (SProg C × RawExpr)) (op : BinOp) (a b : RawExpr)
    (ha : Obs (H a) (fun out => height out.2 ≤ height a))
    (hb : Obs (H b) (fun out => height out.2 ≤ height b)) :
    Obs (hoistBinopWith C H op a b)
      (fun out => height out.2 ≤ height (.binop op a b)) :=
  binop_output_height C H op a b ha hb (captureExpr_height_bound C) (captureBefore_height_bound C)

end Solidity.ElabCallHeight

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

/-- Ordinary argument preparation preserves the maximum input height, using
the existing predicate-preservation traversal rather than another induction. -/
theorem args_output_heights
    (H : RawExpr → ElabM (SProg C × RawExpr)) (args : List RawExpr)
    (hh : ∀ a, a ∈ args → Obs (H a) (fun out => height out.2 ≤ height a)) :
    Obs (hoistArgsWith C H args) (fun out => heights out.2 ≤ heights args) := by
  cases args with
  | nil =>
    simp only [hoistArgsWith]
    apply obs_pure
    exact Nat.le_refl _
  | cons a args =>
    intro sc st m out st' m' h
    have hn : ∀ x, height (.name x) ≤ heights (a :: args) := by
      intro x
      have hp := height_pos a
      simp only [height, heights]
      omega
    have hcallback : ∀ e, e ∈ a :: args →
        Obs (H e) (fun out => height out.2 ≤ heights (a :: args)) := by
      intro e he sc st m out st' m' hrun
      exact Nat.le_trans (hh e he sc st m out st' m' hrun) (mem_height_le he)
    have hout := ElabCallArgsGood.ordinary_good C (fun e => height e ≤ heights (a :: args))
      hn H (a :: args) hcallback sc st m out st' m' h
    exact heights_le hout

/-- Every ordinary prepared argument is strictly smaller than the source call. -/
theorem args_output_argument_lt
    (H : RawExpr → ElabM (SProg C × RawExpr)) (f : String) (args : List RawExpr)
    (hh : ∀ a, a ∈ args → Obs (H a) (fun out => height out.2 ≤ height a))
    (sc : ElabScope) (st st' : ECtx × Nat) (m m' : CallMemo) (out : SProg C × List RawExpr)
    (h : hoistArgsWith C H args sc st m = .ok ((out, st'), m')) :
    ∀ e, e ∈ out.2 → height e < height (.call f args) := by
  intro e he
  have hout := args_output_heights C H args hh sc st m out st' m' h
  have hm := mem_height_le he
  have hp := cost_pos f
  simp only [height]
  omega

end Solidity.ElabCallHeight

section
open Solidity.ElabControlProof

local macro "result_name_tail " h:ident : tactic =>
  `(tactic| repeat' first
    | with_reducible apply $h
    | (with_reducible apply obs_pure; exact ⟨_, rfl⟩)
    | (with_reducible apply obs_any; intro value; try cases value)
    | with_reducible apply obs_throw
    | split
    | extract_lets)

namespace Solidity.ElabControlProof
open Semantics
variable (C : Contract) [FreshNames]
private theorem hash_result_obs
    (H : RawExpr → ElabM (SProg C × RawExpr))
    (mem : RawExpr → ElabM (SProg C × String))
    (stmts : List RawStmt → ElabM (SProg C)) (f : String) (args : List RawExpr) :
    Obs (hoistHashWith C H mem stmts f args) (fun out => ∃ x, out.2 = .name x) := by
  simp only [hoistHashWith]
  repeat first
  | (with_reducible apply obs_throw)
  | (with_reducible apply obs_pure; exact ⟨_, rfl⟩)
  | split
  | (with_reducible apply obs_any; intro value; try cases value)

theorem hash_result_name
    (H : RawExpr → ElabM (SProg C × RawExpr))
    (mem : RawExpr → ElabM (SProg C × String))
    (stmts : List RawStmt → ElabM (SProg C)) (f : String) (args : List RawExpr)
    (sc : ElabScope) (st st' : ECtx × Nat) (m m' : CallMemo) (out : SProg C × RawExpr)
    (h : hoistHashWith C H mem stmts f args sc st m = .ok ((out, st'), m')) :
    ∃ x, out.2 = .name x := hash_result_obs C H mem stmts f args sc st m out st' m' h
/-- The public decode helper makes one internal-decode request after its tuple check. -/
theorem decode_front_eq
    (H : RawExpr → ElabM (SProg C × RawExpr))
    (mem : RawExpr → ElabM (SProg C × String))
    (stmts : List RawStmt → ElabM (SProg C))
    (bytes : String → ByteSrc → Nat → Nat → ElabM (SProg C × String))
    (b T : RawExpr) :
    abiDecodeWith C H mem stmts bytes "abi.decode" [b,T] =
      if (T matches .tuple _) then
        throw "abi.decode: one type here; a tuple of them is a declaration's `(T a, U b) = abi.decode(…)`"
      else H (.call abiDecodeName [b,T,.num 0,.num (decodeHeadWords C T)]) := by
  have hf : ("abi.decode" == "abi.decode") = true := by decide
  cases T <;> simp only [abiDecodeWith, hf, Bool.false_eq_true, ↓reduceIte,
    pure_bind, bind_pure] <;> rfl

private theorem decode_internal_obs
    (H : RawExpr → ElabM (SProg C × RawExpr))
    (mem : RawExpr → ElabM (SProg C × String))
    (stmts : List RawStmt → ElabM (SProg C))
    (bytes : String → ByteSrc → Nat → Nat → ElabM (SProg C × String))
    (f : String) (args : List RawExpr) (hf : f ≠ "abi.decode") :
    Obs (abiDecodeWith C H mem stmts bytes f args) (fun out => ∃ x, out.2 = .name x) := by
  have hfb : (f == "abi.decode") = false := by
    change decide (f = "abi.decode") = false
    exact decide_eq_false hf
  unfold abiDecodeWith
  extract_lets backend
  have hb : ∀ y, Obs (backend y) (fun out => ∃ x, out.2 = .name x) := by
    intro y
    simp -zeta only [backend]
    split
    · with_reducible apply obs_any
      intro value
      rcases value with ⟨P, Q, d⟩
      extract_lets len enough below word pos general
      have hg : ∀ y, Obs (general y) (fun out => ∃ x, out.2 = .name x) := by
        intro y
        simp -zeta only [general]
        split
        · with_reducible apply obs_any
          intro fresh
          extract_lets x finish
          have hfinish : ∀ S, Obs (finish S) (fun out => ∃ x, out.2 = .name x) := by
            intro S
            with_reducible apply obs_any
            intro R
            exact obs_pure ⟨_, rfl⟩
          clear_value finish
          result_name_tail hfinish
        · split
          · extract_lets nested
            have hn : ∀ y, Obs (nested y) (fun out => ∃ x, out.2 = .name x) := by
              intro y
              simp -zeta only [nested]
              with_reducible apply obs_any
              intro fresh
              extract_lets x finish
              have hfinish : ∀ S, Obs (finish S) (fun out => ∃ x, out.2 = .name x) := by
                intro S
                with_reducible apply obs_any
                intro R
                exact obs_pure ⟨_, rfl⟩
              clear_value finish
              result_name_tail hfinish
            clear_value nested
            result_name_tail hn
          · exact obs_throw
      clear_value general
      split
      · extract_lets primitive enum
        have hp : ∀ y, Obs (primitive y) (fun out => ∃ x, out.2 = .name x) := by
          intro y
          simp -zeta only [primitive]
          result_name_tail hg
        clear_value primitive
        have he : ∀ y, Obs (enum y) (fun out => ∃ x, out.2 = .name x) := by
          intro y
          simp -zeta only [enum]
          result_name_tail hp
        clear_value enum
        result_name_tail he
      · result_name_tail hg
    · exact obs_throw
  clear_value backend
  simp only [hfb, Bool.false_eq_true, ↓reduceIte]
  exact hb _



theorem decode_internal_result_name
    (H : RawExpr → ElabM (SProg C × RawExpr))
    (mem : RawExpr → ElabM (SProg C × String))
    (stmts : List RawStmt → ElabM (SProg C))
    (bytes : String → ByteSrc → Nat → Nat → ElabM (SProg C × String))
    (f : String) (args : List RawExpr) (hf : f ≠ "abi.decode")
    (sc : ElabScope) (st st' : ECtx × Nat) (m m' : CallMemo) (out : SProg C × RawExpr)
    (h : abiDecodeWith C H mem stmts bytes f args sc st m = .ok ((out, st'), m')) :
    ∃ x, out.2 = .name x :=
  decode_internal_obs C H mem stmts bytes f args hf sc st m out st' m' h

end Solidity.ElabControlProof

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

/-- Successful hash helpers return an expression of height one. -/
theorem hash_output_height
    (H : RawExpr → ElabM (SProg C × RawExpr))
    (bytes : RawExpr → ElabM (SProg C × String))
    (stmts : List RawStmt → ElabM (SProg C)) (f : String) (args : List RawExpr)
    (sc : ElabScope) (st st' : ECtx × Nat) (m m' : CallMemo) (out : SProg C × RawExpr)
    (h : hoistHashWith C H bytes stmts f args sc st m = .ok ((out, st'), m')) :
    height out.2 = 1 := by
  obtain ⟨x, hx⟩ := hash_result_name C H bytes stmts f args sc st st' m m' out h
  simp only [hx, height]

/-- Successful internal ABI decoding returns an expression of height one. -/
theorem internal_decode_output_height
    (H : RawExpr → ElabM (SProg C × RawExpr))
    (mem : RawExpr → ElabM (SProg C × String))
    (stmts : List RawStmt → ElabM (SProg C))
    (bytes : String → ByteSrc → Nat → Nat → ElabM (SProg C × String))
    (f : String) (args : List RawExpr) (hf : f ≠ "abi.decode")
    (sc : ElabScope) (st st' : ECtx × Nat) (m m' : CallMemo) (out : SProg C × RawExpr)
    (h : abiDecodeWith C H mem stmts bytes f args sc st m = .ok ((out, st'), m')) :
    height out.2 = 1 := by
  obtain ⟨x, hx⟩ := decode_internal_result_name C H mem stmts bytes f args hf sc st st' m m' out h
  simp only [hx, height]

/-- The public decode front preserves the caller's height bound once its
strictly smaller internal request preserves its own height. -/
theorem decode_front_output_height
    (H : RawExpr → ElabM (SProg C × RawExpr))
    (mem : RawExpr → ElabM (SProg C × String))
    (stmts : List RawStmt → ElabM (SProg C))
    (bytes : String → ByteSrc → Nat → Nat → ElabM (SProg C × String))
    (b T : RawExpr)
    (hh : Obs (H (.call abiDecodeName [b, T, .num 0, .num (decodeHeadWords C T)]))
      (fun out => height out.2 ≤ height (.call abiDecodeName [b, T, .num 0, .num (decodeHeadWords C T)]))) :
    Obs (abiDecodeWith C H mem stmts bytes "abi.decode" [b,T])
      (fun out => height out.2 ≤ height (.call "abi.decode" [b,T])) := by
  rw [decode_front_eq]
  split
  · exact obs_throw
  · intro sc st m out st' m' h
    exact Nat.le_trans (hh sc st m out st' m' h) (Nat.le_of_lt (decode_request_lt C b T))

end Solidity.ElabCallHeight

namespace Solidity.ElabControlProof
open Semantics
variable (C : Contract) [FreshNames]
private theorem encode_nested_obs
    (kind : RawExpr → ElabM AbiKind)
    (mem : RawExpr → ElabM (SProg C × String))
    (stmts : List RawStmt → ElabM (SProg C))
    (args : List RawExpr) (marks : List (Option AbiKind)) (sel : Option RawExpr) :
    Obs (abiEncodeNested? C kind mem stmts args marks sel)
      (fun result => ∀ out, result = some out → ∃ x, out.2 = .name x) := by
  unfold abiEncodeNested?
  repeat' first
  | (with_reducible apply obs_pure; intro out he; cases he <;> exact ⟨_, rfl⟩)
  | (with_reducible apply obs_any; intro value; try cases value)
  | with_reducible apply obs_throw
  | split
  | extract_lets

/-- Successful nested ABI encoding returns a raw name whenever it handles the input. -/
theorem encode_nested_result_name
    (kind : RawExpr → ElabM AbiKind)
    (mem : RawExpr → ElabM (SProg C × String))
    (stmts : List RawStmt → ElabM (SProg C))
    (args : List RawExpr) (marks : List (Option AbiKind)) (sel : Option RawExpr)
    (sc : ElabScope) (st st' : ECtx × Nat) (m m' : CallMemo) (out : SProg C × RawExpr)
    (h : abiEncodeNested? C kind mem stmts args marks sel sc st m = .ok ((some out, st'), m')) :
    ∃ x, out.2 = .name x :=
  encode_nested_obs C kind mem stmts args marks sel sc st m (some out) st' m' h out rfl

private theorem encode_obs (rc : ElabRec C) (std strs : Bool) (args : List RawExpr)
    (marks : List (Option AbiKind)) (sel : Option RawExpr) :
    Obs (abiEncodeWith C rc std strs args marks sel) (fun out => ∃ x, out.2 = .name x) := by
  unfold abiEncodeWith
  extract_lets mem stmts kind P base parts len pad words hpos finish select
  have hf : ∀ P selW, Obs (finish P selW) (fun out => ∃ x, out.2 = .name x) := by
    intro P selW
    simp -zeta only [finish]
    repeat' first
    | (with_reducible apply obs_pure; exact ⟨_, rfl⟩)
    | (with_reducible apply obs_any; intro value; try cases value)
    | with_reducible apply obs_throw
    | split
    | extract_lets
  clear_value finish
  have hs : ∀ y, Obs (select y) (fun out => ∃ x, out.2 = .name x) := by
    intro y
    simp -zeta only [select]
    result_name_tail hf
  clear_value select
  split
  · with_reducible apply obs_bind (encode_nested_obs C kind mem stmts args marks sel)
    intro result hr
    cases result with
    | none => result_name_tail hs
    | some out => exact obs_pure (hr out rfl)
  · result_name_tail hs

/-- ABI encoding returns a raw name on every successful run. -/
theorem encode_result_name (rc : ElabRec C) (std strs : Bool) (args : List RawExpr)
    (marks : List (Option AbiKind)) (sel : Option RawExpr)
    (sc : ElabScope) (st st' : ECtx × Nat) (m m' : CallMemo) (out : SProg C × RawExpr)
    (h : abiEncodeWith C rc std strs args marks sel sc st m = .ok ((out, st'), m')) :
    ∃ x, out.2 = .name x :=
  encode_obs C rc std strs args marks sel sc st m out st' m' h


end Solidity.ElabControlProof

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

/-- ABI encoding returns a height-one destination, independently of callback outputs. -/
theorem encode_output_height (rc : ElabRec C) (std strs : Bool) (args : List RawExpr)
    (marks : List (Option AbiKind)) (sel : Option RawExpr)
    (sc : ElabScope) (st st' : ECtx × Nat) (m m' : CallMemo) (out : SProg C × RawExpr)
    (h : abiEncodeWith C rc std strs args marks sel sc st m = .ok ((out, st'), m')) :
    height out.2 = 1 := by
  obtain ⟨x, hx⟩ := encode_result_name C rc std strs args marks sel sc st st' m m' out h
  simp only [hx, height]

end Solidity.ElabCallHeight


end

namespace Solidity.ElabCallHeight
open Semantics ElabControlProof
variable (C : Contract) [FreshNames]

omit [FreshNames] in
/-- Include malformed arities in the ERC helper's output invariant. -/
theorem erc_args_output_height
    (H : RawExpr → ElabM (SProg C × RawExpr)) (args : List RawExpr)
    (hh : ∀ e, height e < height (.call "erc7201" args) →
      Obs (H e) (fun out => height out.2 ≤ height e)) :
    Obs (hoistERC7201With C H args)
      (fun out => height out.2 ≤ height (.call "erc7201" args)) := by
  cases args with
  | nil => exact obs_throw
  | cons a rest =>
    cases rest with
    | nil => exact erc_output_height C H a hh
    | cons b rest => exact obs_throw

/-- Both public and internal decode helpers preserve the original call bound. -/
theorem decode_output_height
    (H : RawExpr → ElabM (SProg C × RawExpr))
    (mem : RawExpr → ElabM (SProg C × String))
    (stmts : List RawStmt → ElabM (SProg C))
    (bytes : String → ByteSrc → Nat → Nat → ElabM (SProg C × String))
    (f : String) (args : List RawExpr)
    (hh : ∀ e, height e < height (.call f args) →
      Obs (H e) (fun out => height out.2 ≤ height e)) :
    Obs (abiDecodeWith C H mem stmts bytes f args)
      (fun out => height out.2 ≤ height (.call f args)) := by
  by_cases hf : f = "abi.decode"
  · subst f
    cases args with
    | nil => exact obs_throw
    | cons b rest =>
      cases rest with
      | nil => exact obs_throw
      | cons T rest =>
        cases rest with
        | nil =>
          exact decode_front_output_height C H mem stmts bytes b T
            (hh _ (decode_request_lt C b T))
        | cons extra rest => exact obs_throw
  · intro sc st m out st' m' hr
    have hn := internal_decode_output_height C H mem stmts bytes f args hf sc st st' m m' out hr
    have hp := height_pos (.call f args)
    omega

end Solidity.ElabCallHeight
