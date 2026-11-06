import Solidity.Backend.LabelExec.Fragment

/-! Soundness of the static fragment against the published numeric execution.
Metadata is never accepted as an execution result: actual step equations are
proved from opcode lookup and physical operand availability. -/
namespace Solidity.Backend.LabelExec

/-- Every recognized numeric row has its operands and returns one real word. -/
theorem numeric_domain (o : Op) (a b suffix : Nat) (stack : Scalar.Stack)
    (hrow : numericArity o = some (a,b)) (hlen : stack.length = a+suffix) :
    ∃ next, Scalar.numericStep o stack = some next ∧ next.length = b+suffix := by
  cases hu : Scalar.unary o with
  | some f =>
    simp only [numericArity, hu, Option.some.injEq, Prod.mk.injEq] at hrow
    rcases hrow with ⟨rfl,rfl⟩
    cases stack with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons x xs =>
      refine ⟨f x :: xs, ?_, ?_⟩
      · simp only [Scalar.numericStep, hu, Scalar.applyUnary]
      · simp only [List.length_cons] at hlen ⊢; omega
  | none =>
    cases hb : Scalar.binary o with
    | some f =>
      simp only [numericArity, hu, hb, Option.some.injEq, Prod.mk.injEq] at hrow
      rcases hrow with ⟨rfl,rfl⟩
      cases stack with
      | nil => simp only [List.length_nil] at hlen; omega
      | cons x xs =>
        cases xs with
        | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
        | cons y ys =>
          refine ⟨f x y :: ys, ?_, ?_⟩
          · simp only [Scalar.numericStep, hu, hb, Scalar.applyBinary]
          · simp only [List.length_cons] at hlen ⊢; omega
    | none =>
      cases ht : Scalar.ternary o with
      | none => simp only [numericArity, hu, hb, ht, reduceCtorEq] at hrow
      | some f =>
        simp only [numericArity, hu, hb, ht, Option.some.injEq, Prod.mk.injEq] at hrow
        rcases hrow with ⟨rfl,rfl⟩
        cases stack with
        | nil => simp only [List.length_nil] at hlen; omega
        | cons x xs =>
          cases xs with
          | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
          | cons y ys =>
            cases ys with
            | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
            | cons z zs =>
              refine ⟨f x y z :: zs, ?_, ?_⟩
              · simp only [Scalar.numericStep, hu, hb, ht, Scalar.applyTernary]
              · simp only [List.length_cons] at hlen ⊢; omega

/-- The real exchange function is defined whenever its indexed operand exists. -/
theorem exchange_domain (a : Scalar.Word) (n : Nat) (stack : Scalar.Stack)
    (h : n < stack.length) :
    ∃ (b : Scalar.Word) (next : Scalar.Stack), Scalar.exchange a n stack = some (b,next) := by
  induction n generalizing stack with
  | zero =>
    cases stack with
    | nil => simp only [List.length_nil] at h; omega
    | cons x xs => exact ⟨x,a :: xs,rfl⟩
  | succ n ih =>
    cases stack with
    | nil => simp only [List.length_nil] at h; omega
    | cons x xs =>
      have hn : n < xs.length := by simp only [List.length_cons] at h; omega
      obtain ⟨b,next,he⟩ := ih xs hn
      refine ⟨b,x :: next,?_⟩
      simp only [Scalar.exchange, he, Option.map_some]

/-- A supported static row produces an ACTUAL Scalar.step result and height.
No independent chosen next stack is accepted as a premise. -/
theorem arity_domain (i : Instr) (a b suffix : Nat) (stack : Scalar.Stack)
    (hrow : arity i = some (a,b)) (hlen : stack.length = a+suffix) :
    ∃ next, Scalar.step i stack = some next ∧ next.length = b+suffix := by
  cases i with
  | push n imm =>
    simp only [arity, Option.some.injEq, Prod.mk.injEq] at hrow
    rcases hrow with ⟨rfl,rfl⟩
    refine ⟨Scalar.immediate imm.toList :: stack,rfl,?_⟩
    simp only [List.length_cons]
    omega
  | op o =>
    cases o <;> simp only [arity, Scalar.step] at hrow ⊢
    case DUP n =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hrow
      rcases hrow with ⟨rfl,rfl⟩
      have hn : n.val < stack.length := by omega
      have hg : stack[n.val]? = some (stack[n.val]'hn) := List.getElem?_eq_getElem hn
      refine ⟨(stack[n.val]'hn) :: stack,?_,?_⟩
      · simp only [Scalar.duplicate, hg, Option.map_some]
      · simp only [List.length_cons]; omega
    case SWAP n =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hrow
      rcases hrow with ⟨rfl,rfl⟩
      cases stack with
      | nil => simp only [List.length_nil] at hlen; omega
      | cons x xs =>
        have hn : n.val < xs.length := by simp only [List.length_cons] at hlen; omega
        obtain ⟨word,next,he⟩ := exchange_domain x n.val xs hn
        have hs : Scalar.swap n.val (x :: xs) = some (word :: next) := by
          simp only [Scalar.swap, he, Option.map_some]
        exact ⟨word :: next,hs,(Scalar.swap_length n.val hs).trans hlen⟩
    case POP =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hrow
      rcases hrow with ⟨rfl,rfl⟩
      cases stack with
      | nil => simp only [List.length_nil] at hlen; omega
      | cons x xs =>
        refine ⟨xs,rfl,?_⟩
        simp only [List.length_cons] at hlen
        omega
    all_goals exact numeric_domain _ _ _ _ _ hrow hlen

/-- Raw control opcodes are excluded by static metadata, not a run premise. -/
theorem InstrShape.no_control {i : Instr} {n m : Nat} (shape : InstrShape i n m) :
    i ≠ .op .JUMP ∧ i ≠ .op .JUMPI ∧ i ≠ .op .JUMPDEST := by
  rcases shape with ⟨a,b,suffix,row,hin,hout⟩
  refine ⟨?_,?_,?_⟩ <;> intro hi <;> subst i <;>
    simp only [arity, numericArity, Scalar.unary, Scalar.binary, Scalar.ternary,
      reduceCtorEq] at row

/-- The raw input is intrinsically sized; the actual fetched successor vector
and height are derived internally from static shape and the existing evaluator. -/
theorem InstrShape.fetched_step {i : Instr} {n m : Nat} (shape : InstrShape i n m)
    (pre post : List UInt8) (stack : Vector Scalar.Word n) :
    ∃ next : Vector Scalar.Word m,
      step (pre ++ (i.encode ++ post)) ⟨pre.length,stack.toList⟩ =
        some ⟨pre.length+i.size,next.toList⟩ := by
  rcases shape with ⟨a,b,suffix,row,hin,hout⟩
  have hlen : stack.toList.length = a+suffix := by rw [Vector.length_toList, hin]
  obtain ⟨next,he,hnext⟩ := arity_domain i a b suffix stack.toList row hlen
  refine ⟨⟨next.toArray,?_⟩,?_⟩
  · simpa only [List.size_toArray] using hnext.trans hout.symm
  · simp only [Vector.toList_mk]
    rw [step_prefix]
    exact effect_of_scalar _ _ _ _ _ he

/-- The outer structured test's actual static peak is recoverable without
identifying Code records that happen to contain the same instructions. -/
theorem BlockShape.control_capacity {b : Block} {n m : Nat} (shape : BlockShape b n m) :
    match b with
    | .ite _ _ _ => n+2 ≤ 1024
    | .loop _ _ => n+2 ≤ 1024
    | _ => True := by
  cases shape <;> first | exact True.intro | assumption

end Solidity.Backend.LabelExec
