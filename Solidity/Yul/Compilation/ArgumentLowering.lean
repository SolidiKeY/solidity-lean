import Solidity.Yul.Compilation.PureLowering

/-! Arity-indexed argument/result lowering. These inline concrete instruction
slices; they do not invent V12 function frames, return addresses or source calls. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

structure LoweredArgs (n arity : Nat) (values : Vector Word n → Vector Word arity) where
  code : Nat → Option Program
  correct : ∀ depth p, code depth = some p →
    ∀ (locals : Vector Word n) (newer : Vector Word depth) (tail : Stack),
      run p (newer.toList ++ (locals.toList ++ tail)) =
        some ((values locals).toList ++ (newer.toList ++ (locals.toList ++ tail)))

def lowerNoArgs (n : Nat) : LoweredArgs n 0 (fun _ => #v[]) where
  code := fun _ => some []
  correct := by intro depth p selected locals newer tail; cases selected; rfl

/-- Evaluation is right-to-left. All already computed right arguments remain
above locals while the next left argument uses the increased live depth. -/
def lowerArgCons {n arity : Nat} {head : Vector Word n → Word}
    {rest : Vector Word n → Vector Word arity}
    (first : LoweredExpr n head) (suffix : LoweredArgs n arity rest) :
    LoweredArgs n (1 + arity) (fun locals => #v[head locals] ++ rest locals) where
  code := fun depth => (suffix.code depth).bind (fun rb =>
    (first.code (arity + depth)).map (fun la => rb ++ la))
  correct := by
    intro depth p selected locals newer tail
    cases hr : suffix.code depth with
    | none => simp only [hr, Option.bind_none] at selected; cases selected
    | some rb =>
      cases hl : first.code (arity + depth) with
      | none => simp only [hr, hl, Option.bind_some, Option.map_none] at selected; cases selected
      | some la =>
        simp only [hr, hl, Option.bind_some, Option.map_some] at selected
        cases selected
        apply run_comp (suffix.correct depth rb hr locals newer tail)
        have h := first.correct (arity + depth) la hl locals (rest locals ++ newer) tail
        simpa only [Vector.toList_append, List.cons_append, List.nil_append,
          List.append_assoc] using h

/-- Exact result mapping for a concrete inline target slice, stronger than a
mere stack delta or existential arity. The body law must really be proved. -/
structure AritySlice (args results : Nat) (value : Vector Word args → Vector Word results) where
  code : Program
  correct : ∀ (input : Vector Word args) (tail : Stack),
    run code (input.toList ++ tail) = some ((value input).toList ++ tail)

def lowerInline {n args results : Nat} {input : Vector Word n → Vector Word args}
    {output : Vector Word args → Vector Word results}
    (arguments : LoweredArgs n args input) (body : AritySlice args results output) :
    LoweredArgs n results (fun locals => output (input locals)) where
  code := fun depth => (arguments.code depth).map (fun p => p ++ body.code)
  correct := by
    intro depth p selected locals newer tail
    cases ha : arguments.code depth with
    | none => simp only [ha, Option.map_none] at selected; cases selected
    | some x =>
      simp only [ha, Option.map_some] at selected
      cases selected
      exact run_comp (arguments.correct depth x ha locals newer tail)
        (body.correct (input locals) (newer.toList ++ (locals.toList ++ tail)))

private theorem vector_pair (v : Vector Word 2) : v.toList = [v[0], v[1]] := by
  apply List.ext_getElem
  · exact Vector.length_toList
  · intro i hi hj
    have h : i = 0 ∨ i = 1 := by simp only [Vector.length_toList] at hi; omega
    rcases h with h | h <;> subst i <;>
      simp only [Vector.getElem_toList, List.getElem_cons_zero, List.getElem_cons_succ]

def addAritySlice : AritySlice 2 1 (fun input => #v[input[0] + input[1]]) where
  code := [.op .ADD]
  correct := by
    intro input tail
    rw [vector_pair]
    rfl

def subAritySlice : AritySlice 2 1 (fun input => #v[input[0] - input[1]]) where
  code := [.op .SUB]
  correct := by intro input tail; rw [vector_pair]; rfl

def swapPairAritySlice : AritySlice 2 2 (fun input => #v[input[1], input[0]]) where
  code := [.op (.SWAP ⟨0, by decide⟩)]
  correct := by intro input tail; rw [vector_pair]; rfl

/-- Capacity on accepted emitted code is separate from local/argument arities. -/
theorem LoweredArgs.capacity {n arity : Nat} {values : Vector Word n → Vector Word arity}
    (compiled : LoweredArgs n arity values) (depth : Nat) (p : Program)
    (selected : compiled.code depth = some p) (locals : Vector Word n)
    (newer : Vector Word depth) (tail : Stack)
    (bounded : stackBound p ((depth + n + tail.length : Nat) : Int) = true) :
    arity + depth + n + tail.length ≤ 1024 := by
  have h := run_capacity (compiled.correct depth p selected locals newer tail)
  simp only [List.length_append, Vector.length_toList] at h
  simpa only [Nat.add_assoc] using h (by simpa only [Nat.add_assoc] using bounded)

#print axioms lowerArgCons
#print axioms lowerInline
#print axioms addAritySlice
#print axioms subAritySlice
#print axioms swapPairAritySlice
#print axioms LoweredArgs.capacity
end Solidity.Yul.Compilation
