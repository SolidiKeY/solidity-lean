import Solidity.Backend.AbiWorld.EntryComposition

/-! Composition of the EXISTING indexed bodyValues recursion. Index transport
only reconciles List.map_append; values remain the existing Vals family. No new
decoder, evaluator, body-success premise or admission predicate is introduced. -/
namespace Solidity.Backend.AbiWorld.BodyComposition
open AbiEntry EntryComposition

/-- Existing typed tuple concatenation, transported solely along map_append. -/
def appendValues (ps qs : List Param) (vs : Vals (ps.map Param.shape)) (ws : Vals (qs.map Param.shape)) :
    Vals ((ps ++ qs).map Param.shape) :=
  (List.map_append (f := Param.shape) (l₁ := ps) (l₂ := qs)).symm ▸ ArrayPairPacket.append vs ws

private theorem transport_cons {ss ts : List AbiEntry.Shape} {s : AbiEntry.Shape}
    (h : ss = ts) (v : AbiEntry.Val s) (vs : Vals ss) :
    (congrArg (List.cons s) h ▸ (Vals.cons v vs)) = Vals.cons v (h ▸ vs) := by
  cases h
  rfl

theorem appendValues_nil (qs : List Param) (ws : Vals (qs.map Param.shape)) : appendValues [] qs .nil ws = ws := rfl

theorem appendValues_cons (p : Param) (ps qs : List Param) (v : AbiEntry.Val p.shape)
    (vs : Vals (ps.map Param.shape)) (ws : Vals (qs.map Param.shape)) :
    appendValues (p :: ps) qs (.cons v vs) ws = .cons v (appendValues ps qs vs ws) := by
  exact transport_cons (List.map_append (f := Param.shape) (l₁ := ps) (l₂ := qs)).symm v (ArrayPairPacket.append vs ws)

private theorem entries_cons {p : Param} {ps qs : List Param} (e : Entered p.shape)
    (es : Entries ps) (fs : Entries qs) : appendEntries (.cons e es) fs = .cons e (appendEntries es fs) := rfl

/-- Unconditional equality, including eager/lazy refusals in original order.
The tail starts at pos+headsOf prefix and retains the SAME original fuel. -/
theorem body_append (I : Input) (f : Nat) {ps qs : List Param} (es : Entries ps) (fs : Entries qs) (pos : Nat) :
    bodyValues I f (ps ++ qs) (appendEntries es fs) pos = (do
      let vs ← bodyValues I f ps es pos
      let ws ← bodyValues I f qs fs (pos + headsOf ps)
      pure (appendValues ps qs vs ws)) := by
  induction es generalizing pos with
  | nil =>
    simp only [List.nil_append,appendEntries,bodyValues,headsOf,List.map_nil,Shape.headsSize,
      Nat.add_zero,bind,Except.bind,pure,Except.pure,appendValues_nil]
    cases bodyValues I f qs fs pos <;> rfl
  | @cons p ps e es ih =>
    cases e with
    | val v =>
      simp only [List.cons_append,entries_cons,heads_cons,Nat.add_assoc]
      conv => lhs; rw [bodyValues]
      conv => rhs; rw [bodyValues]
      simp only [bind,Except.bind,pure,Except.pure]
      rw [ih]
      simp only [Nat.add_assoc]
      cases h : bodyValues I f ps es (pos + p.shape.headSize) with
      | error err => rfl
      | ok vs =>
        dsimp only
        cases bodyValues I f qs fs (pos + (p.shape.headSize + headsOf ps)) <;>
          simp only [bind,Except.bind,pure,Except.pure,appendValues_cons]
    | ref addr len =>
      simp only [List.cons_append,entries_cons,heads_cons,Nat.add_assoc]
      conv => lhs; rw [bodyValues]
      conv => rhs; rw [bodyValues]
      rw [ih]
      simp only [Nat.add_assoc]
      cases h : eager I f p.shape pos with
      | ok v =>
        simp only [bind,Except.bind,pure,Except.pure]
        cases h' : bodyValues I f ps es (pos + p.shape.headSize) with
        | error err => rfl
        | ok vs =>
          dsimp only
          cases bodyValues I f qs fs (pos + (p.shape.headSize + headsOf ps)) <;>
            simp only [bind,Except.bind,pure,Except.pure,appendValues_cons]
      | error err =>
        cases err <;> simp only [bind,Except.bind,pure,Except.pure]
        all_goals try rfl
        all_goals
          cases h' : cvalRef I f p.shape addr len with
          | error err => cases err <;> rfl
          | ok v =>
            cases p.readsOnly <;> simp only [Bool.false_eq_true,ite_false,ite_true,bind,Except.bind,pure,Except.pure]
            all_goals try rfl
            all_goals
              cases h'' : bodyValues I f ps es (pos + p.shape.headSize) with
              | error err => rfl
              | ok vs =>
                dsimp only
                cases bodyValues I f qs fs (pos + (p.shape.headSize + headsOf ps)) <;>
                  simp only [bind,Except.bind,pure,Except.pure,appendValues_cons]



theorem body_success (I : Input) (f : Nat) {ps qs : List Param} (es : Entries ps) (fs : Entries qs)
    (vs : Vals (ps.map Param.shape)) (ws : Vals (qs.map Param.shape)) (pos : Nat)
    (hp : bodyValues I f ps es pos = .ok vs)
    (ht : bodyValues I f qs fs (pos + headsOf ps) = .ok ws) :
    bodyValues I f (ps ++ qs) (appendEntries es fs) pos = .ok (appendValues ps qs vs ws) := by
  rw [body_append,hp]
  simp only [bind,Except.bind,ht,pure,Except.pure]

theorem body_prefix_failure (I : Input) (f : Nat) {ps qs : List Param} (es : Entries ps) (fs : Entries qs)
    (pos : Nat) (err : String) (hp : bodyValues I f ps es pos = .error err) :
    bodyValues I f (ps ++ qs) (appendEntries es fs) pos = .error err := by
  rw [body_append,hp]
  rfl

theorem body_tail_failure (I : Input) (f : Nat) {ps qs : List Param} (es : Entries ps) (fs : Entries qs)
    (vs : Vals (ps.map Param.shape)) (pos : Nat) (err : String)
    (hp : bodyValues I f ps es pos = .ok vs)
    (ht : bodyValues I f qs fs (pos + headsOf ps) = .error err) :
    bodyValues I f (ps ++ qs) (appendEntries es fs) pos = .error err := by
  rw [body_append,hp]
  simp only [bind,Except.bind,ht]


/-- info: 'Solidity.Backend.AbiWorld.BodyComposition.appendValues_cons' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms appendValues_cons
/-- info: 'Solidity.Backend.AbiWorld.BodyComposition.body_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_append
/-- info: 'Solidity.Backend.AbiWorld.BodyComposition.body_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_success
/-- info: 'Solidity.Backend.AbiWorld.BodyComposition.body_prefix_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_prefix_failure
/-- info: 'Solidity.Backend.AbiWorld.BodyComposition.body_tail_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_tail_failure
end Solidity.Backend.AbiWorld.BodyComposition
