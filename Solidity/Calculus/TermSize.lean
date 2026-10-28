import Solidity.Calculus.Step

/-!
# The size of what a rule emits

Every rule of `Stmt.step` writes a bounded number of update elements
(`Stmt.step_upds_le`: two except for explicit tuple snapshots), and every term it emits, in
an update or in a formula, is at most linear in the statement it fires on
(`Stmt.step_tmSize_le`: `16 * s.size + 16`), independently of the types the
statement is at: a size counts the nodes of a term or of a statement, never
a type, a name, a literal's digits or a proof.

**What is counted.**  The terms of the premise's updates
(`Premise.upds`, `Upd.tmSize`: the sum over its elements) and of its
formulas (`Premise.fmls`, `Fml.tmSize`: connectives and terms, a modality's
program not counted).  The programs a premise carries (a capture's block, a
call's inlined body, a loop's body) are statements, not terms: the next
steps fire on them, each bounded by its own statement.  The frame of a loop's
invariant rule (`Premise.inv`'s `xs`) is a list of positions of the context,
no term, so not counted.

**Why the bound is linear and not constant.**  A rule lowers the parts of
its statement it can (`Val.lower`, `Loc.lower`, …), whole: `x = a % b % n`
keeps its operands lazy (`.modular`), a read of a simple location writes
the location, an invariant is copied into the rule's formulas.  Lowering
is at most three term nodes per syntax node (`Val.lower_size`); the worst
rule writes a receiver four times (`sp.push() /= se`, `PushSuffix.saveOp`),
hence `16`.

**The proof** is one lemma per arm of `Stmt.step` (`Calculus/Arms.lean`,
`Calculus/Blocks.lean`), each by cases on the arm's own shape, under the
builders' lemmas (`Premise.Bounded.update1`, …); a premise that emits no
update and no formula (a capture, an unfold, a call inlined, a `try`'s
branches) is bounded by anything (`Premise.Bounded.of_nil`).  A call's
summary (`internalCallSummary`) is one element whose term has the nodes of
the summary, which its gate bounds by the callee's body
(`CallRet.summary?_bounded`, `Tm.sumGate`).
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## Sizes of terms, updates and formulas -/

/-- The nodes of what a local is set to. -/
def Rhs.size {Γ : Ctx} : {t : LTy} → Rhs C Γ t → Nat
  | _, .val t => t.size
  | _, .path p => p.size
  | _, .unset => 0
  | _, .mref i => i.size
  | _, .store s => s.size
  | _, .saveNet => 0
  | _, .saveNetMt => 0
  | _, .zint t => t.size

/-- The nodes of an assigning element: its terms, and one for the target. -/
def UpdElem.size {Γ Δ : Ctx} : UpdElem C Γ Δ → Nat
  | .local _ r => 1 + r.size
  | .storage s => 1 + s.size
  | .memory m => 1 + m.size
  | .selfBalance _ a => 1 + a.size
  | .net r _ a => 1 + r.size + a.size
  | .pay r a => 1 + r.size + a.size
  | .netMt r a => 1 + r.size + a.size
  | .setBalance a => 1 + a.size

/-- The assigning elements of an update (a pop and a drop assign nothing). -/
def Upd.length {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Nat
  | _, .nil => 0
  | _, .snoc U _ => U.length + 1
  | _, .decl U _ _ => U.length + 1
  | _, .pop U _ => U.length
  | _, .drop U _ => U.length

/-- The nodes of an update's elements. -/
def Upd.tmSize {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Nat
  | _, .nil => 0
  | _, .snoc U e => U.tmSize + e.size
  | _, .decl U _ r => U.tmSize + 1 + r.size
  | _, .pop U _ => U.tmSize
  | _, .drop U _ => U.tmSize

/-- The nodes of a formula's connectives and terms; a modality's program is
not a term, and is not counted. -/
def Fml.tmSize : {Γ : Ctx} → Fml C Γ → Nat
  | _, .tt => 1
  | _, .eq a b => 1 + a.size + b.size
  | _, .wellFormed s => 1 + s.size
  | _, .not φ => 1 + φ.tmSize
  | _, .and φ ψ => 1 + φ.tmSize + ψ.tmSize
  | _, .imp φ ψ => 1 + φ.tmSize + ψ.tmSize
  | _, .upd _ U φ => 1 + U.tmSize + φ.tmSize
  | _, .modal _ _ _ φ => 1 + φ.tmSize
  | _, .havoc φ => 1 + φ.tmSize
  | _, .all _ _ φ => 1 + φ.tmSize
  | _, .bind _ _ _ φ => 1 + φ.tmSize
  | _, .anon _ φ | _, .allocAll _ _ φ | _, .grow φ => 1 + φ.tmSize


/-! ## Lowering, by the nodes -/

section Lowering

variable {Γ : Ctx}

theorem Tm.size_castV {p q : PrimTy} (h : p = q) (t : Tm C Γ (.val p)) :
    (Tm.castV h t).size = t.size := by
  cases h; rfl

theorem Simple.lower_size {p : PrimTy} (s : Simple C Γ p) : s.lower.size = 1 := by
  cases s with
  | env k hp => simp only [Simple.lower, Tm.size_castV, Tm.size]
  | _ => rfl

mutual

theorem SPath.lower_size : {T : Ty} → (b : SPath C Γ T) → b.lower.size ≤ 3 * b.size
  | _, .alias _ => by simp only [SPath.lower, Tm.size, SPath.size]; omega
  | _, .loc l => by
    have := Loc.lower_size l
    simp only [SPath.lower, SPath.size]; omega

theorem Loc.lower_size : {T : Ty} → (l : Loc C Γ T) → l.lower.size ≤ 3 * l.size
  | _, .root _ _ => by simp only [Loc.lower, Tm.size, Loc.size]; omega
  | _, .field b _ _ => by
    have := SPath.lower_size b
    simp only [Loc.lower, Tm.size, Loc.size]; omega
  | _, .index _ b i => by
    have := SPath.lower_size b
    have := Val.lower_size i
    simp only [Loc.lower, Tm.size, Loc.size]; omega

theorem MPath.lower_size : {T : Ty} → (b : MPath C Γ T) → b.lower.size ≤ 3 * b.size
  | _, .var _ _ => by simp only [MPath.lower, Tm.size, MPath.size]; omega
  | .ref _, .loc l => by
    have := MLoc.lower_size l
    simp only [MPath.lower, Tm.mread, Tm.size, MPath.size]; omega
  | .prim _, .loc l => by
    have := MLoc.lower_size l
    simp only [MPath.lower, Tm.mread, MPath.size]; omega

theorem MLoc.lower_size : {T : Ty} → (l : MLoc C Γ T) → l.lower.size ≤ 3 * l.size
  | _, .field b _ _ => by
    have := MPath.lower_size b
    simp only [MLoc.lower, Tm.size, MLoc.size]; omega
  | _, .index _ b i => by
    have := MPath.lower_size b
    have := Val.lower_size i
    simp only [MLoc.lower, Tm.size, MLoc.size]; omega

theorem Val.lower_size : {p : PrimTy} → (v : Val C Γ p) → v.lower.size ≤ 3 * v.size
  | _, .simple s => by
    simp only [Val.lower, Simple.lower_size, Val.size, Simple.size]; omega
  | _, .read l => by
    have := Loc.lower_size l
    simp only [Val.lower, Tm.size, Val.size]; omega
  | _, .binop _ _ _ a b => by
    have := Val.lower_size a
    have := Val.lower_size b
    simp only [Val.lower, Tm.size_castV, Tm.size, Val.size]; omega
  | _, .unop _ _ _ a => by
    have := Val.lower_size a
    simp only [Val.lower, Tm.size_castV, Tm.size, Val.size]; omega
  | _, .ternary c a b => by
    have := Val.lower_size c
    have := Val.lower_size a
    have := Val.lower_size b
    simp only [Val.lower, Tm.size, Val.size]; omega
  | _, .readMem l => by
    have := MLoc.lower_size l
    simp only [Val.lower, Tm.size, Val.size]; omega
  | _, .len b _ => by
    have := SPath.lower_size b
    simp only [Val.lower, Tm.size_castV, Tm.size, Val.size]; omega
  | _, .mlen b _ => by
    have := MPath.lower_size b
    simp only [Val.lower, Tm.size_castV, Tm.size, Val.size]; omega
  | _, .hash _ b _ => by
    have := MPath.lower_size b
    simp only [Val.lower, Tm.size_castV, Tm.size, Val.size]; omega
  | _, .modular _ a b k => by
    have := Val.lower_size a
    have := Val.lower_size b
    have := Val.lower_size k
    simp only [Val.lower, Tm.size, Val.size]; omega

end

theorem Src.lower_size {T : Ty} (r : Src C Γ T) : r.lower.size ≤ 3 * r.size := by
  cases r with
  | val v => have := Val.lower_size v; simp only [Src.lower, Tm.size, Src.size]; omega
  | copy p _ => have := SPath.lower_size p; simp only [Src.lower, Tm.size, Src.size]; omega
  | fixedCopy p _ _ =>
    have := SPath.lower_size p; simp only [Src.lower, Tm.size, Src.size]; omega
  | copyMem p | fixedCopyMem p _ => have := MPath.lower_size p; simp only [Src.lower, Tm.size, Src.size]; omega

theorem MSrc.lower_size {T : Ty} (r : MSrc C Γ T) : r.lower.size ≤ 3 * r.size := by
  cases r with
  | val v => have := Val.lower_size v; simp only [MSrc.lower, Tm.size, MSrc.size]; omega
  | ref p => have := MPath.lower_size p; simp only [MSrc.lower, Tm.size, MSrc.size]; omega

/-! ### Shifting keeps the nodes -/

mutual

theorem SPath.size_up {t : LTy} : {T : Ty} → (b : SPath C Γ T) → (b.up (t := t)).size = b.size
  | _, .alias _ => rfl
  | _, .loc l => by simp only [SPath.up, SPath.size, Loc.size_up l]

theorem Loc.size_up {t : LTy} : {T : Ty} → (l : Loc C Γ T) → (l.up (t := t)).size = l.size
  | _, .root _ _ => rfl
  | _, .field b _ _ => by simp only [Loc.up, Loc.size, SPath.size_up b]
  | _, .index _ b i => by simp only [Loc.up, Loc.size, SPath.size_up b, Val.size_up i]

theorem MPath.size_up {t : LTy} : {T : Ty} → (b : MPath C Γ T) → (b.up (t := t)).size = b.size
  | _, .var _ _ => rfl
  | _, .loc l => by simp only [MPath.up, MPath.size, MLoc.size_up l]

theorem MLoc.size_up {t : LTy} : {T : Ty} → (l : MLoc C Γ T) → (l.up (t := t)).size = l.size
  | _, .field b _ _ => by simp only [MLoc.up, MLoc.size, MPath.size_up b]
  | _, .index _ b i => by simp only [MLoc.up, MLoc.size, MPath.size_up b, Val.size_up i]

theorem Val.size_up {t : LTy} : {p : PrimTy} → (v : Val C Γ p) → (v.up (t := t)).size = v.size
  | _, .simple _ => rfl
  | _, .read l => by simp only [Val.up, Val.size, Loc.size_up l]
  | _, .binop _ _ _ a b => by simp only [Val.up, Val.size, Val.size_up a, Val.size_up b]
  | _, .unop _ _ _ a => by simp only [Val.up, Val.size, Val.size_up a]
  | _, .ternary c a b => by
    simp only [Val.up, Val.size, Val.size_up c, Val.size_up a, Val.size_up b]
  | _, .readMem l => by simp only [Val.up, Val.size, MLoc.size_up l]
  | _, .len b _ => by simp only [Val.up, Val.size, SPath.size_up b]
  | _, .mlen b _ => by simp only [Val.up, Val.size, MPath.size_up b]
  | _, .modular _ a b k => by
    simp only [Val.up, Val.size, Val.size_up a, Val.size_up b, Val.size_up k]
  | _, .hash _ b _ => by simp only [Val.up, Val.size, MPath.size_up b]

end

mutual

theorem SPath.size_wk {Δ : Ctx} (h : Thin Γ Δ) : {T : Ty} → (b : SPath C Γ T) → (b.wk h).size = b.size
  | _, .alias _ => rfl
  | _, .loc l => by simp only [SPath.wk, SPath.size, Loc.size_wk h l]

theorem Loc.size_wk {Δ : Ctx} (h : Thin Γ Δ) : {T : Ty} → (l : Loc C Γ T) → (l.wk h).size = l.size
  | _, .root _ _ => rfl
  | _, .field b _ _ => by simp only [Loc.wk, Loc.size, SPath.size_wk h b]
  | _, .index _ b i => by simp only [Loc.wk, Loc.size, SPath.size_wk h b, Val.size_wk h i]

theorem MPath.size_wk {Δ : Ctx} (h : Thin Γ Δ) : {T : Ty} → (b : MPath C Γ T) → (b.wk h).size = b.size
  | _, .var _ _ => rfl
  | _, .loc l => by simp only [MPath.wk, MPath.size, MLoc.size_wk h l]

theorem MLoc.size_wk {Δ : Ctx} (h : Thin Γ Δ) : {T : Ty} → (l : MLoc C Γ T) → (l.wk h).size = l.size
  | _, .field b _ _ => by simp only [MLoc.wk, MLoc.size, MPath.size_wk h b]
  | _, .index _ b i => by simp only [MLoc.wk, MLoc.size, MPath.size_wk h b, Val.size_wk h i]

theorem Val.size_wk {Δ : Ctx} (h : Thin Γ Δ) : {p : PrimTy} → (v : Val C Γ p) → (v.wk h).size = v.size
  | _, .simple _ => rfl
  | _, .read l => by simp only [Val.wk, Val.size, Loc.size_wk h l]
  | _, .binop _ _ _ a b => by simp only [Val.wk, Val.size, Val.size_wk h a, Val.size_wk h b]
  | _, .unop _ _ _ a => by simp only [Val.wk, Val.size, Val.size_wk h a]
  | _, .ternary c a b => by
    simp only [Val.wk, Val.size, Val.size_wk h c, Val.size_wk h a, Val.size_wk h b]
  | _, .readMem l => by simp only [Val.wk, Val.size, MLoc.size_wk h l]
  | _, .len b _ => by simp only [Val.wk, Val.size, SPath.size_wk h b]
  | _, .mlen b _ => by simp only [Val.wk, Val.size, MPath.size_wk h b]
  | _, .modular _ a b k => by
    simp only [Val.wk, Val.size, Val.size_wk h a, Val.size_wk h b, Val.size_wk h k]
  | _, .hash _ b _ => by simp only [Val.wk, Val.size, MPath.size_wk h b]

end

end Lowering

/-! ## What a premise emits -/

section Premises

variable {Γ : Ctx}

/-- The updates a premise writes, each with its contexts. -/
def Premise.upds {Γ' : Ctx} : Premise C Γ Γ' → List ((Γ₀ : Ctx) × (Δ : Ctx) × Upd C Γ₀ Δ)
  | .update U => [⟨_, _, U⟩]
  | .updates U V => [⟨_, _, U⟩, ⟨_, _, V⟩]
  | .guardedUpdates _ U V => [⟨_, _, U⟩, ⟨_, _, V⟩]
  | .cases _ us => us.map fun U => ⟨_, _, U⟩
  | .inv _ _ _ _ U _ _ _ _ _ _ => [⟨_, _, U⟩]
  | _ => []

/-- The formulas a premise writes, each with its context. -/
def Premise.fmls {Γ' : Ctx} : Premise C Γ Γ' → List ((Δ : Ctx) × Fml C Δ)
  | .split _ c c' _ _ => [⟨_, c⟩, ⟨_, c'⟩]
  | .check c => [⟨_, c⟩]
  | .cases fs _ => fs.map fun φ => ⟨_, φ⟩
  | .inv I B _ _ _ c c' _ _ _ post =>
    [⟨_, I⟩] ++ (match B with | some b => [⟨_, b⟩] | none => []) ++ [⟨_, c⟩, ⟨_, c'⟩, ⟨_, post⟩]
  | .guardedUpdates c _ _ => [⟨_, c⟩]
  | _ => []

/-- **A premise bounded by `n`**: at most `maxUpd` elements per update,
and every update's and formula's terms of at most `n` nodes. The default
remains two; lexicographic snapshots state their arity-dependent limit. -/
structure Premise.Bounded {Γ' : Ctx} (n : Nat) (P : Premise C Γ Γ')
    (maxUpd : Nat := 2) : Prop where
  upds : ∀ U ∈ P.upds, U.2.2.length ≤ maxUpd ∧ U.2.2.tmSize ≤ n
  fmls : ∀ φ ∈ P.fmls, φ.2.tmSize ≤ n

namespace Premise.Bounded

variable {Γ' : Ctx}

theorem mono {n n' maxUpd : Nat} {P : Premise C Γ Γ'}
    (h : P.Bounded n maxUpd) (hn : n ≤ n') : P.Bounded n' maxUpd :=
  ⟨fun U hU => ⟨(h.upds U hU).1, Nat.le_trans (h.upds U hU).2 hn⟩,
   fun φ hφ => Nat.le_trans (h.fmls φ hφ) hn⟩

/-- Raising the explicit update-length budget preserves the node bound. -/
theorem mono_upds {n a b : Nat} {P : Premise C Γ Γ'} (h : P.Bounded n a)
    (hab : a ≤ b) : P.Bounded n b :=
  ⟨fun U hU => ⟨Nat.le_trans (h.upds U hU).1 hab, (h.upds U hU).2⟩, h.fmls⟩

/-- A premise that writes no update and no formula. -/
theorem of_nil {n maxUpd : Nat} {P : Premise C Γ Γ'} (hu : P.upds = []) (hf : P.fmls = []) :
    P.Bounded n maxUpd :=
  ⟨fun U hU => by rw [hu] at hU; exact absurd hU List.not_mem_nil,
   fun φ hφ => by rw [hf] at hφ; exact absurd hφ List.not_mem_nil⟩

theorem update {n : Nat} {U : Upd C Γ Γ'} (hl : U.length ≤ 2) (hs : U.tmSize ≤ n) :
    (Premise.update U).Bounded n :=
  ⟨fun V hV => by
    simp only [Premise.upds, List.mem_singleton] at hV
    subst hV; exact ⟨hl, hs⟩,
   fun φ hφ => absurd hφ List.not_mem_nil⟩

theorem upd1 {n : Nat} {e : UpdElem C Γ Γ} (h : e.size ≤ n) : (Premise.upd1 e).Bounded n :=
  update (by simp only [Upd.length]; omega) (by simp only [Upd.tmSize]; omega)

theorem upd2 {n : Nat} {e₁ e₂ : UpdElem C Γ Γ} (h : e₁.size + e₂.size ≤ n) :
    (Premise.update ((Upd.nil.snoc e₁).snoc e₂)).Bounded n :=
  update (by simp only [Upd.length]; omega) (by simp only [Upd.tmSize]; omega)

theorem split {n : Nat} {b : BlockKind} {c c' : Fml C Γ} {Γ₁ Γ₂ : Ctx} {P : Prog C Γ Γ₁}
    {Q : Prog C Γ Γ₂} (hc : c.tmSize ≤ n) (hc' : c'.tmSize ≤ n) :
    (Premise.split b c c' P Q).Bounded n :=
  ⟨fun U hU => absurd hU List.not_mem_nil,
   fun φ hφ => by
    simp only [Premise.fmls, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · exact hc
    · exact hc'⟩

theorem check {n : Nat} {c : Fml C Γ} (hc : c.tmSize ≤ n) : (Premise.check c).Bounded n :=
  ⟨fun U hU => absurd hU List.not_mem_nil,
   fun φ hφ => by
    simp only [Premise.fmls, List.mem_singleton] at hφ
    subst hφ; exact hc⟩

theorem updates {n : Nat} {Δ : Ctx} {U : Upd C Γ Δ} {V : Upd C Δ Γ'} (hU : U.length ≤ 2)
    (hU' : U.tmSize ≤ n) (hV : V.length ≤ 2) (hV' : V.tmSize ≤ n) :
    (Premise.updates U V).Bounded n :=
  ⟨fun W hW => by
    simp only [Premise.upds, List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl
    · exact ⟨hU, hU'⟩
    · exact ⟨hV, hV'⟩,
   fun φ hφ => absurd hφ List.not_mem_nil⟩

theorem guardedUpdates {n : Nat} {Δ : Ctx} {c : Fml C Γ} {U : Upd C Γ Δ} {V : Upd C Δ Γ}
    (hc : c.tmSize ≤ n) (hU : U.length ≤ 2) (hU' : U.tmSize ≤ n) (hV : V.length ≤ 2)
    (hV' : V.tmSize ≤ n) : (Premise.guardedUpdates c U V).Bounded n :=
  ⟨fun W hW => by
    simp only [Premise.upds, List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl
    · exact ⟨hU, hU'⟩
    · exact ⟨hV, hV'⟩,
   fun φ hφ => by
    simp only [Premise.fmls, List.mem_singleton] at hφ
    subst hφ; exact hc⟩

theorem cases {n : Nat} {fs : List (Fml C Γ)} {us : List (Upd C Γ Γ)}
    (hf : ∀ φ ∈ fs, φ.tmSize ≤ n) (hu : ∀ U ∈ us, U.length ≤ 2 ∧ U.tmSize ≤ n) :
    (Premise.cases fs us).Bounded n :=
  ⟨fun W hW => by
    simp only [Premise.upds, List.mem_map] at hW
    obtain ⟨U, hU, rfl⟩ := hW
    exact hu U hU,
   fun φ hφ => by
    simp only [Premise.fmls, List.mem_map] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    exact hf ψ hψ⟩

theorem inv {n maxUpd : Nat} {Δ₀ Δ Γ₁ : Ctx} {I : Fml C Γ} {B : Option (Fml C Γ)}
    {xs : List ((t : LTy) × Idx Γ t)} {hv : Option (List Name)} {U : Upd C Γ Δ} {c c' : Fml C Δ}
    {hu : Ext Γ Δ₀} {hb : Ext Δ₀ Δ} {P : Prog C Δ₀ Γ₁} {post : Fml C Δ₀}
    (hI : I.tmSize ≤ n) (hB : ∀ b, B = some b → b.tmSize ≤ n) (hU : U.length ≤ maxUpd)
    (hU' : U.tmSize ≤ n) (hc : c.tmSize ≤ n) (hc' : c'.tmSize ≤ n) (hp : post.tmSize ≤ n) :
    (Premise.inv I B xs hv U c c' hu hb P post).Bounded n maxUpd :=
  ⟨fun W hW => by
    simp only [Premise.upds, List.mem_singleton] at hW
    subst hW; exact ⟨hU, hU'⟩,
   fun φ hφ => by
    simp only [Premise.fmls, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with (rfl | hφ) | rfl | rfl | rfl
    · exact hI
    · cases B with
      | none => exact absurd hφ List.not_mem_nil
      | some b =>
        simp only [List.mem_singleton] at hφ
        subst hφ; exact hB b rfl
    · exact hc
    · exact hc'
    · exact hp⟩

end Premise.Bounded

end Premises

/-! ## The arms -/

/-- A premise that writes nothing. -/
macro "bnil" : tactic => `(tactic| exact Premise.Bounded.of_nil rfl rfl)

section Arms

variable (k : Nat) {Γ : Ctx}

theorem SPath.one_le_size {T : Ty} (b : SPath C Γ T) : 1 ≤ b.size := by
  cases b <;> simp only [SPath.size] <;> omega
theorem MPath.one_le_size {T : Ty} (b : MPath C Γ T) : 1 ≤ b.size := by
  cases b <;> simp only [MPath.size] <;> omega
theorem Val.one_le_size {p : PrimTy} (v : Val C Γ p) : 1 ≤ v.size := by
  cases v <;> simp only [Val.size] <;> omega

/-! ### The elements -/

theorem UpdElem.setLocal_size {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    (UpdElem.setLocal i v).size ≤ 3 * v.size + 1 := by
  have := Val.lower_size v
  simp only [UpdElem.setLocal, UpdElem.size, Rhs.size]; omega

theorem UpdElem.save_size {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    (UpdElem.save l r).size ≤ 3 * (l.size + r.size) + 3 := by
  have := Loc.lower_size l
  have := Src.lower_size r
  simp only [UpdElem.save, UpdElem.size, Tm.size]; omega

theorem UpdElem.saveMem_size {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    (UpdElem.saveMem l p).size ≤ 3 * (l.size + p.size) + 5 := by
  have := Loc.lower_size l
  have := MPath.lower_size p
  simp only [UpdElem.saveMem, UpdElem.size, Tm.size]; omega

theorem UpdElem.delAt_size {T : Ty} (l : Loc C Γ T) :
    (UpdElem.delAt l).size ≤ 3 * l.size + 3 := by
  have := Loc.lower_size l
  simp only [UpdElem.delAt, UpdElem.size, Tm.size]; omega

theorem UpdElem.writeMem_size {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    (UpdElem.writeMem l r).size ≤ 3 * (l.size + r.size) + 3 := by
  have := MLoc.lower_size l
  have := MSrc.lower_size r
  simp only [UpdElem.writeMem, UpdElem.size, Tm.size]; omega

theorem UpdElem.pushSlot_size {E : Ty} (b : SPath C Γ (.array E)) :
    (UpdElem.pushSlot b).size ≤ 3 * b.size + 3 := by
  have := SPath.lower_size b
  simp only [UpdElem.pushSlot, UpdElem.size, Tm.size]; omega

theorem UpdElem.push_size {E : Ty} (b : SPath C Γ (.array E)) (v : Src C Γ E) :
    (UpdElem.push b v).size ≤ 3 * (b.size + v.size) + 3 := by
  have := SPath.lower_size b
  have := Src.lower_size v
  simp only [UpdElem.push, UpdElem.size, Tm.size]; omega

theorem UpdElem.pop_size {E : Ty} (b : SPath C Γ (.array E)) :
    (UpdElem.pop b).size ≤ 3 * b.size + 3 := by
  have := SPath.lower_size b
  simp only [UpdElem.pop, UpdElem.size, Tm.size]; omega

theorem UpdElem.shrink_size {E : Ty} (b : SPath C Γ (.array E)) :
    (UpdElem.shrink b).size ≤ 3 * b.size + 3 := by
  have := SPath.lower_size b
  simp only [UpdElem.shrink, UpdElem.size, Tm.size]; omega

theorem UpdElem.payTo_size (r a : Simple C Γ .uint) : (UpdElem.payTo r a).size = 3 := by
  simp only [UpdElem.payTo, UpdElem.size, Simple.lower_size]

/-! ### Reads unfolded until they are simple -/

theorem SHole.readStep_bounded {T : Ty} (lhs : SHole C Γ T)
    {root : (r : Name) → C.rootType r = some T → Premise C Γ Γ}
    {field : {s : Name} → SPath C Γ (.struct s) → (f : Name) → C.fieldType s f = some T →
      Premise C Γ Γ}
    {index : {R : RefTy} → {kp : PrimTy} → IndexTy R kp T → SPath C Γ (.ref R) → Simple C Γ kp →
      Premise C Γ Γ} {n : Nat} (l : Loc C Γ T)
    (hr : ∀ r h, l = .root r h → (root r h).Bounded n)
    (hf : ∀ {s : Name} (b : SPath C Γ (.struct s)) f h, l = .field b f h → (field b f h).Bounded n)
    (hi : ∀ {R : RefTy} {kp : PrimTy} (it : IndexTy R kp T) (b : SPath C Γ (.ref R)) ie,
      l = .index it b (.simple ie) → (index it b ie).Bounded n) :
    (lhs.readStep k root field index l).Bounded n := by
  cases l with
  | root r h => exact hr r h rfl
  | field b f h =>
    simp only [SHole.readStep]
    split
    · exact hf b f h rfl
    · bnil
  | index it b i =>
    simp only [SHole.readStep]
    split
    · cases i with
      | simple ie => exact hi it b ie rfl
      | _ => bnil
    · bnil

theorem MHole.readStep_bounded {T : Ty} (lhs : MHole C Γ T)
    {field : {s : Name} → (mv : Idx Γ (.mem (.struct s))) → (Ty.ref (.struct s)).mapFree = true →
      (f : Name) → C.fieldType s f = some T → Premise C Γ Γ}
    {index : {R : RefTy} → ArrTy R T → (mv : Idx Γ (.mem R)) → (Ty.ref R).mapFree = true →
      Simple C Γ .uint → Premise C Γ Γ} {n : Nat} (l : MLoc C Γ T)
    (hf : ∀ {s : Name} (mv : Idx Γ (.mem (.struct s))) hmv f hf',
      l = .field (.var mv hmv) f hf' → (field mv hmv f hf').Bounded n)
    (hi : ∀ {R : RefTy} (a : ArrTy R T) (mv : Idx Γ (.mem R)) hmv ie,
      l = .index a (.var mv hmv) (.simple ie) → (index a mv hmv ie).Bounded n) :
    (lhs.readStep k field index l).Bounded n := by
  cases l with
  | field b f h =>
    cases b with
    | var mv hmv => exact hf mv hmv f h rfl
    | loc _ => bnil
  | index a b i =>
    cases b with
    | var mv hmv =>
      cases i with
      | simple ie => exact hi a mv hmv ie rfl
      | _ => bnil
    | loc _ => bnil

/-! ### Locals and aliases -/

theorem shortStep_bounded {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a : Simple C Γ p') (b : Val C Γ p')
    (n : Nat) : (shortStep i op ha hq a b).Bounded n := by
  unfold shortStep
  split <;> bnil

theorem localStep_bounded {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    (localStep k i v).Bounded (3 * v.size + 1) := by
  cases v with
  | simple s => exact .upd1 (UpdElem.setLocal_size i _)
  | read l =>
    apply SHole.readStep_bounded
    · intro r h e; subst e; exact .upd1 (UpdElem.setLocal_size i _)
    · intro s b f h e; subst e; exact .upd1 (UpdElem.setLocal_size i _)
    · intro R kp it b ie e; subst e; exact .upd1 (UpdElem.setLocal_size i _)
  | binop op ha hq a b =>
    cases a with
    | simple a =>
      cases b with
      | simple b => exact .upd1 (UpdElem.setLocal_size i _)
      | _ =>
        simp only [localStep]
        split
        · exact shortStep_bounded i op ha hq a _ _
        · bnil
    | _ => bnil
  | unop op ha hq a =>
    cases a with
    | simple a => exact .upd1 (UpdElem.setLocal_size i _)
    | _ => bnil
  | ternary c a b =>
    simp only [localStep, ternaryStep]
    split <;> bnil
  | readMem l =>
    apply MHole.readStep_bounded
    · intro s mv hmv f hf e; subst e; exact .upd1 (UpdElem.setLocal_size i _)
    · intro R a mv hmv ie e; subst e; exact .upd1 (UpdElem.setLocal_size i _)
  | len b hp =>
    simp only [localStep]
    split
    · exact .upd1 (UpdElem.setLocal_size i _)
    · bnil
  | mlen b hp =>
    cases b with
    | var mv hm => exact .upd1 (UpdElem.setLocal_size i _)
    | loc l => bnil
  | modular op a b m => exact .upd1 (UpdElem.setLocal_size i _)
  | hash k b hp => exact .upd1 (UpdElem.setLocal_size i _)

theorem rebindStep_bounded {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) :
    (rebindStep k i r).Bounded (6 * r.size + 3) := by
  cases r with
  | path p =>
    cases p with
    | alias j =>
      apply Premise.Bounded.upd1
      simp only [UpdElem.size, Rhs.size, SPath.lower, Tm.size]; omega
    | loc l =>
      apply SHole.readStep_bounded
      · intro r h e; subst e
        apply Premise.Bounded.upd1
        simp only [UpdElem.size, Rhs.size, Loc.lower, Tm.size]; omega
      · intro s b f h e; subst e
        apply Premise.Bounded.upd1
        have := SPath.lower_size b
        simp only [UpdElem.size, Rhs.size, Loc.lower, Tm.size, ARhs.size, SPath.size,
          Loc.size]; omega
      · intro R kp it b ie e; subst e
        apply Premise.Bounded.upd1
        have := SPath.lower_size b
        simp only [UpdElem.size, Rhs.size, Loc.lower, Val.lower, Simple.lower_size, Tm.size,
          ARhs.size, SPath.size, Loc.size, Val.size, Simple.size]; omega
  | push b hd =>
    have := SPath.lower_size b
    simp only [rebindStep]
    split
    · split
      · apply Premise.Bounded.update
        · simp only [Upd.pushBindMapping, Upd.length]; omega
        · simp only [Upd.pushBindMapping, Upd.tmSize, UpdElem.size, Rhs.size, Tm.size,
            ARhs.size]; omega
      · apply Premise.Bounded.update
        · simp only [Upd.pushBind, Upd.length]; omega
        · simp only [Upd.pushBind, Upd.tmSize, UpdElem.size, Rhs.size, Tm.size,
            ARhs.size]; omega
    · bnil

/-! ### Storage writes -/

theorem copyStep_bounded {R : RefTy} (l : Loc C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true)
    (p : SPath C Γ (.ref R)) :
    (copyStep k l hm p).Bounded (3 * (l.size + p.size) + 6) := by
  cases p with
  | alias y =>
    apply Premise.Bounded.upd1
    have := UpdElem.save_size l (.copy (.alias y) hm)
    simp only [Src.size, SPath.size] at this ⊢; omega
  | loc l' =>
    apply SHole.readStep_bounded
    · intro r h e
      apply Premise.Bounded.upd1
      have := UpdElem.save_size l (.copy (.loc l') hm)
      simp only [Src.size, SPath.size] at this ⊢; omega
    · intro s b f h e; bnil
    · intro R kp it b ie e; bnil

theorem VHole.step_bounded {p : PrimTy} (lhs : VHole C Γ p)
    {simple : Simple C Γ p → Premise C Γ Γ} {n : Nat} (hs : ∀ se, (simple se).Bounded n)
    (e : Val C Γ p) : (lhs.step k simple e).Bounded n := by
  cases e with
  | simple se => exact hs se
  | ternary c a b =>
    simp only [VHole.step, ternaryStep]
    split <;> bnil
  | _ => bnil

theorem VHole.lower_bounded {p : PrimTy} (lhs : VHole C Γ p) {other : Premise C Γ Γ} {n : Nat}
    (ho : other.Bounded n) (e : Val C Γ p) : (lhs.lower k other e).Bounded n := by
  cases e with
  | ternary c a b =>
    simp only [VHole.lower, ternaryStep]
    split <;> bnil
  | _ => exact ho

theorem assignStep_bounded {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    (assignStep k l r).Bounded (3 * (l.size + r.size) + 9) := by
  have hs := UpdElem.save_size l r
  cases r with
  | copyMem p => simp only [assignStep]; exact .upd1 (by omega)
  | fixedCopy p shape hm | fixedCopyMem p shape => simp only [assignStep]; exact .upd1 (by omega)
  | val e =>
    cases l with
    | root r h =>
      apply VHole.step_bounded
      intro se
      apply Premise.Bounded.upd1
      have := UpdElem.save_size (.root r h) (.val (.simple se))
      have := Val.one_le_size e
      have h3 : (Src.val (Val.simple se)).size = 3 := rfl
      have he : (Src.val e).size = 1 + e.size := rfl
      omega
    | field b f h =>
      simp only [assignStep]
      split
      · apply VHole.step_bounded
        intro se
        apply Premise.Bounded.upd1
        have := UpdElem.save_size (.field b f h) (.val (.simple se))
        have := Val.one_le_size e
        have h3 : (Src.val (Val.simple se)).size = 3 := rfl
        have he : (Src.val e).size = 1 + e.size := rfl
        omega
      · exact VHole.lower_bounded k _ (by bnil) e
    | index it b i =>
      simp only [assignStep]
      split
      · cases i with
        | simple ie =>
          apply VHole.step_bounded
          intro se
          apply Premise.Bounded.upd1
          have := UpdElem.save_size (.index it b (.simple ie)) (.val (.simple se))
          have := Val.one_le_size e
          have h3 : (Src.val (Val.simple se)).size = 3 := rfl
          have he : (Src.val e).size = 1 + e.size := rfl
          omega
        | _ => exact VHole.lower_bounded k _ (by bnil) e
      · exact VHole.lower_bounded k _ (by bnil) e
  | copy p hm =>
    cases l with
    | root r h =>
      cases p with
      | alias j => exact .upd1 (by omega)
      | loc l' =>
        apply SHole.readStep_bounded
        · intro _ _ _; exact .upd1 (by omega)
        · intro _ _ _ _ _; exact .upd1 (by omega)
        · intro _ _ _ _ _ _; exact .upd1 (by omega)
    | field b f h =>
      simp only [assignStep]
      split
      · exact (copyStep_bounded k _ hm p).mono (by simp only [Src.size]; omega)
      · bnil
    | index it b i =>
      simp only [assignStep]
      split
      · cases i with
        | simple ie => exact (copyStep_bounded k _ hm p).mono (by simp only [Src.size]; omega)
        | _ => bnil
      · bnil

theorem assignFromMemStep_bounded {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    (assignFromMemStep k l p).Bounded (3 * (l.size + p.size) + 5) := by
  have hs := UpdElem.saveMem_size l p
  cases l with
  | root r h => exact .upd1 hs
  | field b f h =>
    simp only [assignFromMemStep]
    split
    · exact .upd1 hs
    · bnil
  | index it b i =>
    simp only [assignFromMemStep]
    split
    · cases i with
      | simple ie => exact .upd1 hs
      | _ => bnil
    · bnil

theorem deleteStep_bounded {T : Ty} (l : Loc C Γ T) :
    (deleteStep k l).Bounded (3 * l.size + 3) := by
  have hs := UpdElem.delAt_size l
  cases l with
  | root r h => exact .upd1 hs
  | field b f h =>
    simp only [deleteStep]
    split
    · exact .upd1 hs
    · bnil
  | index it b i =>
    simp only [deleteStep]
    split
    · cases i with
      | simple ie => exact .upd1 hs
      | _ => bnil
    · bnil

/-! ### Compound assignment and `++`/`--` -/

theorem OpLoc.cur_size {p : PrimTy} (l : OpLoc C Γ p) : l.cur.size ≤ 3 * l.size + 2 := by
  cases l with
  | «local» i => simp only [OpLoc.cur, Tm.size]; omega
  | root r h => simp only [OpLoc.cur, Val.lower, Loc.lower, Tm.size, OpLoc.size]; omega
  | field b f h =>
    have := SPath.lower_size b
    simp only [OpLoc.cur, Val.lower, Loc.lower, Tm.size, OpLoc.size]; omega
  | index it b ie =>
    have := SPath.lower_size b
    simp only [OpLoc.cur, Val.lower, Loc.lower, Simple.lower_size, Tm.size, OpLoc.size]; omega
  | mfield b f h =>
    have := MPath.lower_size b
    simp only [OpLoc.cur, Val.lower, MLoc.lower, Tm.size, OpLoc.size]; omega
  | mindex a b ie =>
    have := MPath.lower_size b
    simp only [OpLoc.cur, Val.lower, MLoc.lower, Simple.lower_size, Tm.size, OpLoc.size]; omega

theorem OpLoc.set_size {p : PrimTy} (l : OpLoc C Γ p) (t : Tm C Γ (.val p)) :
    (l.set t).size ≤ 3 * l.size + t.size + 4 := by
  cases l with
  | «local» i => simp only [OpLoc.set, UpdElem.size, Rhs.size]; omega
  | root r h => simp only [OpLoc.set, UpdElem.size, Loc.lower, Tm.size, OpLoc.size]; omega
  | field b f h =>
    have := SPath.lower_size b
    simp only [OpLoc.set, UpdElem.size, Loc.lower, Tm.size, OpLoc.size]; omega
  | index it b ie =>
    have := SPath.lower_size b
    simp only [OpLoc.set, UpdElem.size, Loc.lower, Val.lower, Simple.lower_size, Tm.size,
      OpLoc.size]; omega
  | mfield b f h =>
    have := MPath.lower_size b
    simp only [OpLoc.set, UpdElem.size, MLoc.lower, Tm.size, OpLoc.size]; omega
  | mindex a b ie =>
    have := MPath.lower_size b
    simp only [OpLoc.set, UpdElem.size, MLoc.lower, Val.lower, Simple.lower_size, Tm.size,
      OpLoc.size]; omega

theorem OpLoc.op_size {p : PrimTy} (l : OpLoc C Γ p) (op : BinOp)
    (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true) (t : Tm C Γ (.val p)) :
    (l.op op hop hp t).size = 1 + l.cur.size + t.size := by
  simp only [OpLoc.op, Tm.size_castV, Tm.size]

theorem OpLoc.unfoldRecv_bounded {p : PrimTy}
    {s : {t : LTy} → OpLoc C (t :: Γ) p → Stmt C (t :: Γ) (t :: Γ)} (l : OpLoc C Γ p)
    {q : Premise C Γ Γ} (h : l.unfoldRecv k s = some q) (n : Nat) : q.Bounded n := by
  cases l with
  | field b f hf =>
    simp only [OpLoc.unfoldRecv] at h
    split at h
    · cases h
    · cases h; bnil
  | index it b ie =>
    simp only [OpLoc.unfoldRecv] at h
    split at h
    · cases h
    · cases h; bnil
  | mfield b f hf =>
    cases b with
    | var _ _ => simp only [OpLoc.unfoldRecv, reduceCtorEq] at h
    | loc _ => simp only [OpLoc.unfoldRecv, Option.some.injEq] at h; subst h; bnil
  | mindex a b ie =>
    cases b with
    | var _ _ => simp only [OpLoc.unfoldRecv, reduceCtorEq] at h
    | loc _ => simp only [OpLoc.unfoldRecv, Option.some.injEq] at h; subst h; bnil
  | «local» i => simp only [OpLoc.unfoldRecv, reduceCtorEq] at h
  | root r hr => simp only [OpLoc.unfoldRecv, reduceCtorEq] at h

theorem opStep_bounded {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) :
    (opStep k op hop hp l r).Bounded (6 * l.size + 8) := by
  cases r with
  | simple se =>
    simp only [opStep]
    split
    · rename_i q hq; exact OpLoc.unfoldRecv_bounded k l hq _
    · apply Premise.Bounded.upd1
      have := OpLoc.set_size l (l.op op hop hp se.lower)
      have := OpLoc.cur_size l
      rw [OpLoc.op_size, Simple.lower_size] at *
      omega
  | _ => bnil

theorem incStep_bounded {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    (incStep k op hp l).Bounded (6 * l.size + 8) := by
  simp only [incStep]
  split
  · rename_i q hq; exact OpLoc.unfoldRecv_bounded k l hq _
  · apply Premise.Bounded.upd1
    have := OpLoc.set_size l (l.op op.binOp (IncDec.binOp_compound op) hp (Tm.one p hp))
    have := OpLoc.cur_size l
    have h1 : (Tm.one (C := C) (Γ := Γ) p hp).size = 1 := rfl
    rw [OpLoc.op_size] at *
    omega

theorem Tm.bumped_size (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true) (t : Tm C Γ (.val p)) :
    (Tm.bumped op hp t).size ≤ t.size + 2 := by
  unfold Tm.bumped
  split
  · simp only [Tm.size_castV, Tm.size, Tm.one]; omega
  · omega

theorem assignIncStep_bounded {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    (assignIncStep i op hp l).Bounded (9 * l.size + 13) := by
  apply Premise.Bounded.upd2
  have := OpLoc.set_size l (l.op op.binOp (IncDec.binOp_compound op) hp (Tm.one p hp))
  have := OpLoc.cur_size l
  have := Tm.bumped_size op hp l.cur
  have h1 : (Tm.one (C := C) (Γ := Γ) p hp).size = 1 := rfl
  have h2 : (UpdElem.local (C := C) i (.val (Tm.bumped op hp l.cur))).size =
      1 + (Tm.bumped op hp l.cur).size := rfl
  rw [OpLoc.op_size] at *
  omega

/-! ### Arrays and payments -/

theorem assignLocalPushStep_bounded {p : PrimTy} (i : Idx Γ (.val p))
    (b : SPath C Γ (.array (.prim p))) :
    (assignLocalPushStep k i b).Bounded (3 * b.size + 5) := by
  simp only [assignLocalPushStep]
  split
  · apply Premise.Bounded.upd2
    have := UpdElem.pushSlot_size b
    simp only [UpdElem.size, Rhs.size, Tm.size] at *
    omega
  · bnil

theorem PushSuffix.saveOp_tmSize {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) (se : Simple C Γ p) :
    (PushSuffix.saveOp op hop hp b se).tmSize ≤ 12 * b.size + 18 := by
  have := SPath.lower_size b
  simp only [PushSuffix.saveOp, PushSuffix.lastPath, PushSuffix.lastIndex, Upd.tmSize,
    UpdElem.size, Tm.size, Tm.size_castV, Simple.lower_size]
  omega

theorem pushOpStep_bounded {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) (r : Val C Γ p) :
    (pushOpStep k op hop hp b r).Bounded (12 * b.size + 18) := by
  have := UpdElem.pushSlot_size b
  have := PushSuffix.saveOp_tmSize op hop hp b
  cases r with
  | simple se =>
    simp only [pushOpStep]
    split
    · split
      · apply Premise.Bounded.guardedUpdates
        · simp only [PushSuffix.nonzero, Fml.tmSize, Tm.size, Simple.lower_size, Tm.zero]; omega
        · simp only [Upd.length]; omega
        · simp only [Upd.tmSize]; omega
        · simp only [PushSuffix.saveOp, Upd.length]; omega
        · exact this se
      · apply Premise.Bounded.updates
        · simp only [Upd.length]; omega
        · simp only [Upd.tmSize]; omega
        · simp only [PushSuffix.saveOp, Upd.length]; omega
        · exact this se
    · bnil
  | _ => bnil

theorem pushIncStep_bounded {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) :
    (pushIncStep k op hp b).Bounded (12 * b.size + 18) := by
  have := UpdElem.pushSlot_size b
  simp only [pushIncStep]
  split
  · apply Premise.Bounded.updates
    · simp only [Upd.length]; omega
    · simp only [Upd.tmSize]; omega
    · simp only [PushSuffix.saveOp, Upd.length]; omega
    · exact PushSuffix.saveOp_tmSize _ _ hp b _
  · bnil

theorem pushStep_bounded {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) :
    (pushStep k b v hd).Bounded
      (3 * (b.size + (match v with | some e => e.size | none => 0)) + 6) := by
  have := UpdElem.pushSlot_size b
  cases v with
  | none =>
    simp only [pushStep]
    split
    · split
      · exact .upd1 (by omega)
      · split
        · exact .upd1 (by simp only [UpdElem.extend]; omega)
        · exact .upd1 (by omega)
    · bnil
  | some e =>
    cases e with
    | val e =>
      cases e with
      | simple se =>
        simp only [pushStep]
        split
        · exact .upd1 (Nat.le_trans (UpdElem.push_size b _) (by omega))
        · bnil
      | _ => simp only [pushStep]; split <;> bnil
    | copy p hm =>
      simp only [pushStep]
      split
      · split
        · exact .upd1 (Nat.le_trans (UpdElem.push_size b _) (by omega))
        · bnil
      · bnil
    | copyMem p =>
      simp only [pushStep]
      split
      · split
        · exact .upd1 (Nat.le_trans (UpdElem.push_size b _) (by omega))
        · bnil
      · bnil
    | fixedCopy p shape hm | fixedCopyMem p shape =>
      simp only [pushStep]
      split
      · exact .upd1 (Nat.le_trans (UpdElem.push_size b _) (by omega))
      · bnil

theorem popStep_bounded {E : Ty} (b : SPath C Γ (.array E)) :
    (popStep k b).Bounded (3 * b.size + 3) := by
  simp only [popStep]
  split
  · split
    · exact .upd1 (UpdElem.shrink_size b)
    · exact .upd1 (UpdElem.pop_size b)
  · bnil

theorem transferStep_bounded (m : Modality) (r a : Val C Γ .uint) :
    (transferStep k m r a).Bounded 3 := by
  cases r with
  | simple sadr =>
    cases a with
    | simple se =>
      cases m with
      | box => exact .upd1 (Nat.le_of_eq (UpdElem.payTo_size sadr se))
      | diamond => bnil
    | _ => bnil
  | _ => bnil

theorem sendStep_bounded (m : Modality) (pv : Idx Γ (.val .bool)) (full : Bool)
    (r a : Val C Γ .uint) : (sendStep k m pv full r a).Bounded 5 := by
  cases r with
  | simple sadr =>
    cases a with
    | simple se =>
      have hus : ∀ U ∈ [(Upd.nil.snoc (UpdElem.payTo sadr se)).snoc
          (.local pv (.val (Tm.lit (p := .bool) true))),
          (Upd.nil.snoc (.local pv (.val (Tm.lit (p := .bool) false))) : Upd C Γ Γ)],
          U.length ≤ 2 ∧ U.tmSize ≤ 5 := by
        intro U hU
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hU
        rcases hU with rfl | rfl
        · have h2 : (UpdElem.local (C := C) (Γ := Γ) pv (.val (Tm.lit (p := .bool) true))).size = 2 :=
            rfl
          simp only [Upd.length, Upd.tmSize]
          rw [UpdElem.payTo_size, h2]; omega
        · simp only [Upd.length, Upd.tmSize, UpdElem.size, Rhs.size, Tm.size]; omega
      cases m with
      | box => exact .cases (fun φ hφ => absurd hφ List.not_mem_nil) hus
      | diamond =>
        refine .cases (fun φ hφ => ?_) hus
        simp only [List.mem_singleton] at hφ
        subst hφ
        simp only [Fml.tmSize, Tm.size, Simple.lower_size]; omega
    | _ => bnil
  | _ => bnil

/-! ### Memory -/

theorem rebindMemStep_bounded {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) :
    (rebindMemStep k i r).Bounded (6 * r.size + 4) := by
  cases r with
  | alias p =>
    cases p with
    | var j hj =>
      apply Premise.Bounded.upd1
      simp only [UpdElem.size, Rhs.size, MPath.lower, Tm.size]; omega
    | loc l =>
      apply MHole.readStep_bounded
      · intro s mv hmv f hf e; subst e
        apply Premise.Bounded.upd1
        simp only [UpdElem.size, Rhs.size, MPath.lower, MLoc.lower, Tm.mread, Tm.size,
          MRhs.size, MPath.size, MLoc.size]; omega
      · intro R a mv hmv ie e; subst e
        apply Premise.Bounded.upd1
        simp only [UpdElem.size, Rhs.size, MPath.lower, MLoc.lower, Tm.mread, Val.lower,
          Simple.lower_size, Tm.size, MRhs.size, MPath.size, MLoc.size, Val.size, Simple.size]
        omega
  | copy sp hm =>
    have := SPath.lower_size sp
    simp only [rebindMemStep]
    split
    · apply Premise.Bounded.update
      · simp only [Upd.allocCopy, Upd.length]; omega
      · simp only [Upd.allocCopy, Upd.tmSize, UpdElem.size, Rhs.size, Tm.size, MRhs.size]; omega
    · bnil
  | newArr n h =>
    apply Premise.Bounded.update
    · simp only [Upd.allocCopy, Upd.length]; omega
    · simp only [Upd.allocCopy, Upd.tmSize, UpdElem.size, Rhs.size, Tm.size, Simple.lower_size,
        MRhs.size, Simple.size]; omega

theorem memRefStep_bounded {R : RefTy} (l : MLoc C Γ (.ref R)) (src : MPath C Γ (.ref R)) :
    (memRefStep k l src).Bounded (3 * (l.size + src.size) + 6) := by
  cases src with
  | var y hy =>
    apply Premise.Bounded.upd1
    have := UpdElem.writeMem_size l (.ref (.var y hy))
    simp only [MSrc.size, MPath.size] at this ⊢; omega
  | loc sl =>
    apply MHole.readStep_bounded
    · intro s mv hmv f hf e; subst e
      apply Premise.Bounded.upd1
      have := UpdElem.writeMem_size l (.ref (.loc (.field (.var mv hmv) f hf)))
      simp only [MSrc.size, MPath.size, MLoc.size] at this ⊢; omega
    · intro R a mv hmv ie e; subst e
      apply Premise.Bounded.upd1
      have := UpdElem.writeMem_size l (.ref (.loc (.index a (.var mv hmv) (.simple ie))))
      simp only [MSrc.size, MPath.size, MLoc.size, Val.size, Simple.size] at this ⊢; omega

theorem assignMemStep_bounded {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    (assignMemStep k l r).Bounded (3 * (l.size + r.size) + 9) := by
  cases l with
  | field b f hf =>
    cases b with
    | var mv hmv =>
      cases r with
      | val e =>
        apply VHole.step_bounded
        intro se
        apply Premise.Bounded.upd1
        have := UpdElem.writeMem_size (.field (.var mv hmv) f hf) (.val (.simple se))
        have := Val.one_le_size e
        have h3 : (MSrc.val (Val.simple se)).size = 3 := rfl
        have he : (MSrc.val e).size = 1 + e.size := rfl
        omega
      | ref src =>
        exact (memRefStep_bounded k _ src).mono (by simp only [MSrc.size]; omega)
    | loc _ => cases r <;> bnil
  | index a b i =>
    cases b with
    | var mv hmv =>
      cases i with
      | simple ie =>
        cases r with
        | val e =>
          apply VHole.step_bounded
          intro se
          apply Premise.Bounded.upd1
          have := UpdElem.writeMem_size (.index a (.var mv hmv) (.simple ie)) (.val (.simple se))
          have := Val.one_le_size e
          have h3 : (MSrc.val (Val.simple se)).size = 3 := rfl
          have he : (MSrc.val e).size = 1 + e.size := rfl
          omega
        | ref src =>
          exact (memRefStep_bounded k _ src).mono (by simp only [MSrc.size]; omega)
      | _ => cases r <;> bnil
    | loc _ => cases r <;> bnil

theorem clearMem_bounded (T : Ty) (a : Tm C Γ (.addr T)) (h : T.mapFree = true) :
    (Premise.clearMem T a h).Bounded (a.size + 7) := by
  cases T with
  | prim q =>
    apply Premise.Bounded.upd1
    simp only [UpdElem.clearMem, UpdElem.size, Tm.size]; omega
  | ref R =>
    apply Premise.Bounded.upd1
    simp only [UpdElem.clearMem, UpdElem.size, Tm.size]; omega

theorem deleteMemStep_bounded {T : Ty} (p : MPath C Γ T) (hd : T.defaultOkS = true) :
    (deleteMemStep k p hd).Bounded (3 * p.size + 7) := by
  cases p with
  | var i hm =>
    apply Premise.Bounded.update
    · simp only [Upd.allocFresh, Upd.length]; omega
    · simp only [Upd.allocFresh, Upd.tmSize, UpdElem.size, Rhs.size, Tm.size]; omega
  | loc l =>
    cases l with
    | field b f hf =>
      cases b with
      | var mv hmv =>
        refine (clearMem_bounded _ _ _).mono ?_
        have := MLoc.lower_size (MLoc.field (.var mv hmv) f hf)
        simp only [MPath.size] at this ⊢; omega
      | loc _ => bnil
    | index a b i =>
      cases b with
      | var mv hmv =>
        cases i with
        | simple ie =>
          refine (clearMem_bounded _ _ _).mono ?_
          have := MLoc.lower_size (MLoc.index a (.var mv hmv) (.simple ie))
          simp only [MPath.size] at this ⊢; omega
        | _ => bnil
      | loc _ => bnil

/-! ### Control flow -/

/-- What a joinable branch assigns is a part of it: `{ x = x + 1; }`
assigns `x + 1`, of fewer nodes than the branch. -/
theorem Prog.joinArm?_size {Γ₁ : Ctx} (P : Prog C Γ Γ₁) {p : PrimTy} {i : Idx Γ (.val p)}
    {r : Val C Γ p} (h : P.joinArm? = some (some ⟨p, i, r⟩)) : r.size + 1 ≤ P.size := by
  cases P with
  | nil => cases h
  | cons s ω =>
    cases s <;> try cases h
    rename_i i' r'
    cases ω with
    | nil =>
      cases h
      simp only [Prog.size, Stmt.size]; omega
    | cons _ _ => cases h

/-- The joined update of two branches has at most two elements, each at
most three nodes a node of the branches, and the condition's. -/
theorem Upd.ifJoin_bounded (se : Simple C Γ .bool) {Γ₁ Γ₂ : Ctx} {thn : Prog C Γ Γ₁}
    {els : Prog C Γ Γ₂} {a b : JoinArm C Γ} (ha : thn.joinArm? = some a)
    (hb : els.joinArm? = some b) :
    (Upd.ifJoin se.lower a b).length ≤ 2 ∧
      (Upd.ifJoin se.lower a b).tmSize ≤ 3 * (thn.size + els.size) + 8 := by
  rcases a with _ | ⟨p, i, ra⟩ <;> rcases b with _ | ⟨q, j, rb⟩
  · simp only [Upd.ifJoin, Upd.length, Upd.tmSize]; omega
  · have := Prog.joinArm?_size els hb
    have := Val.lower_size rb
    simp only [Upd.ifJoin, Upd.length, Upd.tmSize, UpdElem.size, Rhs.size, Tm.size,
      Simple.lower_size]; omega
  · have := Prog.joinArm?_size thn ha
    have := Val.lower_size ra
    simp only [Upd.ifJoin, Upd.length, Upd.tmSize, UpdElem.size, Rhs.size, Tm.size,
      Simple.lower_size]; omega
  · have := Prog.joinArm?_size thn ha
    have := Prog.joinArm?_size els hb
    have := Val.lower_size ra
    have := Val.lower_size rb
    simp only [Upd.ifJoin]
    repeat' split
    all_goals simp only [Upd.length, Upd.tmSize, UpdElem.size, Rhs.size, Tm.size,
      Simple.lower_size, Tm.size_castV]
    all_goals omega

theorem iteStep_bounded {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) : (iteStep k c thn els).Bounded (3 * (thn.size + els.size) + 8) := by
  cases c with
  | simple s =>
    have hsplit : (Premise.split .block (Fml.isBool s.lower true) (Fml.isBool s.lower false)
        thn els).Bounded (3 * (thn.size + els.size) + 8) := by
      apply Premise.Bounded.split <;>
        simp only [Fml.tmSize, Tm.size, Simple.lower_size] <;> omega
    cases ha : thn.joinArm? with
    | none => simp only [iteStep, Upd.ifJoin?, ha]; exact hsplit
    | some a =>
      cases hb : els.joinArm? with
      | none => simp only [iteStep, Upd.ifJoin?, ha, hb]; exact hsplit
      | some b =>
        simp only [iteStep, Upd.ifJoin?, ha, hb]
        obtain ⟨hl, hs⟩ := Upd.ifJoin_bounded s ha hb
        exact Premise.Bounded.update hl hs
  | _ => bnil

theorem requireStep_bounded (c : Val C Γ .bool) : (requireStep k c).Bounded 3 := by
  cases c with
  | simple s =>
    apply Premise.Bounded.split <;>
      simp only [Fml.tmSize, Tm.size, Simple.lower_size] <;> omega
  | _ => bnil

theorem assertStep_bounded (c : Val C Γ .bool) : (assertStep k c).Bounded 3 := by
  cases c with
  | simple s =>
    apply Premise.Bounded.check
    simp only [Fml.tmSize, Tm.size, Simple.lower_size]; omega
  | _ => bnil

/-! ### Loops -/

/-- Every typed metric tuple carries at least its spine node. -/
theorem LoopMetrics.size_pos (metrics : LoopMetrics C Γ n) : 0 < metrics.size := by
  cases metrics <;> simp only [LoopMetrics.size] <;> omega

/-- Erasing a tuple annotation strictly reduces syntax size, even when the
runtime loop and its invariant remain identical. -/
theorem LoopAnn.lex_erasure_size (I : Val C Γ .bool) (metrics : LoopMetrics C Γ (n + 2))
    (brk : Bool) (qs : List (LoopQ C Γ)) :
    (LoopAnn.inv I none brk qs).size < (LoopAnn.invLex I metrics brk qs).size := by
  have h := metrics.size_pos
  simp only [LoopAnn.size]
  omega

theorem LoopQ.toFml_size : {Γ : Ctx} → (q : LoopQ C Γ) → q.toFml.tmSize ≤ 3 * q.size + 2
  | _, .val a => by
    have := Val.lower_size a
    simp only [LoopQ.toFml, Fml.isBool, Fml.tmSize, Tm.size, LoopQ.size]; omega
  | _, .imp a c => by
    have := Val.lower_size a
    have := Val.lower_size c
    simp only [LoopQ.toFml, Fml.isBool, Fml.tmSize, Tm.size, LoopQ.size]; omega
  | _, .all _ _ b => by
    have := LoopQ.toFml_size b
    simp only [LoopQ.toFml, Fml.tmSize, LoopQ.size]; omega

theorem invFml_foldl_size (qs : List (LoopQ C Γ)) (acc : Fml C Γ) :
    (qs.foldl (fun acc q => Fml.and acc q.toFml) acc).tmSize ≤
      acc.tmSize + 6 * (qs.map LoopQ.size).sum := by
  induction qs generalizing acc with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil]; omega
  | cons q qs ih =>
    have h := ih (Fml.and acc q.toFml)
    have hq := LoopQ.toFml_size q
    have h1 : 1 ≤ q.size := by cases q <;> simp only [LoopQ.size] <;> omega
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    simp only [Fml.tmSize] at h
    omega

/-- Adding ghost locals preserves the size of a quantified loop clause. -/
theorem LoopQ.size_wk {Γ Δ : Ctx} (h : Thin Γ Δ) (q : LoopQ C Γ) :
    (q.wk h).size = q.size := by
  induction q generalizing Δ with
  | val a => simp only [LoopQ.wk, LoopQ.size, Val.size_wk]
  | imp a b => simp only [LoopQ.wk, LoopQ.size, Val.size_wk]
  | all x p b ih => simp only [LoopQ.wk, LoopQ.size, ih]

/-- Shifting a clause under a scalar variant does not grow it. -/
theorem LoopQ.size_up {t : LTy} (q : LoopQ C Γ) :
    (q.up (t := t)).size = q.size := LoopQ.size_wk _ q

theorem invFml_size (I : Val C Γ .bool) (qs : List (LoopQ C Γ)) :
    (invFml I qs).tmSize ≤ 3 * I.size + 2 + 6 * (qs.map LoopQ.size).sum := by
  have h := invFml_foldl_size qs (Fml.isBool I.lower true)
  have := Val.lower_size I
  have h0 : (Fml.isBool I.lower true).tmSize = 2 + I.lower.size := by
    simp only [Fml.tmSize, Tm.size]; omega
  unfold invFml
  omega

theorem loopBreak_size (brk : Bool) (c : Val C Γ .bool) :
    ∀ b, loopBreak brk c = some b → b.tmSize ≤ 3 := by
  intro b hb
  simp only [loopBreak, Option.map_eq_some_iff] at hb
  obtain ⟨x, -, rfl⟩ := hb
  simp only [Fml.tmSize, Tm.size]; omega

theorem LoopMetrics.size_wk {Δ : Ctx} (h : Thin Γ Δ) (metrics : LoopMetrics C Γ n) :
    (metrics.wk h).size = metrics.size := by
  induction metrics with
  | nil => rfl
  | cons head tail ih => simp only [LoopMetrics.wk, LoopMetrics.size, Val.size_wk, ih]

/-- Every component contributes its own node and at least one expression node. -/
theorem LoopMetrics.arity_size (metrics : LoopMetrics C Γ n) : 2 * n + 1 ≤ metrics.size := by
  induction metrics with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    have := Val.one_le_size head
    simp only [LoopMetrics.size]
    omega

/-- All tuple components are explicit update elements. -/
theorem LoopLex.snapshot_length (metrics : LoopMetrics C Γ n) :
    (LoopLex.snapshot k metrics).length = n := by
  induction metrics generalizing k with
  | nil => rfl
  | cons head tail ih => simp only [LoopLex.snapshot, Upd.length, ih]

theorem LoopLex.snapshot_tmSize (metrics : LoopMetrics C Γ n) :
    (LoopLex.snapshot k metrics).tmSize ≤ 3 * metrics.size := by
  induction metrics generalizing k with
  | nil => simp only [LoopLex.snapshot, Upd.tmSize, LoopMetrics.size]; omega
  | cons head tail ih =>
    have := Val.lower_size head
    have := ih (k + 1)
    simp only [LoopLex.snapshot, Upd.tmSize, Rhs.size, LoopMetrics.size]
    omega

/-- The comparison is linear in arity and counts every connective. -/
theorem LoopLex.lexFml_tmSize (a b : LoopLex.Refs Γ n) :
    (LoopLex.lexFml (C := C) a b).tmSize = 13 * n + 2 := by
  induction a with
  | nil => cases b; rfl
  | cons head tail ih =>
    cases b with
    | cons other rest =>
      simp only [LoopLex.lexFml, Fml.tmSize, Tm.size, ih]
      omega

/-- Tuple VCs have an explicit arity-plus-condition update budget, and a
proved linear node bound. Nested new-value snapshots are counted in the post. -/
theorem LoopLex.diamondPremise_bounded {Γ₁ : Ctx} (I c : Val C Γ .bool)
    (metrics : LoopMetrics C Γ n) (body : Prog C Γ Γ₁)
    (xs : List ((t : LTy) × Idx Γ t)) (hv : Option (List Name)) :
    (LoopLex.diamondPremise k I c metrics body xs hv).Bounded
      (12 * (I.size + metrics.size + c.size) + 30) (n + 1) := by
  have hI := Val.lower_size I
  have hc := Val.lower_size c
  have hm := LoopLex.snapshot_tmSize k metrics
  have hn := metrics.arity_size
  have hiw := Val.lower_size (I.wk (.ofExt (LoopLex.savedExt Γ n)))
  rw [Val.size_wk] at hiw
  have hmw := LoopLex.snapshot_tmSize (k + n + 1)
    (metrics.wk (.ofExt (LoopLex.savedExt Γ n)))
  rw [LoopMetrics.size_wk] at hmw
  unfold LoopLex.diamondPremise
  apply Premise.Bounded.inv
  · simp only [Fml.tmSize, Tm.size]; omega
  · intro b hb; cases hb
  · simp only [Upd.length, LoopLex.snapshot_length]
    exact Nat.le_refl _
  · simp only [Upd.tmSize, Rhs.size]; omega
  · simp only [Fml.tmSize, Tm.size]; omega
  · simp only [Fml.tmSize, Tm.size]; omega
  · simp only [LoopLex.diamondPost, LoopLex.snapshotsDecrease, Fml.tmSize, Tm.size,
      LoopLex.lexFml_tmSize]
    omega

/-- A tuple's arity is retained by its type, independently of its values. -/
def LoopMetrics.arity {Γ : Ctx} {n : Nat} (_ : LoopMetrics C Γ n) : Nat := n

/-- Only the selected lexicographic diamond dispatch has a larger update:
all old components followed by one condition capture. Other dispatches keep
 their established two-element limit. -/
def LoopAnn.updateLimit {Γ : Ctx} (m : Modality)
    (frame : Option (List ((t : LTy) × Idx Γ t) × Option (List Name))) : LoopAnn C Γ → Nat
  | .invLex _ metrics brk qs =>
      if LoopLex.eraseAllowed m brk qs frame then 2 else metrics.arity + 1
  | _ => 2

theorem loopStep_bounded_two (m : Modality) {Γ₁ : Ctx} (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) (hlimit : a.updateLimit m body.frame = 2) :
    (loopStep k m a c body).Bounded (6 * (a.size + c.size) + 18) := by
  have hc := Val.lower_size c
  cases a with
  | unwind n =>
    cases n with
    | zero =>
      apply Premise.Bounded.check
      simp only [Fml.tmSize, Upd.tmSize, Rhs.size, Tm.size]; omega
    | succ n => bnil
  | auto => bnil
  | invLex I metrics brk qs =>
    cases m <;> cases brk <;> cases qs <;> cases hf : body.frame <;>
      simp only [LoopAnn.updateLimit, LoopMetrics.arity, LoopLex.eraseAllowed, hf,
        Bool.false_eq_true, ↓reduceIte] at hlimit <;>
      first | omega | (simp only [loopStep, hf]; bnil)
  | inv I dec brk qs =>
    have hI := Val.lower_size I
    have hinv := invFml_size I qs
    simp only [loopStep]
    split
    · bnil
    · split
      · apply Premise.Bounded.inv
        · simp only [LoopAnn.size]; omega
        · intro b hb; have := loopBreak_size brk c b hb; omega
        · simp only [Upd.length]; omega
        · simp only [Upd.tmSize, Rhs.size, LoopAnn.size]; omega
        · simp only [Fml.tmSize, Tm.size]; omega
        · simp only [Fml.tmSize, Tm.size]; omega
        · simp only [LoopAnn.size]; omega
      · rename_i d
        have hd := Val.lower_size d
        have hIu := invFml_size (I.up (t := .val .uint)) (qs.map LoopQ.up)
        simp only [List.map_map, Function.comp_def, LoopQ.size_up, Val.size_up] at hIu
        change (invFml I.up (qs.map LoopQ.up)).tmSize ≤
          3 * I.size + 2 + 6 * (qs.map LoopQ.size).sum at hIu
        have hcu := Val.lower_size (c.up (t := .val .uint))
        have hdu := Val.lower_size ((d.up (t := .val .uint)).up (t := .val .bool))
        rw [Val.size_up] at hcu
        rw [Val.size_up, Val.size_up] at hdu
        apply Premise.Bounded.inv
        · simp only [LoopAnn.size]; omega
        · intro b hb; cases hb
        · simp only [Upd.length]; omega
        · simp only [Upd.tmSize, Rhs.size, LoopAnn.size]; omega
        · simp only [Fml.tmSize, Tm.size]; omega
        · simp only [Fml.tmSize, Tm.size]; omega
        · simp only [Fml.tmSize, Upd.tmSize, Rhs.size, Tm.size, LoopAnn.size]
          omega
      · bnil

/-- The original local coefficient is retained for every two-element
(non-lexicographic) dispatch. The tuple case uses a proved larger local bound;
the global statement coefficient remains sixteen. -/
theorem loopStep_bounded (m : Modality) {Γ₁ : Ctx} (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) :
    (loopStep k m a c body).Bounded (12 * (a.size + c.size) + 30)
      (a.updateLimit m body.frame) := by
  cases a with
  | unwind n =>
    exact (loopStep_bounded_two k m (.unwind n) c body rfl).mono (by omega)
  | auto => exact (loopStep_bounded_two k m .auto c body rfl).mono (by omega)
  | inv I dec brk qs =>
    exact (loopStep_bounded_two k m (.inv I dec brk qs) c body rfl).mono (by omega)
  | invLex I metrics brk qs =>
    cases m with
    | box => bnil
    | diamond =>
      cases brk with
      | true => bnil
      | false =>
        cases qs with
        | cons q qs => bnil
        | nil =>
          cases hf : body.frame with
          | none => simp only [loopStep, hf]; bnil
          | some frame =>
            obtain ⟨xs, hv⟩ := frame
            simpa only [loopStep, hf, LoopAnn.updateLimit, LoopLex.eraseAllowed,
              Bool.false_eq_true, ↓reduceIte, LoopMetrics.arity, LoopAnn.size,
              List.map_nil, List.sum_nil, Nat.add_zero] using
              (LoopLex.diamondPremise_bounded k I c metrics body xs hv).mono
                (n' := 12 * ((LoopAnn.invLex I metrics false []).size + c.size) + 30)
                (by simp only [LoopAnn.size, List.map_nil, List.sum_nil]; omega)

/-! ### Calls, `try`, receivers -/

/-- A term read through a frame of one-node terms keeps its nodes. -/
theorem Tm.size_substE {Γ₀ Δ : Ctx} {E : SEnv C Γ₀ Δ}
    (hE : ∀ {p : PrimTy} (i : Idx Δ (.val p)), (E.get i).1.size = 1) :
    {s : Srt} → (t : Tm C Δ s) → {t' : Tm C Γ₀ s} → t.substE E = some t' → t'.size = t.size
  | _, .pvV i, _, h => by cases h; exact hE i
  | _, .app0 _, _, h => by cases h; rfl
  | _, .app1 o x, t', h => by
    have h' : (x.substE E).map (Tm.app1 o) = some t' := h
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h'
    simp only [Tm.size, Tm.size_substE hE x hx]
  | _, .app2 o x y, t', h => by
    have h' : (x.substE E).bind (fun x' => (y.substE E).map fun y' => Tm.app2 o x' y') =
      some t' := h
    obtain ⟨x', hx, h₁⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨y', hy, rfl⟩ := Option.map_eq_some_iff.1 h₁
    simp only [Tm.size, Tm.size_substE hE x hx, Tm.size_substE hE y hy]
  | _, .app3 o x y z, t', h => by
    have h' : (x.substE E).bind (fun x' => (y.substE E).bind fun y' =>
      (z.substE E).map fun z' => Tm.app3 o x' y' z') = some t' := h
    obtain ⟨x', hx, h₁⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨y', hy, h₂⟩ := Option.bind_eq_some_iff.1 h₁
    obtain ⟨z', hz, rfl⟩ := Option.map_eq_some_iff.1 h₂
    simp only [Tm.size, Tm.size_substE hE x hx, Tm.size_substE hE y hy, Tm.size_substE hE z hz]
  | _, .pvP _, _, h | _, .pvS _, _, h | _, .pvI _, _, h | _, .netOf _ _, _, h
  | _, .pvZ _, _, h => nomatch h

theorem Simple.lower_size_one {p : PrimTy} (s : Simple C Γ p) : s.lower.size = 1 := by
  cases s with
  | env k hp => simp only [Simple.lower, Tm.size_castV]; rfl
  | _ => rfl

/-- The arguments of a call read at the call: one node each. -/
theorem Args.sym_id_size : {ps : Ctx} → (args : Args C Γ ps) → {θ : SEnv C Γ ps} →
    Args.sym (SEnv.id Γ) args = some θ →
    ∀ {p : PrimTy} (i : Idx ps (.val p)), (θ.get i).1.size = 1
  | _, .nil, _, _ => fun i => nomatch i
  | _, .snoc as p x e, θ, h => by
    cases e with
    | simple s =>
      have h' : (s.lower.substE (SEnv.id Γ)).bind
          (fun t => (Args.sym (SEnv.id Γ) as).map fun θ => ((t, false), θ)) = some θ := h
      obtain ⟨t, ht, h₁⟩ := Option.bind_eq_some_iff.1 h'
      obtain ⟨θ', hθ', rfl⟩ := Option.map_eq_some_iff.1 h₁
      intro i
      cases i with
      | here =>
        show t.size = 1
        rw [Tm.size_substE (fun j => by rw [SEnv.id, SEnv.get_idAt]; rfl) s.lower ht,
          Simple.lower_size_one]
      | there i => exact Args.sym_id_size as hθ' i
    | _ => exact nomatch h
  | _, .snocStorage .., _, h | _, .snocMemory .., _, h => nomatch h

/-- **A summary's update is no larger than the callee's body bounds**: one
element, its term the summary's own nodes (`Tm.sumGate`). -/
theorem CallRet.summary?_bounded {ps rs Γ' Γf : Ctx} {args : Args C Γ ps}
    {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {U : Upd C Γ Γ'}
    (h : CallRet.summary? args ret body = some U) :
    U.length ≤ 2 ∧ U.tmSize ≤ 16 * body.size + 16 := by
  cases ret with
  | val p r res =>
    cases res with
    | none => exact nomatch h
    | some j =>
      have h' : (if body.hasCall then
          (CallRet.sumOf body.ext (body.sym _ (SEnv.id _))).bind fun R =>
            if Tm.sumGate body R then
              (Args.sym (SEnv.id Γ) args).bind fun θ =>
                (Tm.substE (Γ₀ := Γ) (Δ := .val p :: ps)
                  ((Tm.app0 (.lit (PrimTy.dflt p)), false), θ) R).map fun t =>
                    Upd.nil.snoc (.local j (.val t))
            else Option.none
          else Option.none) = some U := h
      split at h'
      · obtain ⟨R, _, h₁⟩ := Option.bind_eq_some_iff.1 h'
        split at h₁
        · rename_i hgate
          obtain ⟨θ, hθ, h₂⟩ := Option.bind_eq_some_iff.1 h₁
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h₂
          have hR : R.size < 16 * body.size + 16 := by
            simp only [Tm.sumGate, Bool.and_eq_true, decide_eq_true_eq] at hgate; exact hgate.2
          have hts : t.size = R.size := by
            refine Tm.size_substE (E := (show SEnv C Γ (.val p :: ps) from
              ((Tm.app0 (.lit (PrimTy.dflt p)), false), θ))) ?_ R ht
            intro q i
            cases i with
            | here => rfl
            | there i => exact Args.sym_id_size args hθ i
          refine ⟨by simp only [Upd.length]; omega, ?_⟩
          simp only [Upd.tmSize, UpdElem.size, Rhs.size, hts]
          omega
        · cases h₁
      · cases h'
  | none => exact nomatch h
  | rets _ => exact nomatch h
  | mem _ _ _ _ => exact nomatch h
  | storage _ _ => exact nomatch h

theorem callStep_bounded {Γ' ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) (n : Nat)
    (hn : 16 * body.size + 16 ≤ n) :
    (callStep k f args ret body).Bounded n := by
  cases ret with
  | val p r res =>
    simp only [callStep]
    split
    · bnil
    · split
      · rename_i U hU
        obtain ⟨hl, hs⟩ := CallRet.summary?_bounded hU
        exact Premise.Bounded.update hl (by omega)
      · bnil
  | _ => simp only [callStep]; split <;> bnil

theorem tryStep_bounded (m : Modality) {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (rets : Binders ρ)
    (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂) (code : CodeBinder κ)
    (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (n : Nat) :
    (tryStep m rets ok err code pnc other).Bounded n := by
  cases m <;> bnil

theorem tryStepS_bounded (m : Modality) {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (call : ExtCall C Γ)
    (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂) (code : CodeBinder κ)
    (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (sargs : Args C Γ ps)
    (sbody : Prog C (ρ ++ ps) Γf) (self : Bool) (n : Nat) :
    (tryStepS m call rets ok err code pnc other sargs sbody self).Bounded n := by
  cases self <;> cases m <;> bnil

theorem ReceiverValue.step_bounded {ps Γf : Ctx} {E : Ty} (f : Name) (args : Args C Γ ps)
    (r : Var) (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : ReceiverValue C Γ E)
    (n : Nat) : (ReceiverValue.step k f args r body e).Bounded n := by
  cases e <;> bnil

end Arms

/-- The update-element budget of the actual dispatch. It is two for
all non-lexicographic dispatches, and tuple arity plus one for the selected
ordinary lexicographic diamond rule. -/
def Stmt.updateLimit (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Nat :=
  Stmt.casesOn (motive_1 := fun _ _ _ => Nat) s
    (assign := fun _ _ => 2) (rebind := fun _ _ => 2) (assignLocal := fun _ _ => 2)
    (declLocal := fun _ _ _ => 2) (declStorage := fun _ _ _ => 2)
    (opAssign := fun _ _ _ _ _ => 2) (incDec := fun _ _ _ => 2)
    (assignIncDec := fun _ _ _ _ _ => 2) (assignLocalPush := fun _ _ => 2)
    (push := fun _ _ _ => 2) (pop := fun _ => 2)
    (transfer := fun _ _ => 2) (send := fun _ _ _ _ => 2)
    (declMem := fun _ _ _ _ _ => 2) (rebindMem := fun _ _ => 2)
    (assignFromMem := fun _ _ => 2) (assignMem := fun _ _ => 2) (delete := fun _ => 2)
    (deleteMem := fun _ _ => 2) (assignNew := fun _ _ _ => 2)
    (ite := fun _ _ _ => 2) (require := fun _ => 2) (assert := fun _ => 2)
    (revert := 2) (assumeFalse := 2) (call := fun _ _ _ _ => 2)
    (tryCall := fun _ _ _ _ _ _ _ _ _ _ => 2)
    (loop := fun a _ body => a.updateLimit m body.frame) (block := fun _ => 2)
    (pushOpAssign := fun _ _ _ _ _ => 2) (pushIncDec := fun _ _ _ => 2)
    (callReceiver := fun _ _ _ _ _ => 2) (callReceiverPush := fun _ _ _ _ _ _ => 2)
    (callRec := fun _ _ _ _ _ => 2) (revertData := fun _ => 2)
    (catchData := fun _ _ _ _ _ _ _ _ => 2)

/-! ## Every rule -/

section Step

variable (k : Nat) (m : Modality)

/-- **Every rule is bounded by its statement**: the explicit update-length
budget of its dispatch, and every emitted term of at most `16 * s.size + 16`
nodes, including all tuple snapshots and lexicographic comparisons. -/
theorem Stmt.step_bounded {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :
    (s.step k m).Bounded (16 * s.size + 16) (s.updateLimit m) := by
  cases s with
  | assign l r => exact (assignStep_bounded k l r).mono (by simp only [Stmt.size]; omega)
  | rebind i r => exact (rebindStep_bounded k i r).mono (by simp only [Stmt.size]; omega)
  | assignLocal i v => exact (localStep_bounded k i v).mono (by simp only [Stmt.size]; omega)
  | declLocal p x init =>
    cases init with
    | none =>
      apply Premise.Bounded.update
      · simp only [Upd.length]; omega
      · simp only [Upd.tmSize, Rhs.size, Tm.size]; omega
    | some e => bnil
  | declStorage R x init =>
    cases init with
    | none =>
      apply Premise.Bounded.update
      · simp only [Upd.length]; omega
      · simp only [Upd.tmSize, Rhs.size]; omega
    | some r => bnil
  | opAssign op hop hp l r =>
    exact (opStep_bounded k op hop hp l r).mono (by simp only [Stmt.size]; omega)
  | incDec op hp l => exact (incStep_bounded k op hp l).mono (by simp only [Stmt.size]; omega)
  | assignIncDec i op hp l _ =>
    exact (assignIncStep_bounded i op hp l).mono (by simp only [Stmt.size]; omega)
  | assignLocalPush i b =>
    exact (assignLocalPushStep_bounded k i b).mono (by simp only [Stmt.size]; omega)
  | push b v hd =>
    exact (pushStep_bounded k b v hd).mono (by cases v <;> simp only [Stmt.size] <;> omega)
  | pop b => exact (popStep_bounded k b).mono (by simp only [Stmt.size]; omega)
  | transfer r a => exact (transferStep_bounded k m r a).mono (by omega)
  | send pv r a full => exact (sendStep_bounded k m pv full r a).mono (by omega)
  | declMem R x init hd hm =>
    cases init with
    | none =>
      apply Premise.Bounded.update
      · simp only [Upd.length]; omega
      · simp only [Upd.tmSize, UpdElem.size, Rhs.size, Tm.size]; omega
    | some r => bnil
  | rebindMem i r => exact (rebindMemStep_bounded k i r).mono (by simp only [Stmt.size]; omega)
  | assignFromMem l p =>
    exact (assignFromMemStep_bounded k l p).mono (by simp only [Stmt.size]; omega)
  | assignMem l r => exact (assignMemStep_bounded k l r).mono (by simp only [Stmt.size]; omega)
  | delete l => exact (deleteStep_bounded k l).mono (by simp only [Stmt.size]; omega)
  | deleteMem p hd => exact (deleteMemStep_bounded k p hd).mono (by simp only [Stmt.size]; omega)
  | assignNew l n h => bnil
  | ite c thn els => exact (iteStep_bounded k c thn els).mono (by simp only [Stmt.size]; omega)
  | require c => exact (requireStep_bounded k c).mono (by omega)
  | assert c => exact (assertStep_bounded k c).mono (by omega)
  | revert => cases m <;> bnil
  | assumeFalse => bnil
  | call f args ret body =>
    exact callStep_bounded k f args ret body _ (by simp only [Stmt.size]; omega)
  | tryCall call rets ok err code pnc other sargs sbody self =>
    exact tryStepS_bounded m call rets ok err code pnc other sargs sbody self _
  | loop a c body =>
    exact (loopStep_bounded k m a c body).mono (by simp only [Stmt.size]; omega)
  | block body => bnil
  | pushOpAssign op hop hp b r =>
    exact (pushOpStep_bounded k op hop hp b r).mono (by simp only [Stmt.size]; omega)
  | pushIncDec op hp b =>
    exact (pushIncStep_bounded k op hp b).mono (by simp only [Stmt.size]; omega)
  | callReceiver f args r body op => bnil
  | callReceiverPush f args r body code value =>
    exact ReceiverValue.step_bounded k f args r body (.deferred code value) _
  | callRec f d args ret body => bnil
  | revertData d => cases m <;> bnil
  | catchData call rets sargs sbody self kind x body =>
    show (catchDataStep m call sbody self kind x body).Bounded _
    unfold catchDataStep
    split <;> bnil

/-- **Every generated update fits its source dispatch's explicit budget.** -/
theorem Stmt.step_upds_le {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :
    ∀ U ∈ (s.step k m).upds, U.2.2.length ≤ s.updateLimit m :=
  fun U hU => ((Stmt.step_bounded k m s).upds U hU).1

/-- **Non-lexicographic dispatches still write at most two elements per
update.** Their computed `updateLimit` is definitionally two; unsupported
lexicographic fragments also keep this limit through annotation erasure. -/
theorem Stmt.step_upds_le_two {Γ Γ' : Ctx} (s : Stmt C Γ Γ')
    (h : s.updateLimit m = 2) : ∀ U ∈ (s.step k m).upds, U.2.2.length ≤ 2 := by
  simpa only [h] using Stmt.step_upds_le k m s

/-- **Every term a rule emits is linear in its statement**, in an update or
in a formula, whatever the types. -/
theorem Stmt.step_tmSize_le {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :
    (∀ U ∈ (s.step k m).upds, U.2.2.tmSize ≤ 16 * s.size + 16) ∧
      (∀ φ ∈ (s.step k m).fmls, φ.2.tmSize ≤ 16 * s.size + 16) :=
  ⟨fun U hU => ((Stmt.step_bounded k m s).upds U hU).2,
   fun φ hφ => (Stmt.step_bounded k m s).fmls φ hφ⟩

end Step


end Solidity
