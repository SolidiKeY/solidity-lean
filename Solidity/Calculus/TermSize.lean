import Solidity.Calculus.Step

/-!
# The size of what a rule emits

Every rule of `Stmt.step` writes a bounded number of update elements
(`Stmt.step_upds_le`: at most two per update), and every term it emits, in
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
branches) is bounded by anything (`Premise.Bounded.of_nil`).
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## Sizes of terms, updates and formulas -/

/-- The nodes of a term. -/
def Tm.size {Γ : Ctx} : {s : Srt} → Tm C Γ s → Nat
  | _, .pvV _ => 1
  | _, .pvP _ => 1
  | _, .pvS _ => 1
  | _, .pvI _ => 1
  | _, .netOf _ a => 1 + a.size
  | _, .app0 _ => 1
  | _, .app1 _ x => 1 + x.size
  | _, .app2 _ x y => 1 + x.size + y.size
  | _, .app3 _ x y z => 1 + x.size + y.size + z.size
  | _, .pvZ _ => 1

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
  | _, .anon _ φ => 1 + φ.tmSize

/-! ## Sizes of statements -/

section Syntax

variable {Γ : Ctx}

/-- A simple value is one node. -/
def Simple.size {p : PrimTy} (_ : Simple C Γ p) : Nat := 1

mutual

def SPath.size : {T : Ty} → SPath C Γ T → Nat
  | _, .alias _ => 1
  | _, .loc l => 1 + l.size

def Loc.size : {T : Ty} → Loc C Γ T → Nat
  | _, .root _ _ => 1
  | _, .field b _ _ => 1 + b.size
  | _, .index _ b i => 1 + b.size + i.size

def MPath.size : {T : Ty} → MPath C Γ T → Nat
  | _, .var _ _ => 1
  | _, .loc l => 1 + l.size

def MLoc.size : {T : Ty} → MLoc C Γ T → Nat
  | _, .field b _ _ => 1 + b.size
  | _, .index _ b i => 1 + b.size + i.size

def Val.size : {p : PrimTy} → Val C Γ p → Nat
  | _, .simple s => 1 + s.size
  | _, .read l => 1 + l.size
  | _, .binop _ _ _ a b => 1 + a.size + b.size
  | _, .unop _ _ _ a => 1 + a.size
  | _, .ternary c a b => 1 + c.size + a.size + b.size
  | _, .readMem l => 1 + l.size
  | _, .len b _ => 1 + b.size
  | _, .mlen b _ => 1 + b.size
  | _, .modular _ a b k => 1 + a.size + b.size + k.size

end

def Src.size {T : Ty} : Src C Γ T → Nat
  | .val v => 1 + v.size
  | .copy p _ => 1 + p.size
  | .fixedCopy p _ _ => 1 + p.size
  | .copyMem p => 1 + p.size

def MSrc.size {T : Ty} : MSrc C Γ T → Nat
  | .val v => 1 + v.size
  | .ref p => 1 + p.size

def ARhs.size {R : RefTy} : ARhs C Γ R → Nat
  | .path p => 1 + p.size
  | .push b _ => 1 + b.size

def MRhs.size {R : RefTy} : MRhs C Γ R → Nat
  | .alias p => 1 + p.size
  | .copy p _ => 1 + p.size
  | .newArr n _ => 1 + n.size

def NewLhs.size {R : RefTy} : NewLhs C Γ R → Nat
  | .store l => 1 + l.size
  | .mem l => 1 + l.size

/-- A compound target, as the location it denotes (`OpLoc.set`). -/
def OpLoc.size {p : PrimTy} : OpLoc C Γ p → Nat
  | .local _ => 1
  | .root _ _ => 1
  | .field b _ _ => 1 + b.size
  | .index _ b _ => 3 + b.size
  | .mfield b _ _ => 1 + b.size
  | .mindex _ b _ => 3 + b.size

def Args.size : {ps : Ctx} → Args C Γ ps → Nat
  | _, .nil => 0
  | _, .snoc as _ _ e => as.size + 1 + e.size
  | _, .snocStorage as _ _ e => as.size + 1 + e.size
  | _, .snocMemory as _ _ e => as.size + 1 + e.size

def ExtCall.size (e : ExtCall C Γ) : Nat := 1 + e.addr.size + e.args.length

def ReceiverOp.size {E : Ty} : ReceiverOp C Γ E → Nat
  | .push none _ => 1
  | .push (some v) _ => 1 + v.size
  | .pop => 1

end Syntax

def LoopQ.size : {Γ : Ctx} → LoopQ C Γ → Nat
  | _, .val a => 1 + a.size
  | _, .imp a c => 1 + a.size + c.size
  | _, .all _ _ b => 1 + b.size

def LoopAnn.size {Γ : Ctx} : LoopAnn C Γ → Nat
  | .unwind _ => 1
  | .auto => 1
  | .inv I dec _ qs => 1 + I.size + (match dec with | some d => d.size | none => 0) +
      (qs.map LoopQ.size).sum

mutual

/-- The nodes of a statement: its own, its expressions', its blocks'. -/
def Stmt.size : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Nat
  | _, _, .assign l r => 1 + l.size + r.size
  | _, _, .rebind _ r => 1 + r.size
  | _, _, .assignLocal _ r => 1 + r.size
  | _, _, .declLocal _ _ init => 1 + (match init with | some e => e.size | none => 0)
  | _, _, .declStorage _ _ init => 1 + (match init with | some r => r.size | none => 0)
  | _, _, .opAssign _ _ _ l r => 1 + l.size + r.size
  | _, _, .incDec _ _ l => 1 + l.size
  | _, _, .assignIncDec _ _ _ l _ => 1 + l.size
  | _, _, .assignLocalPush _ b => 1 + b.size
  | _, _, .push b v _ => 1 + b.size + (match v with | some e => e.size | none => 0)
  | _, _, .pop b => 1 + b.size
  | _, _, .transfer r a => 1 + r.size + a.size
  | _, _, .send _ r a _ => 1 + r.size + a.size
  | _, _, .declMem _ _ init _ _ => 1 + (match init with | some r => r.size | none => 0)
  | _, _, .rebindMem _ r => 1 + r.size
  | _, _, .assignFromMem l p => 1 + l.size + p.size
  | _, _, .assignMem l r => 1 + l.size + r.size
  | _, _, .delete l => 1 + l.size
  | _, _, .deleteMem p _ => 1 + p.size
  | _, _, .assignNew l n _ => 1 + l.size + n.size
  | _, _, .ite c thn els => 1 + c.size + thn.size + els.size
  | _, _, .require c => 1 + c.size
  | _, _, .assert c => 1 + c.size
  | _, _, .revert => 1
  | _, _, .assumeFalse => 1
  | _, _, .call _ args _ body => 1 + args.size + body.size
  | _, _, .tryCall call _ ok err _ pnc other =>
    1 + call.size + ok.size + err.size + pnc.size + other.size
  | _, _, .loop a c body => 1 + a.size + c.size + body.size
  | _, _, .block body => 1 + body.size
  | _, _, .pushOpAssign _ _ _ b r => 1 + b.size + r.size
  | _, _, .pushIncDec _ _ b => 1 + b.size
  | _, _, .callReceiver _ args _ body op => 1 + args.size + body.size + op.size
  | _, _, .callReceiverPush _ args _ body code value =>
    1 + args.size + body.size + code.size + value.size

def Prog.size : {Γ Γ' : Ctx} → Prog C Γ Γ' → Nat
  | _, _, .nil => 0
  | _, _, .cons s P => s.size + P.size

end

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
  | copyMem p => have := MPath.lower_size p; simp only [Src.lower, Tm.size, Src.size]; omega

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

/-- **A premise bounded by `n`**: at most two elements an update, and every
update's and formula's terms of at most `n` nodes. -/
structure Premise.Bounded {Γ' : Ctx} (n : Nat) (P : Premise C Γ Γ') : Prop where
  upds : ∀ U ∈ P.upds, U.2.2.length ≤ 2 ∧ U.2.2.tmSize ≤ n
  fmls : ∀ φ ∈ P.fmls, φ.2.tmSize ≤ n

namespace Premise.Bounded

variable {Γ' : Ctx}

theorem mono {n n' : Nat} {P : Premise C Γ Γ'} (h : P.Bounded n) (hn : n ≤ n') : P.Bounded n' :=
  ⟨fun U hU => ⟨(h.upds U hU).1, Nat.le_trans (h.upds U hU).2 hn⟩,
   fun φ hφ => Nat.le_trans (h.fmls φ hφ) hn⟩

/-- A premise that writes no update and no formula. -/
theorem of_nil {n : Nat} {P : Premise C Γ Γ'} (hu : P.upds = []) (hf : P.fmls = []) :
    P.Bounded n :=
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

theorem inv {n : Nat} {Δ₀ Δ Γ₁ : Ctx} {I : Fml C Γ} {B : Option (Fml C Γ)}
    {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool} {U : Upd C Γ Δ} {c c' : Fml C Δ}
    {hu : Ext Γ Δ₀} {hb : Ext Δ₀ Δ} {P : Prog C Δ₀ Γ₁} {post : Fml C Δ₀}
    (hI : I.tmSize ≤ n) (hB : ∀ b, B = some b → b.tmSize ≤ n) (hU : U.length ≤ 2)
    (hU' : U.tmSize ≤ n) (hc : c.tmSize ≤ n) (hc' : c'.tmSize ≤ n) (hp : post.tmSize ≤ n) :
    (Premise.inv I B xs hv U c c' hu hb P post).Bounded n :=
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
  | fixedCopy p shape hm => simp only [assignStep]; exact .upd1 (by omega)
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
    | fixedCopy p shape hm =>
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

theorem iteStep_bounded {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) : (iteStep k c thn els).Bounded 3 := by
  cases c with
  | simple s =>
    apply Premise.Bounded.split <;>
      simp only [Fml.tmSize, Tm.size, Simple.lower_size] <;> omega
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

theorem loopStep_bounded (m : Modality) {Γ₁ : Ctx} (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) : (loopStep k m a c body).Bounded (6 * (a.size + c.size) + 18) := by
  have hc := Val.lower_size c
  cases a with
  | unwind n =>
    cases n with
    | zero =>
      apply Premise.Bounded.check
      simp only [Fml.tmSize, Upd.tmSize, Rhs.size, Tm.size]; omega
    | succ n => bnil
  | auto => bnil
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
        have hIu := Val.lower_size (I.up (t := .val .uint))
        have hcu := Val.lower_size (c.up (t := .val .uint))
        have hdu := Val.lower_size ((d.up (t := .val .uint)).up (t := .val .bool))
        rw [Val.size_up] at hIu hcu
        rw [Val.size_up, Val.size_up] at hdu
        apply Premise.Bounded.inv
        · simp only [Fml.tmSize, Tm.size, LoopAnn.size]; omega
        · intro b hb; cases hb
        · simp only [Upd.length]; omega
        · simp only [Upd.tmSize, Rhs.size, LoopAnn.size]; omega
        · simp only [Fml.tmSize, Tm.size]; omega
        · simp only [Fml.tmSize, Tm.size]; omega
        · simp only [Fml.tmSize, Upd.tmSize, Rhs.size, Tm.size, LoopAnn.size]
          omega
      · bnil

/-! ### Calls, `try`, receivers -/

theorem callStep_bounded {Γ' ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) (n : Nat) :
    (callStep k f args ret body).Bounded n := by
  cases ret <;> (simp only [callStep]; split <;> bnil)

theorem tryStep_bounded (m : Modality) {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (rets : Binders ρ)
    (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂) (code : CodeBinder κ)
    (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (n : Nat) :
    (tryStep m rets ok err code pnc other).Bounded n := by
  cases m <;> bnil

theorem ReceiverValue.step_bounded {ps Γf : Ctx} {E : Ty} (f : Name) (args : Args C Γ ps)
    (r : Var) (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : ReceiverValue C Γ E)
    (n : Nat) : (ReceiverValue.step k f args r body e).Bounded n := by
  cases e <;> bnil

end Arms

/-! ## Every rule -/

section Step

variable (k : Nat) (m : Modality)

/-- **Every rule is bounded by its statement**: at most two elements an
update, and every emitted term of at most `16 * s.size + 16` nodes. -/
theorem Stmt.step_bounded {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :
    (s.step k m).Bounded (16 * s.size + 16) := by
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
  | push b v hd => exact (pushStep_bounded k b v hd).mono (by simp only [Stmt.size]; omega)
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
  | ite c thn els => exact (iteStep_bounded k c thn els).mono (by omega)
  | require c => exact (requireStep_bounded k c).mono (by omega)
  | assert c => exact (assertStep_bounded k c).mono (by omega)
  | revert => cases m <;> bnil
  | assumeFalse => bnil
  | call f args ret body => exact callStep_bounded k f args ret body _
  | tryCall call rets ok err code pnc other => exact tryStep_bounded m rets ok err code pnc other _
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

/-- **A rule writes at most two elements an update.** -/
theorem Stmt.step_upds_le {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :
    ∀ U ∈ (s.step k m).upds, U.2.2.length ≤ 2 :=
  fun U hU => ((Stmt.step_bounded k m s).upds U hU).1

/-- **Every term a rule emits is linear in its statement**, in an update or
in a formula, whatever the types. -/
theorem Stmt.step_tmSize_le {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :
    (∀ U ∈ (s.step k m).upds, U.2.2.tmSize ≤ 16 * s.size + 16) ∧
      (∀ φ ∈ (s.step k m).fmls, φ.2.tmSize ≤ 16 * s.size + 16) :=
  ⟨fun U hU => ((Stmt.step_bounded k m s).upds U hU).2,
   fun φ hφ => (Stmt.step_bounded k m s).fmls φ hφ⟩

end Step


end Solidity
