import Solidity.Calculus.AutoComplete

/-!
# The closer's decision, stated (M7)

The theorem the closer is held to (`docs/automation.md`, M7): on a scoped
leaf `Fml C []` it terminates with a proof (`LeafVerdict.proved`) or a
certified counterexample (`LeafVerdict.refuted σ`, a typed state that
refutes the leaf), and it may answer `unknown` only where the user allowed
it (`docs/automation.md`, M6, decisions c, c′, d and their extensions):

* a product of two non-literal terms (KeY `int` or a 256-bit type), `x ** e`
  at a literal `e ≥ 2` and `mulmod` of two symbolic factors among them;
* `/`, `%`, `**`, `<<`, `>>`, `&`, `|`, `^` with two symbolic operands, a
  symbolic divisor (`c / x`), exponent or shift amount counted as such
  (`Waivers`: each class a field, all waived by the user's answer);
* a quantified formula over array or mapping contents outside the array
  property fragment (Bradley, Manna and Sipma), negative-position
  `havoc`/`anon`/`allocAll`/`grow` and storage binders among them;
* hashes: not settled (`HashReading`, a parameter: `excluded` puts every
  hash term outside the fragment; `perGoal` reads the goal under a premise
  of its own, which the user has yet to fix).

The fragment is `Fml.inTarget`, the open statement `DecisionTheorem`, both
about the one decision function `decideLeaf`.  A statement of the form "some
decider is complete" would be vacuous: a classical function deciding
validity by `Classical.choice` exists, so the statement is about this
computable function, which later rounds extend.

What is proved: `decideLeaf` is sound (`decideLeaf_sound`), its refutations
are refutations (`decideLeaf_refutes`), and it answers on `Fml.Covered`
(`decideLeaf_complete`), the fragment M4 proves total
(`dependentReduction?_isSome`) as extended since.  `Fml.Covered ⊆
Fml.inTarget` is not proved: `Fml.Covered` is read on the eliminated leaf,
`Fml.inTarget` on the source.

The array-property check is syntactic and conservative: an update or a
program under a quantifier counts as reading at its variable, the body of a
negative-position block must be quantifier-free, and an index guard may not
negate a comparison of bound variables.  So `Fml.inTarget` is a subset of
the fragment the user named, never a superset.
-/

namespace Solidity.Decide

open Linear

variable {C : Contract}

/-! ## Verdicts and the decision -/

/-- What the closer answers on a leaf. -/
inductive LeafVerdict (C : Contract) where
  /-- The leaf is valid. -/
  | proved
  /-- The typed state refutes the leaf. -/
  | refuted (σ : State C [])
  /-- Neither: allowed only outside the fragment. -/
  | unknown

/-- **The decision**: the automatic pipeline (`dependentReduction?`), its
arithmetic decided by the verified procedure (`AFml.decide_iff`), a `false`
answer turned into a typed countermodel (`DependentReduction.verify`). -/
def decideLeaf (φ : Fml C []) : LeafVerdict C :=
  match dependentReduction? φ with
  | none => .unknown
  | some r =>
    match r.verify with
    | .inl _ => .proved
    | .inr cm => .refuted cm.state

/-- **Soundness.** -/
theorem decideLeaf_sound {φ : Fml C []} (h : decideLeaf φ = .proved) : Fml.Valid φ := by
  unfold decideLeaf at h
  split at h
  · cases h
  · split at h
    · rename_i hv _
      exact hv.down
    · cases h

/-- **Refutations are certified**: the state returned refutes the leaf. -/
theorem decideLeaf_refutes {φ : Fml C []} {σ : State C []} (h : decideLeaf φ = .refuted σ) :
    ¬ holds σ φ := by
  unfold decideLeaf at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i cm _
      cases h
      exact cm.refutes

theorem decideLeaf_not_valid {φ : Fml C []} {σ : State C []} (h : decideLeaf φ = .refuted σ) :
    ¬ Fml.Valid φ :=
  fun hv => decideLeaf_refutes h (hv σ)

/-- **The fragment proved complete**: M4's, on the eliminated leaf. -/
def _root_.Solidity.Fml.Covered (φ : Fml C []) : Bool := φ.inExact && φ.exactBounded

/-- **Completeness on `Fml.Covered`.** -/
theorem decideLeaf_complete {φ : Fml C []} (h : φ.Covered = true) : decideLeaf φ ≠ .unknown := by
  simp only [Fml.Covered, Bool.and_eq_true] at h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (dependentReduction?_isSome φ h.1 h.2)
  unfold decideLeaf
  rw [hr]
  dsimp only
  split <;> exact fun h => nomatch h

/-- On the fragment the verdict is exact. -/
theorem decideLeaf_proved_iff {φ : Fml C []} (h : φ.Covered = true) :
    decideLeaf φ = .proved ↔ Fml.Valid φ := by
  refine ⟨decideLeaf_sound, fun hv => ?_⟩
  cases hd : decideLeaf φ with
  | proved => rfl
  | refuted σ => exact absurd hv (decideLeaf_not_valid hd)
  | unknown => exact absurd hd (decideLeaf_complete h)

/-! ## The fragment the user named -/

/-- How a hash is read: unsettled (`docs/automation.md`, M7).  `admits k`:
a hash term of kind `k` is in the fragment; `goal φ`: the formula the
decision is asked for `φ`. -/
structure HashReading where
  admits : HashKind → Bool
  goal : {C : Contract} → Fml C [] → Fml C []

/-- Every hash term outside the fragment, the goal itself. -/
def HashReading.excluded : HashReading := ⟨fun _ => false, fun φ => φ⟩

/-- The per-goal reading (e3′, proposed, not decided): the goal under a
premise that its own distinct hash inputs hash apart, `premise φ` (to be
fixed with the user); `ecrecover` stays outside. -/
def HashReading.perGoal (premise : {C : Contract} → Fml C [] → Fml C []) : HashReading :=
  ⟨fun k => k != .ecrecover, fun φ => .imp (premise φ) φ⟩

/-- **The classes the closer may leave `unknown` with two symbolic
operands** (`true`: waived; the user's answer of 2026-10-25 waives all
four), and the hash reading. -/
structure Waivers where
  /-- `/`, `%`, a modulus of `addmod`/`mulmod`: a symbolic divisor. -/
  division : Bool := true
  /-- `**`: a symbolic exponent. -/
  power : Bool := true
  /-- `<<`, `>>`: a symbolic shift amount. -/
  shift : Bool := true
  /-- `&`, `|`, `^`: two symbolic operands. -/
  bitwise : Bool := true
  hashes : HashReading := .excluded

/-- The level of a position: `0` for the outermost local, stable under
binders further in. -/
def _root_.Solidity.Idx.level {Γ : Ctx} {t : LTy} (i : Idx Γ t) : Nat := Γ.length - 1 - i.toNat

/-- A literal's integer. -/
def _root_.Solidity.Op0.litValue? {s : Srt} : Op0 C s → Option Int
  | .lit (p := .bool) v => some (cond (show Bool from v) 1 0)
  | .lit (p := .uint) v => some v.val
  | .lit (p := .int) v => some v.val
  | .zlit n => some n
  | _ => none

def _root_.Solidity.Tm.litValue? {Γ : Ctx} {s : Srt} : Tm C Γ s → Option Int
  | .app0 o => o.litValue?
  | _ => none

def _root_.Solidity.Tm.isLitV {Γ : Ctx} {s : Srt} (t : Tm C Γ s) : Bool := t.litValue?.isSome

/-- Whether an operator applied to operands (literal or not, the second's
literal value) is in the fragment. -/
def _root_.Solidity.BinOp.admits (w : Waivers) (op : BinOp) (xl yl : Bool) (y? : Option Int) : Bool :=
  match op with
  | .mul | .mulW => xl || yl
  | .div | .mod => yl || !w.division
  | .pow | .powW =>
    match y? with
    | some n => decide (n ≤ 1)
    | none => !w.power
  | .shl | .shr => yl || !w.shift
  | .band | .bor | .bxor => xl || yl || !w.bitwise
  | _ => true

def _root_.Solidity.Op2.admits (w : Waivers) {a b s : Srt} (o : Op2 C a b s) (xl yl : Bool)
    (y? : Option Int) : Bool :=
  match o with
  | .binop op _ => op.admits w xl yl y?
  | .zbin op _ => op != .mul || xl || yl
  | .hash k => w.hashes.admits k
  | _ => true

def _root_.Solidity.Op3.admits (w : Waivers) {a b c s : Srt} (o : Op3 C a b c s) (xl yl zl : Bool) :
    Bool :=
  match o with
  | .modular .mulmod => (xl || yl) && (zl || !w.division)
  | .modular .addmod => zl || !w.division
  | _ => true

/-- **A term of the fragment**: every operator admitted. -/
def _root_.Solidity.Tm.inTarget {Γ : Ctx} (w : Waivers) : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf _ a => a.inTarget w
  | _, .app1 _ x => x.inTarget w
  | _, .app2 o x y => x.inTarget w && y.inTarget w && o.admits w x.isLitV y.isLitV y.litValue?
  | _, .app3 o x y z => x.inTarget w && y.inTarget w && z.inTarget w &&
      o.admits w x.isLitV y.isLitV z.isLitV
  | _, _ => true

def _root_.Solidity.Rhs.inTarget {Γ : Ctx} (w : Waivers) {t : LTy} : Rhs C Γ t → Bool
  | .val a | .zint a => a.inTarget w
  | .path q => q.inTarget w
  | .mref i => i.inTarget w
  | .store s => s.inTarget w
  | .unset | .saveNet | .saveNetMt => true

def _root_.Solidity.UpdElem.inTarget {Γ Δ : Ctx} (w : Waivers) : UpdElem C Γ Δ → Bool
  | .local _ r => r.inTarget w
  | .storage s => s.inTarget w
  | .memory m => m.inTarget w
  | .selfBalance _ a | .setBalance a => a.inTarget w
  | .net r _ a | .pay r a | .netMt r a => r.inTarget w && a.inTarget w

def _root_.Solidity.Upd.inTarget {Γ : Ctx} (w : Waivers) : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U e => U.inTarget w && e.inTarget w
  | _, .decl U _ r => U.inTarget w && r.inTarget w
  | _, .pop U _ | _, .drop U _ => U.inTarget w

/-! ### Reads and the array property fragment -/

/-- The symbols that read contents: storage, memory, a hash, the ledger. -/
def _root_.Solidity.Op2.isRead {a b s : Srt} : Op2 C a b s → Bool
  | .find | .len | .read | .mlen | .sfind | .copyMem | .iread | .findIn | .sfindIn | .hash _ => true
  | _ => false

/-- The symbols that write. -/
def _root_.Solidity.Op2.isWrite {a b s : Srt} : Op2 C a b s → Bool
  | .delAt | .pushSlot | .pop | .shrink | .extend | .copySt _ | .delAtIn | .copy _ => true
  | _ => false

def _root_.Solidity.Op1.isWrite {a s : Srt} : Op1 C a s → Bool
  | .alloc .. | .addM .. => true
  | _ => false

/-- The symbols that index: the second operand is the index. -/
def _root_.Solidity.Op2.isIndex {a b s : Srt} : Op2 C a b s → Bool
  | .at _ | .mat _ => true
  | _ => false

/-- A bound variable, by its level. -/
def _root_.Solidity.Tm.isBound {Γ : Ctx} (qs : List Nat) {s : Srt} : Tm C Γ s → Bool
  | .pvV i | .pvZ i => qs.contains i.level
  | _ => false

/-- The term mentions a bound variable. -/
def _root_.Solidity.Tm.mentions {Γ : Ctx} (qs : List Nat) : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV i | _, .pvZ i => qs.contains i.level
  | _, .netOf _ a | _, .app1 _ a => a.mentions qs
  | _, .app2 _ x y => x.mentions qs || y.mentions qs
  | _, .app3 _ x y z => x.mentions qs || y.mentions qs || z.mentions qs
  | _, _ => false

/-- The term reads contents at a bound variable. -/
def _root_.Solidity.Tm.readsAt {Γ : Ctx} (qs : List Nat) : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf _ a => a.mentions qs || a.readsAt qs
  | _, .app1 o x => (match o with | .net => x.mentions qs | _ => false) || x.readsAt qs
  | _, .app2 o x y => (o.isRead && (x.mentions qs || y.mentions qs)) || x.readsAt qs || y.readsAt qs
  | _, .app3 _ x y z => x.readsAt qs || y.readsAt qs || z.readsAt qs
  | _, _ => false

/-- The term reads contents at all. -/
def _root_.Solidity.Tm.readsAny {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .netOf _ _ => true
  | _, .app1 o x => (match o with | .net => true | _ => false) || x.readsAny
  | _, .app2 o x y => o.isRead || x.readsAny || y.readsAny
  | _, .app3 _ x y z => x.readsAny || y.readsAny || z.readsAny
  | _, _ => false

/-- **A value term of the array property fragment**: a bound variable
occurs only as an index (`a[i]`, `m[k]`, a memory element, a ledger
entry), never under arithmetic, never in a nested index (`a[a[i]]`), and
nothing is written at a path that mentions it. -/
def _root_.Solidity.Tm.apfV {Γ : Ctx} (qs : List Nat) : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV i | _, .pvZ i => !qs.contains i.level
  | _, .netOf _ a => a.isBound qs || !a.mentions qs
  | _, .app1 o x =>
    match o with
    | .net => x.isBound qs || !x.mentions qs
    | o => if o.isWrite then !x.mentions qs else x.apfV qs
  | _, .app2 o x y =>
    if o.isIndex then x.apfV qs && (y.isBound qs || !y.mentions qs)
    else if o.isWrite then !(x.mentions qs || y.mentions qs)
    else x.apfV qs && y.apfV qs
  | _, .app3 o x y z =>
    match o with
    | .atIn _ => !x.mentions qs && y.apfV qs && (z.isBound qs || !z.mentions qs)
    | .ite => x.apfV qs && y.apfV qs && z.apfV qs
    | .modular _ => x.apfV qs && y.apfV qs && z.apfV qs
    | _ => !(x.mentions qs || y.mentions qs || z.mentions qs)
  | _, _ => true

def _root_.Solidity.Op1.isNot {a s : Srt} : Op1 C a s → Bool
  | .unop .not _ => true
  | _ => false

def _root_.Solidity.Op2.isNeB {a b s : Srt} : Op2 C a b s → Bool
  | .binop .neB _ => true
  | _ => false

/-- No `!=`, `!` over a bound variable: a guard is positive in them. -/
def _root_.Solidity.Tm.positiveIn {Γ : Ctx} (qs : List Nat) : {s : Srt} → Tm C Γ s → Bool
  | _, .app1 o x => if o.isNot then !x.mentions qs else x.positiveIn qs
  | _, .netOf _ x => x.positiveIn qs
  | _, .app2 o x y => if o.isNeB then !(x.mentions qs || y.mentions qs)
      else x.positiveIn qs && y.positiveIn qs
  | _, .app3 _ x y z => x.positiveIn qs && y.positiveIn qs && z.positiveIn qs
  | _, _ => true

/-- An index-guard term: linear in the bound variables (`Tm.inTarget`),
positive in them, reading nothing at them. -/
def _root_.Solidity.Tm.apfG {Γ : Ctx} (qs : List Nat) {s : Srt} (t : Tm C Γ s) : Bool :=
  !t.readsAt qs && t.positiveIn qs

/-- The literal `true`. -/
def _root_.Solidity.Tm.isTrueLit {Γ : Ctx} {p : PrimTy} : Tm C Γ (.val p) → Bool
  | .app0 o => match o with | .lit (p := .bool) v => v | _ => false
  | _ => false

/-- A quantifier-free formula not mentioning a bound variable. -/
def _root_.Solidity.Fml.groundQF {Γ : Ctx} (qs : List Nat) : Fml C Γ → Bool
  | .tt => true
  | .eq a b => !(a.mentions qs || b.mentions qs)
  | .wellFormed s => !s.mentions qs
  | .not φ => φ.groundQF qs
  | .and φ ψ | .imp φ ψ => φ.groundQF qs && ψ.groundQF qs
  | _ => false

/-- **An index guard**: conjunctions of guard atoms, an atom an equation of
guard terms (a Boolean one against `true`), or ground. -/
def _root_.Solidity.Fml.apfGuard {Γ : Ctx} (qs : List Nat) : Fml C Γ → Bool
  | .tt => true
  | .and φ ψ => φ.apfGuard qs && ψ.apfGuard qs
  | φ@(@Fml.eq _ _ p a b) =>
    φ.groundQF qs ||
      (a.apfG qs && b.apfG qs && (match p with | .bool => a.isTrueLit || b.isTrueLit | _ => true))
  | φ => φ.groundQF qs

/-- A quantifier-free value formula over `Tm.apfV` terms. -/
def _root_.Solidity.Fml.apfValue {Γ : Ctx} (qs : List Nat) : Fml C Γ → Bool
  | .tt => true
  | .eq a b => a.apfV qs && b.apfV qs
  | .wellFormed s => s.apfV qs
  | .not φ => φ.apfValue qs
  | .and φ ψ | .imp φ ψ => φ.apfValue qs && ψ.apfValue qs
  | _ => false

/-- **The body of a universal block**: `guard → value`, conjunctions of
them. -/
def _root_.Solidity.Fml.apfBody {Γ : Ctx} (qs : List Nat) : Fml C Γ → Bool
  | .imp G V => (G.apfGuard qs && V.apfBody qs) || (Fml.imp G V).apfValue qs
  | .and φ ψ => φ.apfBody qs && ψ.apfBody qs
  | φ => φ.apfValue qs

/-- The formula reads contents at a bound variable; an update or a program
counts as one (conservative). -/
def _root_.Solidity.Fml.readsAt (qs : List Nat) : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt => false
  | _, .eq a b => a.readsAt qs || b.readsAt qs
  | _, .wellFormed s => s.mentions qs || s.readsAt qs
  | _, .not φ | _, .havoc φ | _, .anon _ φ | _, .grow φ | _, .all _ _ φ | _, .bind _ _ _ φ
  | _, .allocAll _ _ φ => φ.readsAt qs
  | _, .and φ ψ | _, .imp φ ψ => φ.readsAt qs || ψ.readsAt qs
  | _, .upd .. | _, .modal .. => true

/-- The formula reads contents at all. -/
def _root_.Solidity.Fml.readsAny : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt => false
  | _, .eq a b => a.readsAny || b.readsAny
  | _, .wellFormed _ => true
  | _, .not φ | _, .havoc φ | _, .anon _ φ | _, .grow φ | _, .all _ _ φ | _, .bind _ _ _ φ
  | _, .allocAll _ _ φ => φ.readsAny
  | _, .and φ ψ | _, .imp φ ψ => φ.readsAny || ψ.readsAny
  | _, .upd .. | _, .modal .. => true

/-- The quantifier-free formulas whose terms are in the fragment. -/
def _root_.Solidity.Fml.qfTarget {Γ : Ctx} (w : Waivers) : Fml C Γ → Bool
  | .tt => true
  | .eq a b => a.inTarget w && b.inTarget w
  | .wellFormed s => s.inTarget w
  | .not φ => φ.qfTarget w
  | .and φ ψ | .imp φ ψ => φ.qfTarget w && ψ.qfTarget w
  | _ => false

/-- **A universal block of the array property fragment**, the levels of its
variables collected. -/
def _root_.Solidity.Fml.apfBlock (w : Waivers) : {Γ : Ctx} → List Nat → Fml C Γ → Bool
  | Γ, qs, .all _ _ φ => φ.apfBlock w (Γ.length :: qs)
  | _, qs, φ => φ.apfBody qs && φ.qfTarget w

/-- **The fragment, at a polarity** (`pol`: positive, the formula's own
`∀` a `∃` of its negation; `pres`: under a negative-position quantifier,
past which only Presburger quantifiers, reading nothing at their variable,
keep the negation in `∃*∀*`). -/
def _root_.Solidity.Fml.target (w : Waivers) : {Γ : Ctx} → Bool → Bool → Fml C Γ → Bool
  | _, _, _, .tt => true
  | _, _, _, .eq a b => a.inTarget w && b.inTarget w
  | _, _, _, .wellFormed s => s.inTarget w
  | _, pol, n, .not φ => φ.target w (!pol) n
  | _, pol, n, .and φ ψ => φ.target w pol n && ψ.target w pol n
  | _, pol, n, .imp φ ψ => φ.target w (!pol) n && ψ.target w pol n
  | _, pol, n, .upd _ U φ => U.inTarget w && φ.target w pol n
  | _, _, _, .modal .. => false
  | Γ, pol, n, .all _ _ φ =>
    if !φ.readsAt [Γ.length] then φ.target w pol (n || !pol)
    else if n then false
    else if pol then φ.target w pol n
    else φ.apfBlock w [Γ.length]
  | Γ, pol, n, .bind _ _ t φ =>
    match t with
    | .val _ | .kint =>
      if !φ.readsAt [Γ.length] then φ.target w pol (n || !pol)
      else if n then false
      else if pol then φ.target w pol n
      else φ.apfBlock w [Γ.length]
    | _ => if pol && !n then φ.target w pol n else !φ.readsAny && φ.target w pol true
  | _, pol, n, .havoc φ | _, pol, n, .anon _ φ | _, pol, n, .grow φ | _, pol, n, .allocAll _ _ φ =>
    if pol && !n then φ.target w pol n else !φ.readsAny && φ.target w pol true

/-- **The fragment the user named**, on a scoped leaf: no program, every
operator admitted (`Waivers`), every quantifier over contents in the array
property fragment. -/
def _root_.Solidity.Fml.inTarget (w : Waivers) (φ : Fml C []) : Bool := φ.target w true false

/-- **The open theorem**: on the fragment, `decideLeaf` answers. -/
def DecisionTheorem (w : Waivers := {}) : Prop :=
  ∀ (C : Contract) (φ : Fml C []), φ.inTarget w = true → decideLeaf (w.hashes.goal φ) ≠ .unknown

/-- info: 'Solidity.Decide.decideLeaf_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideLeaf_sound

/-- info: 'Solidity.Decide.decideLeaf_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideLeaf_refutes

/-- info: 'Solidity.Decide.decideLeaf_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideLeaf_complete

end Solidity.Decide
