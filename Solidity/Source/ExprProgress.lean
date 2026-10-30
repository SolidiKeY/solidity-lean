import Solidity.Source.Eval
import Solidity.Source.ValueProgress
import Solidity.Source.Hoare

/-!
# Progress of the interpreter on value expressions (lane V04b)

`NS m`: the computation `m` never halts `stuck`, from any state. For the
**value fragment** of resolved expressions (`RExpr.ValFrag`: constants,
locals of value type, `this`, unary and binary operators, comparisons,
shifts and powers, conditionals, and implicit conversions between value
types or from constants) evaluation is never `stuck` at any horizon,
provided the expression is in the operations' domains (`RExpr.OpsOK`),
which every elaborated expression is (`Typed.toR_opsOK`):
`evalE_valFrag_ns`.

This is the expression core of gap-relative progress: the value-layer
lemmas of `Solidity/Source/ValueProgress.lean` lifted through the
interpreter's binds, pipelines (`evalPair`) and conversions (`convRV`).
-/

namespace Solidity.Source

open EM

variable {E : Env}

/-- **Never `stuck`**: from every state, `m` succeeds or halts otherwise. -/
def NS {Γ : RCtx} {α : Type} (m : EM E Γ α) : Prop := ∀ x w, (m.run x).1 ≠ .error (.stuck w)

namespace NS

variable {Γ : RCtx} {α β : Type}

theorem pure' (a : α) : NS (pure a : EM E Γ α) := fun _ _ h => by cases h

theorem halt' {h : Halt} (hh : ∀ w, h ≠ .stuck w) : NS (halt h : EM E Γ α) := fun _ w e => by
  cases e; exact hh w rfl

theorem bind {m : EM E Γ α} {k : α → EM E Γ β} (hm : NS m) (hk : ∀ a, NS (k a)) : NS (m >>= k) := by
  intro x w h
  rw [Hoare.run_bind] at h
  rcases hr : m.run x with ⟨r, y⟩
  rw [hr] at h
  cases r with
  | ok a => exact hk a y w h
  | error e =>
    have he : e = .stuck w := by cases h; rfl
    have := hm x w
    rw [hr, he] at this
    exact this rfl

theorem lift' {r : R α} (h : NotStuckR r) : NS (lift r : EM E Γ α) := by
  intro x w e
  cases r with
  | ok a => cases e
  | error e' => exact h w (by cases e; rfl)

theorem locals' : NS (locals : EM E Γ (Locals E.layout Γ)) := fun _ _ h => by cases h

theorem modSt' (f : St E → St E) : NS (modSt f : EM E Γ Unit) := fun _ _ h => by cases h

end NS

/-- A run-time value of a value type is plain: `getV` is never `stuck`. -/
theorem getV_ns {Γ : RCtx} {τ : STy} (hτ : τ.isValue = true) (v : RVal E.layout τ) :
    NS (getV (Γ := Γ) v) := by
  refine NS.lift' ?_
  cases v with
  | val x => exact NotStuckR.pure _
  | const _ => cases hτ
  | strLit _ => cases hτ
  | hex _ _ => cases hτ
  | tuple _ => cases hτ

/-! ## Never `stuck`, with a postcondition -/

/-- From every state, `m` returns a result satisfying `Q` or halts other
than `stuck`. -/
def NSP {Γ : RCtx} {α : Type} (m : EM E Γ α) (Q : α → Prop) : Prop :=
  ∀ x, match (m.run x).1 with
    | .ok a => Q a
    | .error h => NotStuck h

namespace NSP

variable {Γ : RCtx} {α β : Type}

theorem pure' {a : α} {Q : α → Prop} (h : Q a) : NSP (pure a : EM E Γ α) Q := fun _ => h

theorem halt' {h : Halt} {Q : α → Prop} (hh : NotStuck h) : NSP (halt h : EM E Γ α) Q := fun _ => hh

theorem bind {m : EM E Γ α} {k : α → EM E Γ β} {Q : α → Prop} {R : β → Prop} (hm : NSP m Q)
    (hk : ∀ a, Q a → NSP (k a) R) : NSP (m >>= k) R := by
  intro x
  rw [Hoare.run_bind]
  have h1 := hm x
  rcases hr : m.run x with ⟨r, y⟩
  rw [hr] at h1
  cases r with
  | ok a => exact hk a h1 y
  | error e => exact h1

theorem lift' {r : R α} {Q : α → Prop}
    (h : match r with | .ok a => Q a | .error e => NotStuck e) : NSP (lift r : EM E Γ α) Q := by
  intro x
  cases r with
  | ok a => exact h
  | error e => exact h

theorem of_ns {m : EM E Γ α} (h : NS m) : NSP m (fun _ => True) := by
  intro x
  rcases hr : (m.run x).1 with e | a
  · cases e with
    | stuck w => exact (h x w hr).elim
    | _ => trivial
  · trivial

theorem ns {m : EM E Γ α} {Q : α → Prop} (h : NSP m Q) : NS m := by
  intro x w e
  have := h x
  rw [e] at this
  exact this

theorem weaken {m : EM E Γ α} {Q Q' : α → Prop} (h : NSP m Q) (hq : ∀ a, Q a → Q' a) : NSP m Q' := by
  intro x
  have := h x
  rcases hr : (m.run x).1 with e | a
  · rw [hr] at this; exact this
  · rw [hr] at this; exact hq a this

/-- A computation over other locals. -/
theorem sub' {Γ' : RCtx} {l' : Locals E.layout Γ'} {m : EM E Γ' α} {Q : α × Locals E.layout Γ' → Prop}
    (h : NSP m fun a => ∀ l'', Q (a, l'')) : NSP (sub (Γ := Γ) l' m) Q := by
  intro ⟨l, s⟩
  have h1 := h (l', s)
  unfold EM.sub
  rcases hr : m.run (l', s) with ⟨r, ⟨l'', s'⟩⟩
  have hr' : m (l', s) = (r, (l'', s')) := hr
  rw [hr] at h1
  cases r with
  | ok a => simp only [ExceptT.run, ExceptT.mk, hr']; exact h1 l''
  | error e => simp only [ExceptT.run, ExceptT.mk, hr']; exact h1

end NSP

/-! ## Conversions -/

/-- An implicit conversion of a hexadecimal constant to anything but
`bytesN` is never `stuck` (as a rational constant's). -/
theorem constVal_hex_ok (B : DeclName → DeclName → Bool) {q : Q} {k : Nat} {τ : STy}
    (h : (STy.hexConst q k).implicit B τ = true) (hτ : ∀ m hm, τ ≠ .fixedBytes m hm) :
    NotStuckR (constVal (D := E.layout) q τ) := by
  cases τ <;> (try (cases h <;> done))
  · rename_i t
    exact constVal_ok B (τ := .int t) (by
      rw [show STy.implicit B (.hexConst q k) (.int t) = decide (q.FitsInt t) from rfl] at h
      exact h)
  · rename_i m hm
    exact absurd rfl (hτ m hm)
  · rename_i f
    exact constVal_ok B (τ := .fixed f) (by
      rw [show STy.implicit B (.hexConst q k) (.fixed f) = (q.toFixed? f).isSome from rfl] at h
      exact h)

/-- A type of the fragment's conversions has no location. -/
theorem loc_of_frag {σ : STy} (hσ : σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k)) :
    σ.loc? = none := by
  rcases hσ with hσ | ⟨q, rfl⟩ | ⟨q, k, rfl⟩
  · cases σ <;> first | rfl | cases hσ
  · rfl
  · rfl

/-- **`convRV` is never `stuck` on the conversions of the value fragment**:
an implicit conversion (or the identity) from a value type or a constant
to a value type. -/
theorem convRV_ns {Γ : RCtx} (F : Fr) (n : Nat) {σ τ : STy} (hc : Conv E.isBase σ τ)
    (hσ : σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k)) (v : RVal E.layout σ) :
    NS (convRV (Γ := Γ) F n τ v) := by
  have hl := loc_of_frag hσ
  unfold convRV
  split
  · -- a constant
    dsimp only
    split
    · exact NS.pure' _
    · rename_i he
      exact NS.bind (NS.pure' _) fun _ => NS.bind (NS.lift' (constVal_ok E.isBase (hc.resolve_right he)))
        fun _ => NS.pure' _
  · -- a hexadecimal constant to `bytesN`
    dsimp only
    split
    · exact NS.pure' _
    · exact NS.bind (NS.pure' _) fun _ => NS.pure' _
  · -- a hexadecimal constant to another type
    rename_i hτ
    dsimp only
    split
    · exact NS.pure' _
    · rename_i he
      exact NS.bind (NS.pure' _) fun _ => NS.bind (NS.lift' (constVal_hex_ok E.isBase (hc.resolve_right he)
        (fun m hm e => hτ m hm e))) fun _ => NS.pure' _
  all_goals first
    | (exfalso; rcases hσ with h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h)
    | (rename_i h; rw [hl] at h; cases h)
    | skip
  · -- a plain value
    rename_i x hr hh _ _ _ _ _ _
    dsimp only
    split
    · exact NS.pure' _
    · rename_i he
      have hv : σ.isValue = true := by
        rcases hσ with hσ | ⟨q, rfl⟩ | ⟨q, k, rfl⟩
        · exact hσ
        · exact (hr q _ rfl HEq.rfl).elim
        · exact (hh q k _ rfl HEq.rfl).elim
      exact NS.bind (NS.pure' _) fun _ =>
        NS.bind (NS.lift' (convVal_ok E.isBase hv (.inl (hc.resolve_right he)) x)) fun _ => NS.pure' _
  · -- not a plain value: impossible for the fragment's types
    rename_i hr hh _ _ hval _ _ _ _
    exfalso
    rcases hσ with hσ | ⟨q, rfl⟩ | ⟨q, k, rfl⟩
    · cases v with
      | val x => exact hval x rfl
      | const _ => cases hσ
      | strLit _ => cases hσ
      | hex _ _ => cases hσ
      | tuple _ => cases hσ
    · exact hr q v rfl HEq.rfl
    · exact hh q k v rfl HEq.rfl

/-! ## Storage of value types -/

/-- A cell whose type has a default always reads a value. -/
theorem Storage.read_isSome {D : Layout} {L : SPath → STy} (st : Storage D L) (p : SPath)
    (h : (Val.default D (L p)).isSome = true) : (st.read p).isSome = true := by
  unfold Storage.read
  cases st.cell p with
  | some _ => rfl
  | none => exact h

/-- **Reading a storage cell of value type is never `stuck`** when the
path's layout type is the read type and has a default. -/
theorem readAt_ns {Γ : RCtx} (F : Fr) (p : SPath) {τ : STy} (hc : E.cellTy p = τ)
    (hd : (Val.default E.layout τ).isSome = true) : NS (readAt (E := E) (Γ := Γ) F p τ) := by
  subst hc
  unfold readAt readCell
  refine NS.bind (NS.bind (fun _ _ h => by cases h) fun s => ?_) fun v => ?_
  · dsimp only
    split
    · exact NS.pure' _
    · rename_i hn
      exfalso
      split at hn
      · have := Storage.read_isSome (s.ex.transient.cells F.this) p hd
        rw [hn] at this; cases this
      · have := Storage.read_isSome (s.ex.world.accounts F.this).storage p hd
        rw [hn] at this; cases this
  · rw [dif_pos rfl]
    exact NS.pure' _

/-- **Writing a storage cell of value type is never `stuck`** (in a static
frame it reverts). -/
theorem writeAt_ns {Γ : RCtx} (F : Fr) (p : SPath) {τ : STy} (hc : τ = E.cellTy p) (v : Val E.layout τ) :
    NS (writeAt (E := E) (Γ := Γ) F p v) := by
  unfold writeAt
  rw [dif_pos hc]
  unfold setCell
  split <;>
  · unfold applyOp
    split
    · exact NS.bind (NS.halt' fun _ h => by cases h) fun _ => NS.modSt' _
    · exact NS.bind (NS.pure' _) fun _ => NS.modSt' _

/-! ## The value fragment -/

/-- A local, or a state variable of a value type stored at its own cell
type, with a default. -/
def RLVal.IsSimple {Γ : RCtx} : {τ : STy} → RLVal E Γ τ → Prop
  | _, .local _ => True
  | τ, .state d _ _ => τ.byRef = false ∧ E.cellTy d.path = τ ∧ (Val.default E.layout τ).isSome = true
  | _, _ => False

/-- Mapping key types whose values have a word (`Val.word`). -/
def STy.keyable : STy → Bool
  | .int _ | .bool | .address _ | .fixedBytes _ _ | .fixed _ | .enum _ | .contract _ => true
  | _ => false

mutual

/-- **The value fragment** of resolved expressions: no memory, calls or
references; state variables and mapping values only of value types at
their cell types; every intermediate value of a value type, every
conversion from a value type or a constant. -/
def RExpr.ValFrag {Γ : RCtx} : {τ : STy} → RExpr E Γ τ → Prop
  | _, .const _ | _, .bytesLit _ _ | _, .addressLit _ | _, .bool _ | _, .this _ | _, .compareConst _ _ _ => True
  | τ, .local _ => τ.isValue = true
  | τ, .state d _ => d.isConst = false ∧ τ.byRef = false ∧ E.cellTy d.path = τ ∧
      (Val.default E.layout τ).isSome = true ∧ τ.isValue = true
  | τ, .unary _ a => RExpr.ValFrag a ∧ τ.isValue = true
  | τ, .binary _ a b => RExpr.ValFrag a ∧ RExpr.ValFrag b ∧ τ.isValue = true
  | _, .compare (τ := τ) _ a b => RExpr.ValFrag a ∧ RExpr.ValFrag b ∧ τ.isValue = true
  | τ, .shiftLike _ a b _ => RExpr.ValFrag a ∧ RExpr.ValFrag b ∧ τ.isValue = true
  | τ, .cond c a b => RExpr.ValFrag c ∧ RExpr.ValFrag a ∧ RExpr.ValFrag b ∧ τ.isValue = true
  | τ, .conv (σ := σ) a _ => RExpr.ValFrag a ∧ τ.isValue = true ∧
      (σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k))
  | τ, .assign l e => l.IsSimple ∧ RExpr.ValFrag e ∧ τ.isValue = true
  | τ, .compound (σ := σ) _ l e _ => l.IsSimple ∧ RExpr.ValFrag e ∧ τ.isValue = true ∧
      (σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k))
  | _, .incDec _ _ l => l.IsSimple
  | τv, .indexMapping (τk := τk) a k => RExpr.MapRef a ∧ RExpr.ValFrag k ∧ τk.keyable = true ∧
      τv.isValue = true ∧ (Val.default E.layout τv).isSome = true
  | _, _ => False

/-- **Mapping references of the fragment**: a mapping state variable, or a
mapping value of a mapping, with keys of the fragment. -/
def RExpr.MapRef {Γ : RCtx} : {τ : STy} → RExpr E Γ τ → Prop
  | τ, .state d _ => d.isConst = false ∧ E.pathTy d.path = some τ ∧ (∃ k v, τ = .mapping k v)
  | τv, .indexMapping (τk := τk) a k => RExpr.MapRef a ∧ RExpr.ValFrag k ∧ τk.keyable = true ∧
      (∃ k' v', τv = .mapping k' v')
  | _, _ => False

end

theorem cmpConst_ok {op : BinOp} (hop : (BinKind.order.admits op || BinKind.eq.admits op) = true) (a b : Q) :
    NotStuckR (cmpConst op a b) := by
  intro w h
  cases op <;> (try exact absurd hop (by decide)) <;> cases h

/-- A logical operator's domain is `bool`. -/
theorem fitsAt_logic {op : BinOp} {τ : STy} (h : op.FitsAt τ) (hl : (op = .and || op = .or) = true) :
    τ = .bool := by
  rcases h with ⟨hop, _⟩ | ⟨hop, _⟩ | ⟨_, hτ⟩
  · cases op <;> first | exact absurd hop (by decide) | exact absurd hl (by decide)
  · cases op <;> first | exact absurd hop (by decide) | exact absurd hl (by decide)
  · exact hτ

/-- Evaluating a local lvalue is never `stuck`. -/
theorem evalLoc_local_ns (G : Glob E) (F : Fr) (n : Nat) {Γ : RCtx} {τ : STy} (i : Idx Γ τ) :
    NS (evalLoc G F n (.local i)) := by
  cases n with
  | zero => rw [evalLoc.eq_1]; exact NS.halt' fun _ h => by cases h
  | succ n => exact NS.pure' _

/-- Evaluating a local lvalue, then continuing at its location. -/
theorem evalLoc_local_bind (G : Glob E) (F : Fr) (n : Nat) {Γ : RCtx} {τ : STy} {α : Type} (i : Idx Γ τ)
    {k : Loc E.layout Γ τ → EM E Γ α} (hk : NS (k (.local i))) : NS (evalLoc G F n (.local i) >>= k) := by
  cases n with
  | zero =>
    rw [evalLoc.eq_1, show (halt .timeout >>= k : EM E Γ α) = halt .timeout from rfl]
    exact NS.halt' fun _ h => by cases h
  | succ n =>
    simp only [evalLoc, pure_bind]
    exact hk

/-- Evaluating a state-variable lvalue, then continuing at its path. -/
theorem evalLoc_state_bind (G : Glob E) (F : Fr) (n : Nat) {Γ : RCtx} {τ : STy} {α : Type} (d : Decl)
    (h : d.varTy E = some τ) (hm : d.mutable = true) {k : Loc E.layout Γ τ → EM E Γ α}
    (hk : NS (k (.stor d.path))) : NS (evalLoc G F n (.state d h hm) >>= k) := by
  cases n with
  | zero =>
    rw [evalLoc.eq_1, show (halt .timeout >>= k : EM E Γ α) = halt .timeout from rfl]
    exact NS.halt' fun _ h => by cases h
  | succ n =>
    simp only [evalLoc, pure_bind]
    exact hk

/-- Reading and writing a local location is never `stuck`. -/
theorem readLoc_local_ns (F : Fr) {Γ : RCtx} {τ : STy} (i : Idx Γ τ) :
    NS (readLoc (E := E) F (Loc.local i)) :=
  NS.bind NS.locals' fun _ => NS.pure' _

theorem writeLoc_local_ns (F : Fr) (n : Nat) {Γ : RCtx} {τ : STy} (i : Idx Γ τ) (v : Val E.layout τ) :
    NS (writeLoc (E := E) F n (Loc.local i) v) :=
  NS.bind NS.locals' fun _ => fun _ _ h => by cases h

theorem readLoc_stor_ns {Γ : RCtx} (F : Fr) (p : SPath) {τ : STy} (hb : τ.byRef = false) (hc : E.cellTy p = τ)
    (hd : (Val.default E.layout τ).isSome = true) : NS (readLoc (E := E) (Γ := Γ) F (Loc.stor (τ := τ) p)) := by
  show NS (if τ.byRef = true then storRef τ p else readAt F p τ)
  rw [if_neg (by rw [hb]; exact Bool.false_ne_true)]
  exact readAt_ns F p hc hd

theorem writeLoc_stor_ns {Γ : RCtx} (F : Fr) (n : Nat) (p : SPath) {τ : STy} (hb : τ.byRef = false)
    (hc : E.cellTy p = τ) (v : Val E.layout τ) : NS (writeLoc (E := E) (Γ := Γ) F n (Loc.stor p) v) := by
  show NS (if τ.byRef = true then storeVal F n τ p v else writeAt F p v)
  rw [if_neg (by rw [hb]; exact Bool.false_ne_true)]
  exact writeAt_ns F p hc.symm v

/-- The binary operator of a compound assignment is in `binVal`'s domain,
or the assignment is a shift (`AssignOp.fits`). -/
theorem compound_dom {B : DeclName → DeclName → Bool} {op : AssignOp} {σ τ : STy} (h : op.fits B σ τ = true) :
    (op.kind? ≠ some .shift ∧ σ.implicit B τ = true ∧ (AssignOp.binOp op).FitsAt τ) ∨
      (op.kind? = some .shift ∧ τ.isBits = true ∧ σ.isAmount = true) := by
  unfold AssignOp.fits at h
  cases op <;> simp only [AssignOp.kind?] at h <;> (try simp only [Bool.and_eq_true] at h)
  all_goals first
    | exact .inl ⟨by decide, h.1, .inl ⟨rfl, h.2⟩⟩
    | exact .inl ⟨by decide, h.1, .inr (.inl ⟨rfl, h.2⟩)⟩
    | exact .inr ⟨rfl, h.1, h.2⟩
    | exact absurd h (by decide)

/-! ## Mappings -/

/-- **A storage reference agrees with the layout**: it names a path of its
type. -/
def RPost {τ : STy} (v : RVal E.layout τ) : Prop := ∀ h p, v = .val (.storRef h p) → E.pathTy p = some τ

theorem rpost_of_loc {τ : STy} (hτ : τ.loc? = none) (v : RVal E.layout τ) : RPost v :=
  fun h _ _ => by rw [hτ] at h; cases h

theorem Env.pathTy_go (p : SPath) (st : Step) : E.pathTy (p.go st) = (E.pathTy p).bind (E.stepTy · st) := by
  simp only [Env.pathTy, SPath.go, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem STy.byRef_of_value {τ : STy} (h : τ.isValue = true) : τ.byRef = false := by
  cases τ <;> first | rfl | cases h

theorem STy.cell_of_value {τ : STy} (h : τ.isValue = true) : τ.cell = τ := by
  cases τ <;> first | rfl | cases h

/-- A mapping value of value type is stored at its own type. -/
theorem cellTy_key {p : SPath} {τk τv : STy} (hp : E.pathTy p = some (.mapping τk τv)) (bs : List UInt8)
    (hv : τv.isValue = true) : E.cellTy (p.go (.key bs)) = τv := by
  simp only [Env.cellTy, Env.pathTy_go, hp, Option.bind_some, Env.stepTy, Option.map_some,
    Option.getD_some, STy.cell_of_value hv]

theorem pathTy_key {p : SPath} {τk τv : STy} (hp : E.pathTy p = some (.mapping τk τv)) (bs : List UInt8) :
    E.pathTy (p.go (.key bs)) = some τv := by
  simp only [Env.pathTy_go, hp, Option.bind_some, Env.stepTy]

theorem Val.word_isSome {D : Layout} {τ : STy} (h : τ.keyable = true) (x : Val D τ) : x.word.isSome = true := by
  cases τ <;> (try (cases h <;> done))
  · obtain ⟨_, _, rfl⟩ := Val.eq_int x; rfl
  · obtain ⟨_, rfl⟩ := Val.eq_bool x; rfl
  · obtain ⟨_, rfl⟩ := Val.eq_address x; rfl
  · obtain ⟨_, _, rfl⟩ := Val.eq_fixedBytes x; rfl
  · obtain ⟨_, _, rfl⟩ := Val.eq_fixed x; rfl
  · obtain ⟨_, rfl⟩ := Val.eq_enum x; rfl
  · cases x with
    | contract _ => rfl
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ => cases h

/-- **A mapping key of a keyable type is a key step**, never `stuck`. -/
theorem keyStep_nsp {Γ : RCtx} (F : Fr) (n : Nat) {τ : STy} (hτ : τ.keyable = true) (k : RVal E.layout τ) :
    NSP (keyStep (Γ := Γ) F n k) (fun st => ∃ bs, st = .key bs) := by
  unfold keyStep
  split
  · cases hτ
  · cases hτ
  · cases hτ
  · rename_i x _ _ _
    split
    · exact NSP.pure' ⟨_, rfl⟩
    · rename_i hw
      have := Val.word_isSome hτ x
      rw [hw] at this; cases this
  · rename_i _ _ _ hval
    exfalso
    cases k with
    | val x => exact hval x rfl
    | _ => cases hτ

/-- **The induction hypothesis** of expression progress at horizon `n`. -/
structure ExprNSAt (G : Glob E) (F : Fr) (n : Nat) : Prop where
  val : ∀ {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ), e.ValFrag → e.OpsOK → NS (evalE G F n e)
  pair : ∀ {Γ : RCtx} {σ ρ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ ρ), a.ValFrag → a.OpsOK →
    b.ValFrag → b.OpsOK → NS (evalPair G F n a b)
  ref : ∀ {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ), e.MapRef → e.OpsOK → NSP (evalE G F n e) RPost

theorem exprNSAt_zero (G : Glob E) (F : Fr) : ExprNSAt G F 0 where
  val _ _ _ := by rw [evalE.eq_1]; exact NS.halt' fun _ h => by cases h
  pair _ _ _ _ _ _ := by rw [evalPair.eq_1]; exact NS.halt' fun _ h => by cases h
  ref _ _ _ := by rw [evalE.eq_1]; exact NSP.halt' trivial

section
variable {G : Glob E} {F : Fr} {n : Nat}

theorem val_step (ih : ExprNSAt G F n) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) (hf : e.ValFrag) (ho : e.OpsOK) :
    NS (evalE G F (n + 1) e) := by
    cases e with
    | const _ => exact NS.pure' _
    | bytesLit _ _ => exact NS.pure' _
    | addressLit _ => exact NS.pure' _
    | bool _ => exact NS.pure' _
    | this _ => exact NS.pure' _
    | «local» i =>
      simp only [evalE]
      exact NS.bind NS.locals' fun _ => NS.pure' _
    | state d h =>
      simp only [evalE]
      rw [if_neg (by rw [hf.1]; exact Bool.false_ne_true), if_neg (by rw [hf.2.1]; exact Bool.false_ne_true)]
      exact NS.bind (readAt_ns F d.path hf.2.2.1 hf.2.2.2.1) fun _ => NS.pure' _
    | unary op a =>
      simp only [evalE]
      exact NS.bind (ih.val a hf.1 ho.2) fun v => NS.bind (getV_ns hf.2 v) fun x =>
        NS.bind (NS.lift' (unaryVal_ok _ ho.1 x)) fun _ => NS.pure' _
    | binary op a b =>
      simp only [evalE]
      split
      · rename_i hl
        have hb : τ = .bool := fitsAt_logic ho.1 hl
        subst hb
        refine NS.bind (ih.val a hf.1 ho.2.1) fun v => NS.bind (getV_ns rfl v) fun x => ?_
        obtain ⟨c, rfl⟩ := Val.eq_bool x
        show NS (match some (if c then (1 : Int) else 0) with
          | some kx =>
            if (decide (op = BinOp.and) && decide (kx = 0) || decide (op = BinOp.or) && decide (kx = 1)) = true then
              pure (RVal.val (Val.bool c))
            else do
              let __do_lift ← evalE G F n b
              let __do_lift ← getV __do_lift
              pure (RVal.val __do_lift)
          | none => halt (Halt.stuck "logical operand"))
        dsimp only
        split <;> split <;> first
          | exact NS.pure' _
          | exact NS.bind (ih.val b hf.2.1 ho.2.2) fun w => NS.bind (getV_ns rfl w) fun _ =>
              NS.pure' _
      · exact NS.bind (ih.pair a b hf.1 ho.2.1 hf.2.1 ho.2.2) fun p =>
          NS.bind (getV_ns hf.2.2 p.1) fun x => NS.bind (getV_ns hf.2.2 p.2) fun y =>
            NS.bind (NS.lift' (binVal_ok _ ho.1 x y)) fun _ => NS.pure' _
    | compare op a b =>
      simp only [evalE]
      exact NS.bind (ih.pair a b hf.1 ho.2.2.1 hf.2.1 ho.2.2.2) fun p =>
        NS.bind (getV_ns hf.2.2 p.1) fun x => NS.bind (getV_ns hf.2.2 p.2) fun y =>
          NS.bind (NS.lift' (cmpVal_ok ho.1 ho.2.1 x y)) fun _ => NS.pure' _
    | compareConst op qa qb =>
      simp only [evalE]
      exact NS.bind (NS.lift' (cmpConst_ok ho qa qb)) fun _ => NS.pure' _
    | shiftLike op a b h =>
      simp only [evalE]
      exact NS.bind (ih.pair a b hf.1 ho.2.1 hf.2.1 ho.2.2) fun p =>
        NS.bind (NS.lift' (amount_ok h p.2)) fun k => NS.bind (getV_ns hf.2.2 p.1) fun x =>
          NS.bind (NS.lift' (shiftVal_ok _ k ho.1 x)) fun _ => NS.pure' _
    | cond c a b =>
      simp only [evalE]
      refine NS.bind (ih.val c hf.1 ho.1) fun v => NS.bind (getV_ns rfl v) fun x => ?_
      split
      · exact ih.val a hf.2.1 ho.2.1
      · exact ih.val b hf.2.2.1 ho.2.2
    | conv a h =>
      simp only [evalE]
      exact NS.bind (ih.val a hf.1 ho) fun v => convRV_ns F n h hf.2.2 v
    | assign l e =>
      simp only [evalE]
      cases l with
      | «local» i =>
        exact NS.bind (ih.val e hf.2.1 ho.2) fun v => evalLoc_local_bind G F n i <|
          NS.bind (getV_ns hf.2.2 v) fun x => NS.bind (writeLoc_local_ns F n i x) fun _ => NS.pure' _
      | state d h hm =>
        exact NS.bind (ih.val e hf.2.1 ho.2) fun v => evalLoc_state_bind G F n d h hm <|
          NS.bind (getV_ns hf.2.2 v) fun x =>
            NS.bind (writeLoc_stor_ns F n d.path hf.1.1 hf.1.2.1 x) fun _ => NS.pure' _
      | _ => exact hf.1.elim
    | @compound _ σ op l e h =>
      simp only [evalE]
      have core : ∀ (L : Loc E.layout Γ τ) (v : RVal E.layout σ), NS (readLoc F L) →
          (∀ x, NS (writeLoc F n L x)) → NS (do
            let old ← readLoc F L
            let new ← match op.kind? with
              | some .shift => lift (shiftVal F.checked (if op = .shl then .shl else if op = .sar then .sar else .shr)
                  (← lift v.amount) old)
              | _ => do
                let y ← getV (← convRV F n τ v)
                lift (binVal F.checked (AssignOp.binOp op) old y)
            writeLoc F n L new
            return RVal.val new) := by
        intro L v hr hw
        refine NS.bind hr fun old => ?_
        dsimp only
        rcases compound_dom h with ⟨hk, hi, hfit⟩ | ⟨hk, hb, ha⟩
        · split
          · rename_i hk'; exact absurd hk' hk
          · exact NS.bind (convRV_ns F n (.inl hi) hf.2.2.2 v) fun w => NS.bind (getV_ns hf.2.2.1 w) fun y =>
              NS.bind (NS.lift' (binVal_ok _ hfit old y)) fun nw => NS.bind (hw nw) fun _ => NS.pure' _
        · split
          · refine NS.bind (NS.lift' (amount_ok ha v)) fun k =>
              NS.bind (NS.lift' (shiftVal_ok _ k (.inl ⟨?_, hb⟩) old)) fun nw => NS.bind (hw nw) fun _ => NS.pure' _
            split
            · rfl
            · split <;> rfl
          · rename_i hn; exact (hn hk).elim
      cases l with
      | «local» i =>
        exact NS.bind (ih.val e hf.2.1 ho.2) fun v => evalLoc_local_bind G F n i <|
          core _ v (readLoc_local_ns F i) (writeLoc_local_ns F n i)
      | state d hd hm =>
        exact NS.bind (ih.val e hf.2.1 ho.2) fun v => evalLoc_state_bind G F n d hd hm <|
          core _ v (readLoc_stor_ns F d.path hf.1.1 hf.1.2.1 hf.1.2.2) (writeLoc_stor_ns F n d.path hf.1.1 hf.1.2.1)
      | _ => exact hf.1.elim
    | incDec inc pre l =>
      simp only [evalE]
      cases l with
      | «local» i =>
        exact evalLoc_local_bind G F n i <| NS.bind (readLoc_local_ns F i) fun old =>
          NS.bind (NS.lift' (incDecVal_ok _ inc ho.1 old)) fun nw =>
            NS.bind (writeLoc_local_ns F n i nw) fun _ => NS.pure' _
      | state d hd hm =>
        exact evalLoc_state_bind G F n d hd hm <|
          NS.bind (readLoc_stor_ns F d.path hf.1 hf.2.1 hf.2.2) fun old =>
          NS.bind (NS.lift' (incDecVal_ok _ inc ho.1 old)) fun nw =>
            NS.bind (writeLoc_stor_ns F n d.path hf.1 hf.2.1 nw) fun _ => NS.pure' _
      | _ => exact hf.elim
    | indexMapping a k =>
      simp only [evalE]
      refine NSP.ns (NSP.bind (R := fun _ => True) (ih.ref a hf.1 ho.1) fun v hv => ?_)
      cases v with
      | val x =>
        rw [show getV (Γ := Γ) (RVal.val x) = pure x from rfl, pure_bind]
        cases x with
        | storRef hs p =>
          have hp := hv hs p rfl
          refine NSP.bind (NSP.of_ns (ih.val k hf.2.1 ho.2)) fun kv _ =>
            NSP.bind (keyStep_nsp F n hf.2.2.1 kv) fun st hst => ?_
          obtain ⟨bs, rfl⟩ := hst
          exact NSP.bind (NSP.of_ns (readLoc_stor_ns F _ (STy.byRef_of_value hf.2.2.2.1)
            (cellTy_key hp bs hf.2.2.2.1) hf.2.2.2.2)) fun _ _ => NSP.pure' trivial
        | memRef hm _ => cases hm
        | cdRef hm _ => cases hm
    | _ => exact hf.elim

theorem pair_step (ih : ExprNSAt G F n) {Γ : RCtx} {σ ρ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ ρ)
    (ha : a.ValFrag) (ha' : a.OpsOK) (hb : b.ValFrag) (hb' : b.OpsOK) : NS (evalPair G F (n + 1) a b) := by
  simp only [evalPair]
  split
  · exact NS.bind (ih.val b hb hb') fun _ => NS.bind (ih.val a ha ha') fun _ => NS.pure' _
  · exact NS.bind (ih.val a ha ha') fun _ => NS.bind (ih.val b hb hb') fun _ => NS.pure' _

/-- A storage reference to a mapping path of its type agrees. -/
theorem storRef_map_nsp {Γ : RCtx} {τk τv : STy} (p : SPath) (hp : E.pathTy p = some (.mapping τk τv)) :
    NSP (do return RVal.val (← storRef (E := E) (Γ := Γ) (.mapping τk τv) p)) RPost := by
  unfold storRef
  rw [dif_pos (show (STy.mapping τk τv).loc? = some .storage from rfl)]
  refine NSP.bind (NSP.pure' (Q := fun x => x = Val.storRef (show (STy.mapping τk τv).loc? = some .storage
    from rfl) p) rfl) fun x hx => NSP.pure' ?_
  intro h p' e
  subst hx
  simp only [RVal.val.injEq, Val.storRef.injEq] at e
  rw [← e]
  exact hp

theorem ref_step (ih : ExprNSAt G F n) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) (hm : e.MapRef) (ho : e.OpsOK) :
    NSP (evalE G F (n + 1) e) RPost := by
  cases e with
  | state d h =>
    obtain ⟨hc, hp, τk, τv, rfl⟩ := hm
    simp only [evalE]
    rw [if_neg (by rw [hc]; exact Bool.false_ne_true), if_pos (show (STy.mapping τk τv).byRef = true from rfl)]
    exact storRef_map_nsp d.path hp
  | indexMapping a k =>
    obtain ⟨ha, hk, hkey, τk', τv', rfl⟩ := hm
    simp only [evalE]
    refine NSP.bind (ih.ref a ha ho.1) fun v hv => ?_
    cases v with
    | val x =>
      rw [show getV (Γ := Γ) (RVal.val x) = pure x from rfl, pure_bind]
      cases x with
      | storRef hs p =>
        have hp := hv hs p rfl
        refine NSP.bind (NSP.of_ns (ih.val k hk ho.2)) fun kv _ =>
          NSP.bind (keyStep_nsp F n hkey kv) fun st hst => ?_
        obtain ⟨bs, rfl⟩ := hst
        show NSP (do return RVal.val (← (if (STy.mapping τk' τv').byRef = true then storRef _ (p.go (.key bs))
          else readAt F (p.go (.key bs)) _))) RPost
        rw [if_pos (show (STy.mapping τk' τv').byRef = true from rfl)]
        exact storRef_map_nsp _ (pathTy_key hp bs)
      | memRef hm _ => cases hm
      | cdRef hm _ => cases hm
  | _ => exact hm.elim

end

/-- **Expression progress at every horizon.** -/
theorem exprNSAt (G : Glob E) (F : Fr) : ∀ n, ExprNSAt G F n
  | 0 => exprNSAt_zero G F
  | n + 1 =>
    have ih := exprNSAt G F n
    { val := fun e hf ho => val_step ih e hf ho
      pair := fun a b ha ha' hb hb' => pair_step ih a b ha ha' hb hb'
      ref := fun e hm ho => ref_step ih e hm ho }

/-- **Progress on the value fragment**: evaluating an expression of the
value fragment that is in the operations' domains is never `stuck`, at any
horizon, from any state (it may time out, revert or panic). -/
theorem evalE_valFrag_ns (G : Glob E) (F : Fr) (n : Nat) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (hf : e.ValFrag) (ho : e.OpsOK) : NS (evalE G F n e) :=
  (exprNSAt G F n).val e hf ho

end Solidity.Source
