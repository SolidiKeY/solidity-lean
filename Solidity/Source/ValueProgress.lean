import Solidity.Source.Elaborated
import Solidity.Source.Value

/-!
# Progress of the value operations (lane V04b)

The pure operations of `Solidity/Source/Value.lean` halt `stuck` only on
operands outside their domain. Here each is shown never `stuck` on the
operands S01's typing gives it, through the premises its `toR` image
carries:

| Operation | Domain (`toR` premise) |
|---|---|
| `binVal` | `+ - * / %` at a numeric type (`arith`), `& \| ^` at `int`/`bytesN` (`bit`), `&& \|\|` at `bool` (`logic`): `BinOp.FitsAt` |
| `cmpVal` | `< > <= >=` at an ordered type (`order`), `== !=` at a type with equality (`eq`): `BinOp.ComparesAt` |
| `shiftVal` | `<< >> >>>` at `int`/`bytesN`, `**` at `int` (`shift`, `exp`): `BinOp.ShiftsAt` |
| `unaryVal` | `-` at `int`/`fixed`, `!` at `bool`, `~` at `int`/`bytesN`: `PrefixOp.AppliesAt` |
| `incDecVal` | a numeric type |
| `RVal.amount` | an amount type (`isAmount`) |
| `RVal.get` | a type no constant or literal has (`STy.Plain`) |

`binOpName_admits` shows that the operator `toR` reads off
the syntax is in the domain the rule's kind gives it. The census of every
`stuck` site of the interpreter, and which invariant rules out each, is in
`docs/feature-work/source-soundness.md`.
-/

namespace Solidity.Source

variable {D : Layout}

/-- **A pure step that is never `stuck`**: it succeeds or halts
otherwise (a panic, a revert). -/
def NotStuckR {α : Type} (r : R α) : Prop := ∀ w, r ≠ .error (.stuck w)

theorem NotStuckR.pure {α : Type} (a : α) : NotStuckR (pure a : R α) := fun _ h => by cases h

theorem NotStuckR.panic {α : Type} (c : PanicCode) : NotStuckR (panic c : R α) := fun _ h => by cases h

theorem NotStuckR.bind {α β : Type} {r : R α} {k : α → R β} (hr : NotStuckR r)
    (hk : ∀ a, NotStuckR (k a)) : NotStuckR (r >>= k) := by
  intro w h
  cases r with
  | ok a => exact hk a w h
  | error e =>
    have e' : e = .stuck w := by cases h; rfl
    subst e'
    exact hr w rfl

/-! ## Operators by rule kind -/

/-- **The operators a rule kind admits**: the operator `toR` reads off
the syntax (`Syn.binOpName`) for an expression of that kind. -/
def BinKind.admits : BinKind → BinOp → Bool
  | .arith, op => op == .add || op == .sub || op == .mul || op == .div || op == .mod
  | .bit, op => op == .bitAnd || op == .bitOr || op == .bitXor
  | .shift, op => op == .shl || op == .sar || op == .shr
  | .exp, op => op == .exp
  | .order, op => op == .lt || op == .gt || op == .le || op == .ge
  | .eq, op => op == .eq || op == .ne
  | .logic, op => op == .and || op == .or

/-- Every binary expression's operator is one its kind admits. -/
theorem binOpName_admits (e : Syn .expr) {k : BinKind} {a b : Syn .expr}
    (h : e.binOp? = some (k, a, b)) : k.admits e.binOpName = true := by
  have hb : (match e.binOp? with
      | some (k, _, _) => k.admits e.binOpName
      | none => true) = true := by
    cases e <;> (try rfl) <;> (rename_i op _ _; cases op <;> rfl)
  rw [h] at hb
  exact hb

/-! ## Values of a type without a location are plain -/

theorem Val.eq_int {t : IntTy} (x : Val D (.int t)) : ∃ v h, x = .int v h := by
  cases x with
  | int v h => exact ⟨v, h, rfl⟩
  | memRef h _ => cases h
  | storRef h _ => cases h
  | cdRef h _ => cases h

theorem Val.eq_fixed {t : FixTy} (x : Val D (.fixed t)) : ∃ v h, x = .fixed v h := by
  cases x with
  | fixed v h => exact ⟨v, h, rfl⟩
  | memRef h _ => cases h
  | storRef h _ => cases h
  | cdRef h _ => cases h

theorem Val.eq_bool (x : Val D .bool) : ∃ b, x = .bool b := by
  cases x with
  | bool b => exact ⟨b, rfl⟩
  | memRef h _ => cases h
  | storRef h _ => cases h
  | cdRef h _ => cases h

theorem Val.eq_fixedBytes {n : Nat} {hn : 1 ≤ n ∧ n ≤ 32} (x : Val D (.fixedBytes n hn)) :
    ∃ bs h, x = .fixedBytes bs h := by
  cases x with
  | fixedBytes bs h => exact ⟨bs, h, rfl⟩
  | memRef h _ => cases h
  | storRef h _ => cases h
  | cdRef h _ => cases h

/-! ## Arithmetic -/

theorem intRes_ok (t : IntTy) (c : Bool) (v : Int) : NotStuckR (intRes (D := D) t c v) := by
  intro w h
  unfold intRes at h
  split at h
  · cases h
  · split at h <;> cases h

theorem fixRes_ok (t : FixTy) (c : Bool) (v : Int) : NotStuckR (fixRes (D := D) t c v) := by
  intro w h
  unfold fixRes at h
  split at h
  · cases h
  · split at h <;> cases h

theorem intBin_ok (t : IntTy) (c : Bool) {op : BinOp}
    (hop : (BinKind.arith.admits op || BinKind.bit.admits op) = true) (x y : Int) :
    NotStuckR (intBin (D := D) t c op x y) := by
  intro w h
  cases op <;> (try exact absurd hop (by decide)) <;> simp only [intBin] at h <;>
    first
    | exact intRes_ok t c _ w h
    | cases h
    | (split at h
       · cases h
       · exact intRes_ok t c _ w h)

theorem fixBin_ok (t : FixTy) (c : Bool) {op : BinOp} (hop : BinKind.arith.admits op = true) (x y : Int) :
    NotStuckR (fixBin (D := D) t c op x y) := by
  intro w h
  cases op <;> (try exact absurd hop (by decide)) <;> simp only [fixBin] at h <;>
    first
    | exact fixRes_ok t c _ w h
    | (split at h
       · cases h
       · exact fixRes_ok t c _ w h)

theorem bytesBin_ok {op : BinOp} (hop : BinKind.bit.admits op = true) (xs ys : List UInt8) :
    NotStuckR (bytesBin op xs ys) := by
  intro w h
  cases op <;> (try exact absurd hop (by decide)) <;> cases h

/-- **The domain of `binVal`**: an operator of `arith` at a numeric type,
of `bit` at a bit type, of `logic` at `bool` (`toR` of `arith`, `bit`,
`logic`). -/
def BinOp.FitsAt (op : BinOp) (τ : STy) : Prop :=
  (BinKind.arith.admits op = true ∧ τ.isNumeric = true) ∨ (BinKind.bit.admits op = true ∧ τ.isBits = true) ∨
    (BinKind.logic.admits op = true ∧ τ = .bool)

/-- **`binVal` is never stuck in its domain.** -/
theorem binVal_ok (c : Bool) {op : BinOp} {τ : STy} (h : op.FitsAt τ) (x y : Val D τ) :
    NotStuckR (binVal c op x y) := by
  rcases h with ⟨hop, hτ⟩ | ⟨hop, hτ⟩ | ⟨hop, hτ⟩
  · cases τ <;> (try (cases hτ <;> done))
    · obtain ⟨_, _, rfl⟩ := Val.eq_int x
      obtain ⟨_, _, rfl⟩ := Val.eq_int y
      exact intBin_ok _ c (by rw [hop]; rfl) _ _
    · obtain ⟨_, _, rfl⟩ := Val.eq_fixed x
      obtain ⟨_, _, rfl⟩ := Val.eq_fixed y
      exact fixBin_ok _ c hop _ _
  · cases τ <;> (try (cases hτ <;> done))
    · obtain ⟨_, _, rfl⟩ := Val.eq_int x
      obtain ⟨_, _, rfl⟩ := Val.eq_int y
      exact intBin_ok _ c (by rw [hop, Bool.or_true]) _ _
    · obtain ⟨_, _, rfl⟩ := Val.eq_fixedBytes x
      obtain ⟨_, _, rfl⟩ := Val.eq_fixedBytes y
      exact NotStuckR.bind (bytesBin_ok hop _ _) fun _ => NotStuckR.pure _
  · subst hτ
    obtain ⟨_, rfl⟩ := Val.eq_bool x
    obtain ⟨_, rfl⟩ := Val.eq_bool y
    cases op <;> (try exact absurd hop (by decide)) <;> exact NotStuckR.pure _


theorem Val.eq_address {p : Bool} (x : Val D (.address p)) : ∃ a, x = .address a := by
  cases x with
  | address a => exact ⟨a, rfl⟩
  | memRef h _ => cases h
  | storRef h _ => cases h
  | cdRef h _ => cases h

theorem Val.eq_enum {d : DeclName} (x : Val D (.enum d)) : ∃ i, x = .enum i := by
  cases x with
  | enum i => exact ⟨i, rfl⟩
  | memRef h _ => cases h
  | storRef h _ => cases h
  | cdRef h _ => cases h

theorem Val.eq_extFn {ps rs : List STy} {m : Option Mutability} (x : Val D (.fn true ps rs m)) :
    ∃ a sel h, x = .externalFn a sel h := by
  cases x with
  | externalFn a sel h => exact ⟨a, sel, h, rfl⟩
  | memRef h _ => cases h
  | storRef h _ => cases h
  | cdRef h _ => cases h

/-! ## Comparisons -/

/-- Every value of an ordered type, or of a type with equality, has an
order key. -/
theorem Val.key_isSome {τ : STy} (hτ : (τ.isOrdered || τ.hasEq) = true) (v : Val D τ) :
    v.key.isSome = true := by
  cases τ <;> (try (cases hτ <;> done))
  · obtain ⟨_, _, rfl⟩ := Val.eq_int v; rfl
  · obtain ⟨_, rfl⟩ := Val.eq_bool v; rfl
  · obtain ⟨_, rfl⟩ := Val.eq_address v; rfl
  · obtain ⟨_, _, rfl⟩ := Val.eq_fixedBytes v; rfl
  · obtain ⟨_, _, rfl⟩ := Val.eq_fixed v; rfl
  · obtain ⟨_, rfl⟩ := Val.eq_enum v; rfl
  · rename_i ext _ _ _
    cases ext
    · cases hτ
    · obtain ⟨_, _, _, rfl⟩ := Val.eq_extFn v; rfl

/-- **`cmpVal` is never stuck** on a comparison operator at an ordered type
or a type with equality (`toR` of `order` and `eq`). -/
theorem cmpVal_ok {op : BinOp} (hop : (BinKind.order.admits op || BinKind.eq.admits op) = true) {τ : STy}
    (hτ : (τ.isOrdered || τ.hasEq) = true) (a b : Val D τ) : NotStuckR (cmpVal op a b) := by
  intro w h
  unfold cmpVal at h
  rcases ha : a.key with _ | x
  · have := Val.key_isSome hτ a; rw [ha] at this; cases this
  rcases hb : b.key with _ | y
  · have := Val.key_isSome hτ b; rw [hb] at this; cases this
  rw [ha, hb] at h
  cases op <;> (try exact absurd hop (by decide)) <;> cases h

/-! ## Shifts, powers, unary operators -/

theorem intPow_ok (t : IntTy) (c : Bool) (x : Int) (k : Nat) : NotStuckR (intPow (D := D) t c x k) := by
  intro w h
  unfold intPow at h
  split at h
  · exact intRes_ok t c _ w h
  · split at h
    · exact intRes_ok t c _ w h
    · split at h <;> cases h

/-- **`shiftVal` is never stuck** on a shift at `int`/`bytesN` or a power
at `int` (`toR` of `shift` and `exp`). -/
theorem shiftVal_ok (c : Bool) {op : BinOp} (k : Nat) {τ : STy}
    (h : (BinKind.shift.admits op = true ∧ τ.isBits = true) ∨ (op = .exp ∧ τ.isInt = true))
    (x : Val D τ) : NotStuckR (shiftVal c op k x) := by
  rcases h with ⟨hop, hτ⟩ | ⟨hop, hτ⟩
  · cases τ <;> (try (cases hτ <;> done))
    · obtain ⟨_, _, rfl⟩ := Val.eq_int x
      intro w h
      cases op <;> (try exact absurd hop (by decide)) <;> simp only [shiftVal] at h <;>
        (try split at h) <;> cases h
    · obtain ⟨_, _, rfl⟩ := Val.eq_fixedBytes x
      intro w h
      cases op <;> (try exact absurd hop (by decide)) <;> cases h
  · subst hop
    cases τ <;> (try (cases hτ <;> done))
    obtain ⟨_, _, rfl⟩ := Val.eq_int x
    exact intPow_ok _ c _ _

/-- **The domain of `unaryVal`** (`toR` of `neg`, `negFixed`, `not`,
`bitNot`). -/
def PrefixOp.AppliesAt (op : PrefixOp) (τ : STy) : Prop :=
  (op = .neg ∧ (τ.isInt || τ matches .fixed _) = true) ∨ (op = .not ∧ τ = .bool) ∨
    (op = .bitNot ∧ τ.isBits = true)

/-- **`unaryVal` is never stuck in its domain.** -/
theorem unaryVal_ok (c : Bool) {op : PrefixOp} {τ : STy} (h : op.AppliesAt τ) (x : Val D τ) :
    NotStuckR (unaryVal c op x) := by
  rcases h with ⟨hop, hτ⟩ | ⟨hop, hτ⟩ | ⟨hop, hτ⟩ <;> subst hop
  · cases τ <;> (try (cases hτ <;> done))
    · obtain ⟨_, _, rfl⟩ := Val.eq_int x; exact intRes_ok _ c _
    · obtain ⟨_, _, rfl⟩ := Val.eq_fixed x; exact fixRes_ok _ c _
  · subst hτ
    obtain ⟨_, rfl⟩ := Val.eq_bool x
    exact NotStuckR.pure _
  · cases τ <;> (try (cases hτ <;> done))
    · obtain ⟨_, _, rfl⟩ := Val.eq_int x; exact NotStuckR.pure _
    · obtain ⟨_, _, rfl⟩ := Val.eq_fixedBytes x; exact NotStuckR.pure _

/-- **`incDecVal` is never stuck at a numeric type** (`toR` of `incDec`). -/
theorem incDecVal_ok (c inc : Bool) {τ : STy} (hτ : τ.isNumeric = true) (x : Val D τ) :
    NotStuckR (incDecVal c inc x) := by
  cases τ <;> (try (cases hτ <;> done))
  · obtain ⟨_, _, rfl⟩ := Val.eq_int x; exact intRes_ok _ c _
  · obtain ⟨_, _, rfl⟩ := Val.eq_fixed x; exact fixRes_ok _ c _

/-- **A shift amount or exponent of an amount type is never stuck.** -/
theorem amount_ok {σ : STy} (hσ : σ.isAmount = true) (v : RVal D σ) : NotStuckR v.amount := by
  intro w h
  cases σ <;> (try (cases hσ <;> done))
  · cases v with
    | val x =>
      obtain ⟨_, _, rfl⟩ := Val.eq_int x
      cases h
  · cases v with
    | val x =>
      cases x with
      | memRef hl _ => cases hl
      | storRef hl _ => cases hl
      | cdRef hl _ => cases hl
    | const _ => cases h
  · cases v with
    | val x =>
      cases x with
      | memRef hl _ => cases hl
      | storRef hl _ => cases hl
      | cdRef hl _ => cases hl
    | hex _ _ => cases h

/-! ## Elaborated terms stay in the domains -/

mutual

/-- **Every operator node is in its operation's domain**: what `Typed.toR`
guarantees of the resolved terms it builds (`RExpr` itself does not tie a
`binary` node's operator to its type). -/
def RExpr.OpsOK {E : Env} {Γ : RCtx} : {τ : STy} → RExpr E Γ τ → Prop
  | _, .const _ | _, .bytesLit _ _ | _, .addressLit _ | _, .bool _ | _, .str _ | _, .local _
  | _, .state _ _ | _, .this _ | _, .compareConst _ _ _ | _, .magic _ _ _ => True
  | _, .tuple es => RArgs.OpsOK es
  | _, .conv e _ | _, .convExplicit e _ | _, .length e _ | _, .payable e | _, .balance e
  | _, .member e _ _ => RExpr.OpsOK e
  | τ, .unary op e => op.AppliesAt τ ∧ RExpr.OpsOK e
  | τ, .incDec _ _ l => τ.isNumeric = true ∧ RLVal.OpsOK l
  | _, .delete l => RLVal.OpsOK l
  | τ, .binary op a b => op.FitsAt τ ∧ RExpr.OpsOK a ∧ RExpr.OpsOK b
  | _, .compare (τ := τ) op a b =>
    (BinKind.order.admits op || BinKind.eq.admits op) = true ∧ (τ.isOrdered || τ.hasEq) = true ∧
      RExpr.OpsOK a ∧ RExpr.OpsOK b
  | τ, .shiftLike op a b _ =>
    ((BinKind.shift.admits op = true ∧ τ.isBits = true) ∨ (op = .exp ∧ τ.isInt = true)) ∧
      RExpr.OpsOK a ∧ RExpr.OpsOK b
  | _, .cond c a b => RExpr.OpsOK c ∧ RExpr.OpsOK a ∧ RExpr.OpsOK b
  | _, .assign l e => RLVal.OpsOK l ∧ RExpr.OpsOK e
  | _, .compound _ l e _ => RLVal.OpsOK l ∧ RExpr.OpsOK e
  | _, .indexArray a i _ | _, .indexMapping a i | _, .indexBytes a i _ => RExpr.OpsOK a ∧ RExpr.OpsOK i
  | _, .call _ _ args => RConvArgs.OpsOK args
  | _, .builtin _ args _ => RArgs.OpsOK args
  | _, .structNew _ args => RConvArgs.OpsOK args
  | _, .extCall t _ _ v args => RExpr.OpsOK t ∧ RExpr.OpsOK v ∧ RConvArgs.OpsOK args
  | _, .transfer a v | _, .send a v => RExpr.OpsOK a ∧ RExpr.OpsOK v
  | _, .abiEncode _ args => RArgs.OpsOK args
  | _, .assignCopy l e _ => RLVal.OpsOK l ∧ RExpr.OpsOK e

def RArgs.OpsOK {E : Env} {Γ : RCtx} : {τs : List STy} → RArgs E Γ τs → Prop
  | _, .nil => True
  | _, .cons e es => RExpr.OpsOK e ∧ RArgs.OpsOK es

def RConvArgs.OpsOK {E : Env} {Γ : RCtx} : {τs : List STy} → RConvArgs E Γ τs → Prop
  | _, .nil => True
  | _, .cons e _ es => RExpr.OpsOK e ∧ RConvArgs.OpsOK es

def RLVal.OpsOK {E : Env} {Γ : RCtx} : {τ : STy} → RLVal E Γ τ → Prop
  | _, .local _ | _, .state _ _ _ => True
  | _, .indexArray a _ i _ | _, .indexMapping a i | _, .indexBytes a _ i _ => RExpr.OpsOK a ∧ RExpr.OpsOK i
  | _, .member a _ _ _ => RExpr.OpsOK a

end

theorem RArgs.convert_opsOK {E : Env} {Γ : RCtx} : {σs : List STy} → (ps : List STy) →
    (a : RArgs E Γ σs) → (h : argsFit E.isBase σs ps = true) → RArgs.OpsOK a →
    RConvArgs.OpsOK (a.convert ps h)
  | [], [], .nil, _, _ => trivial
  | _ :: _, _ :: ps, .cons _ es, _, ho => by
    simp only [RArgs.convert, RConvArgs.OpsOK]
    exact And.intro ho.1 (RArgs.convert_opsOK ps es _ ho.2)
  | [], _ :: _, _, h, _ => by simp only [argsFit, List.length_nil, List.length_cons] at h; cases h
  | _ :: _, [], _, h, _ => by simp only [argsFit, List.length_nil, List.length_cons] at h; cases h

mutual

/-- **Elaborated expressions stay in the operations' domains.** -/
theorem Typed.toR_opsOK {Γ : Ctx} : {e : Syn .expr} → {τ : STy} → (d : Typed Γ e τ) → d.toR.OpsOK
  | _, _, .const _ _ _ | _, _, .litBytes _ | _, _, .litAddress _ | _, _, .bool _ | _, _, .str _
  | _, _, .hexStr _ | _, _, .unicodeStr _ | _, _, .loc _ _ | _, _, .state _ _ | _, _, .this _ _
  | _, _, .compareConst _ _ _ _ | _, _, .magic _ _ _ _ => trivial
  | _, _, .paren d => Typed.toR_opsOK d
  | _, _, .tuple d ds _ => And.intro (Typed.toR_opsOK d) (TypedSlots.toR_opsOK ds)
  | _, _, .neg d _ => And.intro (.inl ⟨rfl, rfl⟩) (Typed.toR_opsOK d)
  | _, _, .negFixed d => And.intro (.inl ⟨rfl, rfl⟩) (Typed.toR_opsOK d)
  | _, _, .not d => And.intro (.inr (.inl ⟨rfl, rfl⟩)) (Typed.toR_opsOK d)
  | _, _, .bitNot d h => And.intro (.inr (.inr ⟨rfl, h⟩)) (Typed.toR_opsOK d)
  | _, _, .incDec _ l hn => And.intro hn (LVal.toR_opsOK l)
  | _, _, .incDecSuffix l hn => And.intro hn (LVal.toR_opsOK l)
  | _, _, .delete l _ => LVal.toR_opsOK l
  | _, _, .arith hk da db _ hn _ =>
    And.intro (.inl ⟨binOpName_admits _ hk, hn⟩) (And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK db))
  | _, _, .bit hk da db _ hn =>
    And.intro (.inr (.inl ⟨binOpName_admits _ hk, hn⟩)) (And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK db))
  | _, _, .logic hk da db =>
    And.intro (.inr (.inr ⟨binOpName_admits _ hk, rfl⟩)) (And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK db))
  | _, _, .shift hk da db h1 _ _ =>
    And.intro (.inl ⟨binOpName_admits _ hk, h1⟩) (And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK db))
  | _, _, .exp _ da db h1 _ _ =>
    And.intro (.inr ⟨rfl, h1⟩) (And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK db))
  | _, _, .order hk da db _ hn =>
    And.intro (by rw [binOpName_admits _ hk]; rfl) (And.intro (by rw [hn]; rfl)
      (And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK db)))
  | _, _, .eq hk da db _ hn =>
    And.intro (by rw [binOpName_admits _ hk, Bool.or_true]) (And.intro (by rw [hn, Bool.or_true])
      (And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK db)))
  | _, _, .cond dc da db _ =>
    And.intro (Typed.toR_opsOK dc) (And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK db))
  | _, _, .assign l db _ _ => And.intro (LVal.toR_opsOK l) (Typed.toR_opsOK db)
  | _, _, .compound l db _ => And.intro (LVal.toR_opsOK l) (Typed.toR_opsOK db)
  | _, _, .indexArray da di _ _ => And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK di)
  | _, _, .indexMapping da di _ => And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK di)
  | _, _, .indexBytes da _ di _ _ => And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK di)
  | _, _, .length da _ => Typed.toR_opsOK da
  | _, _, .convElem dx _ _ => Typed.toR_opsOK dx
  | _, _, .convUser _ dx _ => Typed.toR_opsOK dx
  | _, _, .payable dx _ => Typed.toR_opsOK dx
  | _, _, .callInternal da _ _ => RArgs.convert_opsOK _ _ _ (TypedArgs.toR_opsOK da)
  | _, _, .balance da => Typed.toR_opsOK da
  | _, _, .builtinCall _ _ da _ => TypedArgs.toR_opsOK da
  | _, _, .member da _ => Typed.toR_opsOK da
  | _, _, .structNew _ _ da _ => RArgs.convert_opsOK _ _ _ (TypedArgs.toR_opsOK da)
  | _, _, .extCall dc da _ _ =>
    And.intro (Typed.toR_opsOK dc) (And.intro trivial (RArgs.convert_opsOK _ _ _ (TypedArgs.toR_opsOK da)))
  | _, _, .extCallValue dc dv _ da _ _ _ =>
    And.intro (Typed.toR_opsOK dc) (And.intro (Typed.toR_opsOK dv)
      (RArgs.convert_opsOK _ _ _ (TypedArgs.toR_opsOK da)))
  | _, _, .transfer da dv _ => And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK dv)
  | _, _, .send da dv _ => And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK dv)
  | _, _, .abiEncode _ _ da _ => TypedArgs.toR_opsOK da
  | _, _, .assignCopy l db _ => And.intro (LVal.toR_opsOK l) (Typed.toR_opsOK db)

theorem TypedArgs.toR_opsOK {Γ : Ctx} : {es : Syn (.list .expr)} → {τs : List STy} →
    (d : TypedArgs Γ es τs) → RArgs.OpsOK d.toR
  | _, _, .nil => trivial
  | _, _, .cons d ds => And.intro (Typed.toR_opsOK d) (TypedArgs.toR_opsOK ds)

theorem TypedSlots.toR_opsOK {Γ : Ctx} : {es : Syn (.list (.opt .expr))} → {τs : List STy} →
    (d : TypedSlots Γ es τs) → RArgs.OpsOK d.toR
  | _, _, .nil => trivial
  | _, _, .cons d ds => And.intro (Typed.toR_opsOK d) (TypedSlots.toR_opsOK ds)

theorem LVal.toR_opsOK {Γ : Ctx} : {e : Syn .expr} → {τ : STy} → (d : LVal Γ e τ) → RLVal.OpsOK d.toR
  | _, _, .loc _ _ | _, _, .state _ _ _ => trivial
  | _, _, .paren l => LVal.toR_opsOK l
  | _, _, .indexArray da _ di _ _ => And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK di)
  | _, _, .indexMapping da di _ => And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK di)
  | _, _, .indexBytes da _ di _ => And.intro (Typed.toR_opsOK da) (Typed.toR_opsOK di)
  | _, _, .member da _ _ => Typed.toR_opsOK da

end

/-! ## Statements -/

def ROptBool.OpsOK {E : Env} {Γ : RCtx} : ROptBool E Γ → Prop
  | .none => True
  | .some c => c.OpsOK

def ROptExpr.OpsOK {E : Env} {Γ : RCtx} : ROptExpr E Γ → Prop
  | .none => True
  | .some e => e.OpsOK

mutual

/-- Every expression of a statement keeps the operations' domains. -/
def RStmt.OpsOK {E : Env} {R : List STy} {M : Bool} : {k : SCtx} → {Γ Γ' : RCtx} → RStmt E R M k Γ Γ' → Prop
  | _, _, _, .expr e => e.OpsOK
  | _, _, _, .placeholder _ | _, _, _, .declVar _ | _, _, _, .skip | _, _, _, .brk | _, _, _, .cont
  | _, _, _, .ret _ | _, _, _, .rethrow _ => True
  | _, _, _, .declInit e _ => e.OpsOK
  | _, _, _, .block b => RItems.OpsOK b
  | _, _, _, .ifThen c s => c.OpsOK ∧ RStmt.OpsOK s
  | _, _, _, .ifElse c s t => c.OpsOK ∧ RStmt.OpsOK s ∧ RStmt.OpsOK t
  | _, _, _, .whileLoop c s => c.OpsOK ∧ RStmt.OpsOK s
  | _, _, _, .doWhile s c => RStmt.OpsOK s ∧ c.OpsOK
  | _, _, _, .forLoop i c p s => RStmt.OpsOK i ∧ c.OpsOK ∧ p.OpsOK ∧ RStmt.OpsOK s
  | _, _, _, .retVal _ e _ => e.OpsOK
  | _, _, _, .retTuple es => RConvArgs.OpsOK es
  | _, _, _, .emit _ _ args | _, _, _, .revertError _ _ args => RConvArgs.OpsOK args

def RItems.OpsOK {E : Env} {R : List STy} {M : Bool} : {k : SCtx} → {Γ Γ' : RCtx} → RItems E R M k Γ Γ' → Prop
  | _, _, _, .nil => True
  | _, _, _, .stmt s rest => RStmt.OpsOK s ∧ RItems.OpsOK rest
  | _, _, _, .unchecked b rest => RItems.OpsOK b ∧ RItems.OpsOK rest

end

theorem TypedArgs.ofSlots_opsOK {Γ : Ctx} : {es : Syn (.list (.opt .expr))} → {τs : List STy} →
    (d : TypedSlots Γ es τs) → RArgs.OpsOK (TypedArgs.ofSlots d)
  | _, _, .nil => trivial
  | _, _, .cons d ds => And.intro (Typed.toR_opsOK d) (TypedArgs.ofSlots_opsOK ds)

mutual

/-- **Elaborated statements stay in the operations' domains.** -/
theorem StmtD.toR_opsOK {C : Ctx} : {k : SCtx} → {L L' : List (String × STy)} → {s : Syn (.stmt k)} →
    (d : StmtD C L s L') → d.toR.OpsOK
  | _, _, _, _, .expr d _ => Typed.toR_opsOK d
  | _, _, _, _, .placeholder _ | _, _, _, _, .declVar _ _ | _, _, _, _, .brk | _, _, _, _, .cont
  | _, _, _, _, .ret _ | _, _, _, _, .rethrow _ _ _ _ => trivial
  | _, _, _, _, .declInit _ _ d _ => Typed.toR_opsOK d
  | _, _, _, _, .block b => ItemsD.toR_opsOK b
  | _, _, _, _, .ifThen dc _ ds => And.intro (Typed.toR_opsOK dc) (StmtD.toR_opsOK ds)
  | _, _, _, _, .ifElse dc _ _ ds dt =>
    And.intro (Typed.toR_opsOK dc) (And.intro (StmtD.toR_opsOK ds) (StmtD.toR_opsOK dt))
  | _, _, _, _, .whileLoop dc _ ds => And.intro (Typed.toR_opsOK dc) (StmtD.toR_opsOK ds)
  | _, _, _, _, .doWhile _ ds dc => And.intro (StmtD.toR_opsOK ds) (Typed.toR_opsOK dc)
  | _, _, _, _, .forLoop dc dp _ ds =>
    And.intro trivial (And.intro (OptCond.toR_opsOK dc) (And.intro (OptExpr.toR_opsOK dp) (StmtD.toR_opsOK ds)))
  | _, _, _, _, .forInit di dc dp _ ds =>
    And.intro (StmtD.toR_opsOK di) (And.intro (OptCond.toR_opsOK dc)
      (And.intro (OptExpr.toR_opsOK dp) (StmtD.toR_opsOK ds)))
  | _, _, _, _, .retVal _ d _ => Typed.toR_opsOK d
  | _, _, _, _, .retTuple d ds _ _ =>
    RArgs.convert_opsOK _ _ _ (And.intro (Typed.toR_opsOK d) (TypedArgs.ofSlots_opsOK ds))
  | _, _, _, _, .emit da _ => RArgs.convert_opsOK _ _ _ (TypedArgs.toR_opsOK da)
  | _, _, _, _, .revertError da _ => RArgs.convert_opsOK _ _ _ (TypedArgs.toR_opsOK da)

theorem ItemsD.toR_opsOK {C : Ctx} : {k : SCtx} → {L L' : List (String × STy)} → {b : Syn (.list (.item k))} →
    (d : ItemsD C L b L') → d.toR.OpsOK
  | _, _, _, _, .nil => trivial
  | _, _, _, _, .stmt ds rest => And.intro (StmtD.toR_opsOK ds) (ItemsD.toR_opsOK rest)
  | _, _, _, _, .unchecked db rest => And.intro (ItemsD.toR_opsOK db) (ItemsD.toR_opsOK rest)

theorem OptCond.toR_opsOK {Γ : Ctx} {c : Syn (.opt .expr)} : (d : OptCond Γ c) → d.toR.OpsOK
  | .none => trivial
  | .some d => Typed.toR_opsOK d

theorem OptExpr.toR_opsOK {Γ : Ctx} {c : Syn (.opt .expr)} : (d : OptExpr Γ c) → d.toR.OpsOK
  | .none => trivial
  | .some d => Typed.toR_opsOK d

end

/-! ## Elaborated programs -/

theorem RItems.opsOK_of_heq {E : Env} {R R' : List STy} {M M' : Bool} {k : SCtx} {Γ Γ' Δ Δ' : RCtx}
    {x : RItems E R M k Γ Δ} {y : RItems E R' M' k Γ' Δ'} (hR : R = R') (hM : M = M') (hΓ : Γ = Γ')
    (hΔ : Δ = Δ') (h : HEq x y) (hy : y.OpsOK) : x.OpsOK := by
  subst hR hM hΓ hΔ
  rw [eq_of_heq h]
  exact hy

theorem RConvArgs.opsOK_of_heq {E : Env} {Γ Γ' : RCtx} {ps : List STy} {x : RConvArgs E Γ ps}
    {y : RConvArgs E Γ' ps} (hΓ : Γ = Γ') (h : HEq x y) (hy : RConvArgs.OpsOK y) : RConvArgs.OpsOK x := by
  subst hΓ
  rw [eq_of_heq h]
  exact hy

/-- Arguments elaborated from a derivation, in the derivation's context. -/
theorem RConvArgs.DerivedIn.opsOK {C : Ctx} {es : Syn (.list .expr)} {ps : List STy}
    {args : RConvArgs C.env C.tys ps} (h : RConvArgs.DerivedIn C es ps args) : RConvArgs.OpsOK args := by
  obtain ⟨_, D, hf, he⟩ := h
  exact RConvArgs.opsOK_of_heq rfl he (RArgs.convert_opsOK _ _ hf (TypedArgs.toR_opsOK D))

/-- An initializer elaborated from a derivation. -/
theorem RInit.Derived.opsOK {E : Env} {i : RInit E} (h : RInit.Derived E i) : i.e.OpsOK := by
  obtain ⟨_, _, D, _, _, he⟩ := h
  rw [he]
  exact Typed.toR_opsOK D

/-- **Every body of an elaborated unit stays in the operations' domains**:
its items and its modifier invocations' arguments. -/
theorem Elaborated.body_opsOK (el : Elaborated) {d : Decl} {b : RBody el.res.env}
    (hd : d ∈ el.res.unit.decls) (hb : el.prog.body d = some b) :
    b.items.OpsOK ∧ ∀ m ∈ b.mods, RConvArgs.OpsOK m.args := by
  obtain ⟨f, L', hf, D, _, hrs, hm, hloc, hout, hI⟩ := el.bodies_typed d hd b hb
  refine ⟨RItems.opsOK_of_heq hrs hm hloc hout hI (ItemsD.toR_opsOK D), fun m hm' => ?_⟩
  obtain ⟨f', hf', hmods⟩ := el.mods_typed d b hb
  have e : f' = f := Option.some.inj (hf'.symm.trans hf)
  subst e
  obtain ⟨p, a, es, _, _, _, hD⟩ := hmods m hm'
  obtain ⟨_, D', hfit, he⟩ := hD
  exact RConvArgs.opsOK_of_heq hloc he (RArgs.convert_opsOK _ _ hfit (TypedArgs.toR_opsOK D'))

/-- Every constant's value and every state variable initializer of an
elaborated unit stays in the operations' domains. -/
theorem Elaborated.inits_opsOK (el : Elaborated) :
    (∀ d i, el.prog.consts d = some i → i.e.OpsOK) ∧ (∀ c, ∀ i ∈ el.prog.inits c, i.e.OpsOK) :=
  ⟨fun d i h => (el.consts_typed d i h).2.opsOK, fun c i h => (el.inits_typed c i h).2.opsOK⟩

/-! ## Implicit conversions of values -/

theorem mkInt_ok (t : IntTy) {v : Int} (h : t.lo ≤ v ∧ v ≤ t.hi) : NotStuckR (mkInt (D := D) t v) := by
  intro w hw
  simp only [mkInt, dif_pos h] at hw
  cases hw

theorem mkFix_ok (t : FixTy) {v : Int} (h : t.lo ≤ v ∧ v ≤ t.hi) : NotStuckR (mkFix (D := D) t v) := by
  intro w hw
  simp only [mkFix, dif_pos h] at hw
  cases hw

theorem FixTy.scale_pos (f : FixTy) : 0 < f.scale := by
  unfold FixTy.scale
  have := Nat.pow_pos (n := f.digits) (show 0 < 10 by decide)
  omega

/-- An integer within solc's integer bounds of a fixed-point type is in its
range once scaled. -/
theorem FixTy.scaled_mem (f : FixTy) {x : Int} (h1 : f.minInt ≤ x) (h2 : x ≤ f.maxInt) :
    f.lo ≤ x * f.scale ∧ x * f.scale ≤ f.hi := by
  have hs := f.scale_pos
  have hs' : (0 : Int) ≤ f.scale := Int.le_of_lt hs
  unfold FixTy.minInt at h1
  unfold FixTy.maxInt at h2
  have e1 : (f.hi / f.scale) * f.scale ≤ f.hi := Int.ediv_mul_le _ (Int.ne_of_gt hs)
  have e2 : ((-f.lo) / f.scale) * f.scale ≤ -f.lo := Int.ediv_mul_le _ (Int.ne_of_gt hs)
  have m2 := Int.mul_le_mul_of_nonneg_right h2 hs'
  have m1 := Int.mul_le_mul_of_nonneg_right h1 hs'
  have e3 : -((-f.lo) / f.scale) * f.scale = -(((-f.lo) / f.scale) * f.scale) := Int.neg_mul _ _
  omega

/-- A conversion of a value of a type to itself, through `convVal`'s
fallback. -/
theorem convVal_self_ok {σ : STy} (x : Val D σ) (hf : convVal σ x = if h : σ = σ then pure (h ▸ x)
    else stuck "implicit conversion of a value") : NotStuckR (convVal σ x) := by
  rw [hf, dif_pos rfl]
  exact NotStuckR.pure _

/-- **`convVal` is never stuck on an implicit conversion of a value
type**, or on the identity: the conversions `toR` inserts around operands
of value type. -/
theorem convVal_ok (B : DeclName → DeclName → Bool) {σ τ : STy} (hσ : σ.isValue = true)
    (h : σ.implicit B τ = true ∨ σ = τ) (x : Val D σ) : NotStuckR (convVal τ x) := by
  rcases h with h | rfl
  · cases σ <;> (try (cases hσ <;> done)) <;> cases τ <;> (try (cases h <;> done))
    · rename_i t t'
      obtain ⟨v, hv, rfl⟩ := Val.eq_int x
      have r := implicit_int_range h
      rw [show convVal (D := D) (.int t') (Val.int (t := t) v hv) = mkInt t' v from rfl]
      exact mkInt_ok _ ⟨Int.le_trans r.1 hv.1, Int.le_trans hv.2 r.2⟩
    · rename_i t f
      obtain ⟨v, hv, rfl⟩ := Val.eq_int x
      have h' : f.minInt ≤ t.lo ∧ t.hi ≤ f.maxInt := by
        rw [show STy.implicit B (.int t) (.fixed f) = f.intImplicit t.lo t.hi from rfl] at h
        simpa only [FixTy.intImplicit, Bool.and_eq_true, decide_eq_true_eq] using h
      rw [show convVal (D := D) (.fixed f) (Val.int (t := t) v hv) = mkFix f (v * f.scale) from rfl]
      exact mkFix_ok _ (f.scaled_mem (Int.le_trans h'.1 hv.1) (Int.le_trans hv.2 h'.2))
    · obtain ⟨b, rfl⟩ := Val.eq_bool x
      rw [show convVal (D := D) .bool (Val.bool b) = pure (.bool b) from rfl]
      exact NotStuckR.pure _
    · rename_i p p'
      obtain ⟨a, rfl⟩ := Val.eq_address x
      rw [show convVal (D := D) (.address p') (Val.address (p := p) a) = pure (.address a) from rfl]
      exact NotStuckR.pure _
    · rename_i n hn m hm
      obtain ⟨bs, hl, rfl⟩ := Val.eq_fixedBytes x
      rw [show convVal (D := D) (.fixedBytes m hm) (Val.fixedBytes (h := hn) bs hl) =
        pure (mkBytes (n := m) (h := hm) bs) from rfl]
      exact NotStuckR.pure _
    · rename_i f f'
      obtain ⟨v, hv, rfl⟩ := Val.eq_fixed x
      have h' : f.subsumes f' = true := by
        rw [show STy.implicit B (.fixed f) (.fixed f') = f.implicitOK f' from rfl] at h
        simp only [FixTy.implicitOK, Bool.and_eq_true] at h
        exact h.2
      have r := FixTy.subsumes_inRange h' hv
      rw [show convVal (D := D) (.fixed f') (Val.fixed (f := f) v hv) =
        mkFix f' (v * ((10 ^ (f'.digits - f.digits) : Nat) : Int)) from rfl]
      refine mkFix_ok _ ?_
      have e : (((10 ^ (f'.digits - f.digits) : Nat) : Int)) = (10 : Int) ^ (f'.digits - f.digits) := by
        simp only [Int.natCast_pow, Int.cast_ofNat_Int]
      rw [e]; exact r
    · rename_i d d'
      have e : d = d' := by
        rw [show STy.implicit B (.enum d) (.enum d') = (d == d') from rfl] at h
        exact beq_iff_eq.mp h
      subst e
      obtain ⟨i, rfl⟩ := Val.eq_enum x
      rw [show convVal (D := D) (.enum d) (Val.enum i) = (if h : i.val < D.enumSize d then
        pure (Val.enum ⟨i.val, h⟩) else stuck "enum") from rfl, dif_pos i.isLt]
      exact NotStuckR.pure _
    · rename_i d d'
      have e : d = d' := by
        rw [show STy.implicit B (.udvt d) (.udvt d') = (d == d') from rfl] at h
        exact beq_iff_eq.mp h
      subst e
      rw [show convVal (D := D) (.udvt d) x = (if h : d = d then pure (h ▸ x) else
        stuck "user-defined value type") from rfl, dif_pos rfl]
      exact NotStuckR.pure _
    · rename_i d d'
      obtain ⟨a, rfl⟩ : ∃ a, x = .contract a := by
        cases x with
        | contract a => exact ⟨a, rfl⟩
        | memRef h _ => cases h
        | storRef h _ => cases h
        | cdRef h _ => cases h
      rw [show convVal (D := D) (.contract d') (Val.contract (d := d) a) = pure (.contract a) from rfl]
      exact NotStuckR.pure _
    · rename_i e ps rs m e' ps' rs' m'
      have he : STy.fn e ps rs m = STy.fn e' ps' rs' m' := by
        rw [show STy.implicit B (.fn e ps rs m) (.fn e' ps' rs' m') = (e == e' && STy.sameList ps ps' &&
          STy.sameList rs rs' && m == m') from rfl] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        rw [h1, STy.eq_of_sameList _ _ h2, STy.eq_of_sameList _ _ h3, h4]
      rw [← he]
      cases x <;> exact convVal_self_ok _ rfl
  · cases σ <;> (try (cases hσ <;> done))
    · rename_i t
      obtain ⟨v, hv, rfl⟩ := Val.eq_int x
      rw [show convVal (D := D) (.int t) (Val.int (t := t) v hv) = mkInt t v from rfl]
      exact mkInt_ok _ hv
    · obtain ⟨b, rfl⟩ := Val.eq_bool x
      rw [show convVal (D := D) .bool (Val.bool b) = pure (.bool b) from rfl]
      exact NotStuckR.pure _
    · rename_i p
      obtain ⟨a, rfl⟩ := Val.eq_address x
      rw [show convVal (D := D) (.address p) (Val.address (p := p) a) = pure (.address a) from rfl]
      exact NotStuckR.pure _
    · rename_i n hn
      obtain ⟨bs, hl, rfl⟩ := Val.eq_fixedBytes x
      rw [show convVal (D := D) (.fixedBytes n hn) (Val.fixedBytes (h := hn) bs hl) =
        pure (mkBytes (n := n) (h := hn) bs) from rfl]
      exact NotStuckR.pure _
    · rename_i f
      obtain ⟨v, hv, rfl⟩ := Val.eq_fixed x
      rw [show convVal (D := D) (.fixed f) (Val.fixed (f := f) v hv) =
        mkFix f (v * ((10 ^ (f.digits - f.digits) : Nat) : Int)) from rfl]
      refine mkFix_ok _ ?_
      simp only [Nat.sub_self, Nat.pow_zero, Int.natCast_one, Int.mul_one]
      exact hv
    · rename_i d
      obtain ⟨i, rfl⟩ := Val.eq_enum x
      rw [show convVal (D := D) (.enum d) (Val.enum i) = (if h : i.val < D.enumSize d then
        pure (Val.enum ⟨i.val, h⟩) else stuck "enum") from rfl, dif_pos i.isLt]
      exact NotStuckR.pure _
    · rename_i d
      rw [show convVal (D := D) (.udvt d) x = (if h : d = d then pure (h ▸ x) else
        stuck "user-defined value type") from rfl, dif_pos rfl]
      exact NotStuckR.pure _
    · rename_i d
      obtain ⟨a, rfl⟩ : ∃ a, x = .contract a := by
        cases x with
        | contract a => exact ⟨a, rfl⟩
        | memRef h _ => cases h
        | storRef h _ => cases h
        | cdRef h _ => cases h
      rw [show convVal (D := D) (.contract d) (Val.contract (d := d) a) = pure (.contract a) from rfl]
      exact NotStuckR.pure _
    · cases x <;> exact convVal_self_ok _ rfl

/-- A constant's exact value at a fixed-point type is in its range. -/
theorem Q.toFixed?_mem {q : Q} {f : FixTy} {v : Int} (h : q.toFixed? f = some v) : f.lo ≤ v ∧ v ≤ f.hi := by
  unfold Q.toFixed? at h
  split at h
  · simp only at h
    split at h
    · rename_i hr; cases h; exact hr
    · cases h
  · cases h

/-- **`constVal` is never stuck on an implicit conversion of a constant**
(to an integer type it fits, a fixed-point type that holds it exactly, or
`bytesN` from zero). -/
theorem constVal_ok (B : DeclName → DeclName → Bool) {q : Q} {τ : STy}
    (h : (STy.rational q).implicit B τ = true) : NotStuckR (constVal (D := D) q τ) := by
  cases τ <;> (try (cases h <;> done))
  · rename_i t
    have hf : q.FitsInt t := by
      rw [show STy.implicit B (.rational q) (.int t) = decide (q.FitsInt t) from rfl] at h
      exact of_decide_eq_true h
    rw [show constVal (D := D) q (.int t) = (if q.isInt then mkInt t q.toInt
      else stuck "fractional constant at an integer type") from rfl, if_pos hf.1]
    exact mkInt_ok _ hf.2
  · rename_i n hn
    have h0 : q.num = 0 := by
      rw [show STy.implicit B (.rational q) (.fixedBytes n hn) = (q.num == 0) from rfl] at h
      exact beq_iff_eq.mp h
    rw [show constVal (D := D) q (.fixedBytes n hn) = (if q.num = 0 then pure (mkBytes (n := n) (h := hn) [])
      else stuck "constant at bytes") from rfl, if_pos h0]
    exact NotStuckR.pure _
  · rename_i f
    rw [show STy.implicit B (.rational q) (.fixed f) = (q.toFixed? f).isSome from rfl] at h
    rcases hv : q.toFixed? f with _ | v
    · rw [hv] at h; cases h
    · rw [show constVal (D := D) q (.fixed f) = (match q.toFixed? f with
        | some v => mkFix f v
        | none => stuck "constant not exact at a fixed-point type") from rfl, hv]
      exact mkFix_ok _ (Q.toFixed?_mem hv)

end Solidity.Source
