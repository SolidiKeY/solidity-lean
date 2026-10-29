import Solidity.Calculus.MemInst

/-!
# Stable typed exterior observations of one fresh primitive array

A proof-carrying supported-shape view of existing intrinsic terms/formulas.
The view has a primitive sort at every node and reifies to `Tm`/`Fml`;
unsupported symbols and binders are refused. Optional observations, including
halted reads and checked operators, are preserved exactly by reconstruction.
-/

namespace Solidity.Decide

variable {C : Contract} {Γ : Ctx} {q p : PrimTy}

inductive MxObs (q : PrimTy) : PrimTy → Type where
  | lit (p : PrimTy) (v : p.Denote) : MxObs q p
  | len : MxObs q .uint
  | read (k : PrimTy.uint.Denote) : MxObs q q
  | binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true)
      (a b : MxObs q p) : MxObs q (op.ret p)

def MxObs.tm {p : PrimTy} (a : MxObs q p) : Tm C (.mem (.array (.prim q)) :: Γ) (.val p) :=
  MxObs.casesOn (motive := fun p _ => Tm C (.mem (.array (.prim q)) :: Γ) (.val p)) a
    (fun _ v => .app0 (.lit v)) (MxOrig.len .here).tm
    (fun k => .app2 .read (.app0 .memory)
      (.app2 (.mat .dyn) (.pvI .here) (.app0 (.lit k))))
    (fun op {_} h a b => .app2 (.binop op h) a.tm b.tm)
  termination_by structural a

def MxObs.reads {p : PrimTy} (a : MxObs q p) : List PrimTy.uint.Denote :=
  MxObs.casesOn (motive := fun _ _ => List PrimTy.uint.Denote) a
    (fun _ _ => []) [] (fun k => [k]) (fun _ {_} _ a b => a.reads ++ b.reads)
  termination_by structural a

def MxObs.obs {H : HTy} (o : MObj H (.array (.prim q))) {p : PrimTy} (a : MxObs q p) : Option p.Denote :=
  MxObs.casesOn (motive := fun p _ => Option p.Denote) a
    (fun _ v => some v) (some (mxFillN .dyn o))
    (fun k => (MObj.elems .dyn o)[k.1.toNat]?)
    (fun op {_} h a b => (a.obs o).bind fun v => binopT op h v (b.obs o))
  termination_by structural a

/-- Extract a proposed literal key through intrinsic recursor views; the
complete read is checked against its typed reconstruction before accepting it. -/
def mxObsReadKey? {p : PrimTy} (t : Tm C (.mem (.array (.prim q)) :: Γ) (.val p)) :
    Option PrimTy.uint.Denote := do
  let ⟨addr, _⟩ ← mxReadView t
  let ⟨_, (_, _, e), _⟩ ← mxAddressView addr
  let ⟨k, _⟩ ← mxLiteralView e
  pure k

def MxObs.atom? {p : PrimTy} (t : Tm C (.mem (.array (.prim q)) :: Γ) (.val p)) :
    Option {a : MxObs q p // t = a.tm} :=
  let len? : Option {a : MxObs q p // t = a.tm} :=
    if hp : p = .uint then
      let l : MxObs q .uint := .len
      if ht : (hp ▸ t).beqR (l.tm (C := C) (Γ := Γ)) = true then
        some ⟨hp.symm ▸ l, by cases hp; exact Tm.eq_of_beqR ht⟩
      else none
    else none
  match len? with
  | some a => some a
  | none =>
    if hp : p = q then
      match mxObsReadKey? t with
      | some k =>
        let a : MxObs q q := .read k
        if ht : (hp ▸ t).beqR (a.tm (C := C) (Γ := Γ)) = true then
          some ⟨hp.symm ▸ a, by cases hp; exact Tm.eq_of_beqR ht⟩
        else none
      | none => none
    else none

/-- Sort-indexed wrapper lets the parser recurse on the existing `Tm`
recursor without a partial or fuel-bounded untyped intermediate. -/
inductive MxObsAt (q : PrimTy) : Srt → Type where
  | val {p : PrimTy} (a : MxObs q p) : MxObsAt q (.val p)

def MxObsAt.tm {s : Srt} (a : MxObsAt q s) : Tm C (.mem (.array (.prim q)) :: Γ) s :=
  MxObsAt.casesOn (motive := fun s _ => Tm C (.mem (.array (.prim q)) :: Γ) s) a
    (fun a => a.tm)

def mxObsAtomAt? {s : Srt} : (t : Tm C (.mem (.array (.prim q)) :: Γ) s) →
    Option {a : MxObsAt q s // t = a.tm} :=
  match s with
  | .val _ => fun t => (MxObs.atom? t).map fun ⟨a, ha⟩ => ⟨.val a, ha⟩
  | _ => fun _ => none

private def mxObsParse0 {s : Srt} (o : Op0 C s) :
    Option {a : MxObsAt q s // Tm.app0 o = a.tm (Γ := Γ)} := by
  apply @Op0.casesOn C (fun s o => Option {a : MxObsAt q s // Tm.app0 o = a.tm (Γ := Γ)}) s o
  case lit => exact fun v => some ⟨.val (.lit _ v), rfl⟩
  all_goals intros; exact none

private def mxObsVal {s : Srt} (a : MxObsAt q s) :
    match s with
    | .val p => {b : MxObs q p // a.tm (C := C) (Γ := Γ) = b.tm}
    | _ => PUnit :=
  MxObsAt.casesOn (motive := fun s a => match s with
    | .val p => {b : MxObs q p // a.tm (C := C) (Γ := Γ) = b.tm}
    | _ => PUnit) a (fun a => ⟨a, rfl⟩)

private def mxObsParse2 {a b s : Srt} (o : Op2 C a b s) :
    (x : Tm C (.mem (.array (.prim q)) :: Γ) a) →
    (y : Tm C (.mem (.array (.prim q)) :: Γ) b) →
    Option {v : MxObsAt q a // x = v.tm} →
    Option {v : MxObsAt q b // y = v.tm} →
    Option {v : MxObsAt q s // Tm.app2 o x y = v.tm} := by
  apply @Op2.casesOn C (fun a b s o =>
    (x : Tm C (.mem (.array (.prim q)) :: Γ) a) →
    (y : Tm C (.mem (.array (.prim q)) :: Γ) b) →
    Option {v : MxObsAt q a // x = v.tm} →
    Option {v : MxObsAt q b // y = v.tm} →
    Option {v : MxObsAt q s // Tm.app2 o x y = v.tm}) a b s o
  case binop =>
    intro op p h x y rx ry
    exact do
      let ⟨va, ha⟩ ← rx
      let ⟨vb, hb⟩ ← ry
      let a := mxObsVal (C := C) (Γ := Γ) va
      let b := mxObsVal (C := C) (Γ := Γ) vb
      pure ⟨.val (.binop op h a.val b.val),
        congr (congrArg (Tm.app2 (.binop op h)) (ha.trans a.property)) (hb.trans b.property)⟩
  all_goals intros; exact mxObsAtomAt? _

def MxObs.parse {s : Srt} (t : Tm C (.mem (.array (.prim q)) :: Γ) s) :
    Option {a : MxObsAt q s // t = a.tm} :=
  @Tm.casesOn C (.mem (.array (.prim q)) :: Γ)
    (fun s t => Option {a : MxObsAt q s // t = a.tm}) s t
    (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
    (fun _ _ => none) (fun o => mxObsParse0 o) (fun _ _ => none)
    (fun o x y => mxObsParse2 o x y (MxObs.parse x) (MxObs.parse y))
    (fun _ _ _ _ => none) (fun _ => none)
  termination_by structural t

/-- Constructor equations avoid the recursive definition's generic equation. -/
theorem MxObs.parse_app0 {s : Srt} (o : Op0 C s) :
    MxObs.parse (q := q) (Γ := Γ) (.app0 o) = mxObsParse0 o := rfl

theorem MxObs.parse_app2 {a b s : Srt} (o : Op2 C a b s)
    (x : Tm C (.mem (.array (.prim q)) :: Γ) a)
    (y : Tm C (.mem (.array (.prim q)) :: Γ) b) :
    MxObs.parse (.app2 o x y) = mxObsParse2 o x y (MxObs.parse x) (MxObs.parse y) := rfl

theorem MxObs.parse_lit (v : p.Denote) :
    MxObs.parse (C := C) (Γ := Γ) (q := q) (.app0 (.lit v)) =
      some ⟨.val (.lit p v), rfl⟩ := rfl

def MxObs.ofTm? {p : PrimTy} (t : Tm C (.mem (.array (.prim q)) :: Γ) (.val p)) :
    Option {a : MxObs q p // t = a.tm} :=
  (MxObs.parse t).map fun ⟨a, ha⟩ =>
    let v := mxObsVal (C := C) (Γ := Γ) a
    ⟨v.val, ha.trans v.property⟩

theorem MxObs.eval_alloc (σ : State C Γ) (o : MObj σ.H (.array (.prim q))) :
    {p : PrimTy} → (a : MxObs q p) → a.tm.eval (σ.allocPush o) = a.obs o
  | _, .lit _ _ => rfl
  | _, .len => by
    have hl : (MObj.elems .dyn o).length < 2 ^ 256 := by rw [MObj.elems_dyn]; exact o.2
    simpa only [MxObs.tm, MxObs.obs, mxFillN, uintOfNat_eq_lenU hl] using mxLenNew_eval σ o
  | _, .read k => by
    simpa only [MxObs.tm, MxObs.obs, Tm.wk_app0, Tm.eval, Op0.eval, Option.bind_some] using
      mxReadNew_eval σ o .dyn (.app0 (.lit k)) rfl rfl
  | _, .binop op h a b => by
    change Op2.eval (σ.allocPush o).glob (.binop op h) (a.tm.eval (σ.allocPush o))
      (b.tm.eval (σ.allocPush o)) = _
    rw [a.eval_alloc σ o, b.eval_alloc σ o, Op2.eval_eq_evalM]
    rfl

theorem MxObs.denote_alloc (σ : State C Γ) (o : MObj σ.H (.array (.prim q))) :
    {p : PrimTy} → (a : MxObs q p) → a.tm.denote (σ.allocPush o) = a.obs o
  | _, .lit _ _ => rfl
  | _, .len => by
    change (MxOrig.len .here).tm.denote (σ.allocPush o) = _
    rw [MxOrig.denote_eq]
    exact MxObs.eval_alloc σ o .len
  | _, .read k => by
    change (MxOrig.elem .here .dyn (.app0 (.lit k)) rfl).tm.denote (σ.allocPush o) = _
    rw [MxOrig.denote_eq]
    exact MxObs.eval_alloc σ o (.read k)
  | _, .binop op h a b => by
    change (a.tm.denote (σ.allocPush o)).bind (fun v => binopT op h v (b.tm.denote (σ.allocPush o))) = _
    rw [a.denote_alloc σ o, b.denote_alloc σ o]
    rfl

/-- Stability is proved from the read footprint, not from denote/eval
agreement alone. It includes all optional failures of exterior operators. -/
theorem MxObs.rebuild {H : HTy} (o : MObj H (.array (.prim q))) (B : List Int)
    (hn : ((MObj.elems .dyn o).length : Int) ∈ B) :
    {p : PrimTy} → (a : MxObs q p) → (∀ k ∈ a.reads, k.1 ∈ B) →
      a.obs (mxFloorRebuild .dyn (by trivial) o B) = a.obs o
  | _, .lit _ _, _ => rfl
  | _, .len, _ => congrArg some (mxFloorRebuild_fillN .dyn (by trivial) o B)
  | _, .read k, hr => by
    change (MObj.elems .dyn (mxFloorRebuild .dyn (by trivial) o B))[k.1.toNat]? = _
    apply mxFloorRebuild_at .dyn (by trivial) o B hn
    have h0 := mxUint_nonneg k
    have hk := hr k (List.mem_singleton_self k)
    have he : (k.1.toNat : Int) = k.1 := by omega
    rw [he]
    exact hk
  | _, .binop op h a b, hr => by
    change (a.obs (mxFloorRebuild .dyn (by trivial) o B)).bind
      (fun v => binopT op h v (b.obs (mxFloorRebuild .dyn (by trivial) o B))) = _
    rw [a.rebuild o B hn (fun k hk => hr k (List.mem_append_left _ hk)),
      b.rebuild o B hn (fun k hk => hr k (List.mem_append_right _ hk))]
    rfl

inductive MxExterior (q : PrimTy) where
  | tt
  | eq {p : PrimTy} (a b : MxObs q p)
  | not (a : MxExterior q)
  | and (a b : MxExterior q)
  | imp (a b : MxExterior q)

/-- Reify the Boolean shell in any context using its typed term reader. -/
def MxExterior.fmlWith (tm : {p : PrimTy} → MxObs q p → Tm C Γ (.val p)) : MxExterior q → Fml C Γ
  | .tt => .tt
  | .eq a b => .eq (tm a) (tm b)
  | .not a => .not (a.fmlWith tm)
  | .and a b => .and (a.fmlWith tm) (b.fmlWith tm)
  | .imp a b => .imp (a.fmlWith tm) (b.fmlWith tm)

def MxExterior.fml (a : MxExterior q) : Fml C (.mem (.array (.prim q)) :: Γ) :=
  a.fmlWith MxObs.tm

def MxExterior.reads : MxExterior q → List PrimTy.uint.Denote
  | .tt => []
  | .eq a b => a.reads ++ b.reads
  | .not a => a.reads
  | .and a b | .imp a b => a.reads ++ b.reads

def MxExterior.obs {H : HTy} (o : MObj H (.array (.prim q))) : MxExterior q → Prop
  | .tt => True
  | .eq a b => a.obs o = b.obs o
  | .not a => ¬ a.obs o
  | .and a b => a.obs o ∧ b.obs o
  | .imp a b => a.obs o → b.obs o

/-- The formula recursor generalizes its context and takes a reader at
that context. Only the Boolean shell recurses; unsupported binders fail closed. -/
def MxExterior.parseWith {Δ : Ctx} (φ : Fml C Δ) :
    (tm : {p : PrimTy} → MxObs q p → Tm C Δ (.val p)) →
    ({p : PrimTy} → (t : Tm C Δ (.val p)) → Option {a : MxObs q p // t = tm a}) →
    Option {a : MxExterior q // φ = a.fmlWith tm} :=
  @Fml.casesOn C (fun Δ φ =>
    (tm : {p : PrimTy} → MxObs q p → Tm C Δ (.val p)) →
    ({p : PrimTy} → (t : Tm C Δ (.val p)) → Option {a : MxObs q p // t = tm a}) →
    Option {a : MxExterior q // φ = a.fmlWith tm}) Δ φ
    (fun _ _ => some ⟨.tt, rfl⟩)
    (fun a b _ parse => do
      let ⟨a', ha⟩ ← parse a
      let ⟨b', hb⟩ ← parse b
      pure ⟨.eq a' b', by rw [ha, hb]; rfl⟩)
    (fun _ _ _ => none)
    (fun a tm parse => do
      let ⟨a', ha⟩ ← MxExterior.parseWith a tm parse
      pure ⟨.not a', by rw [ha]; rfl⟩)
    (fun a b tm parse => do
      let ⟨a', ha⟩ ← MxExterior.parseWith a tm parse
      let ⟨b', hb⟩ ← MxExterior.parseWith b tm parse
      pure ⟨.and a' b', by rw [ha, hb]; rfl⟩)
    (fun a b tm parse => do
      let ⟨a', ha⟩ ← MxExterior.parseWith a tm parse
      let ⟨b', hb⟩ ← MxExterior.parseWith b tm parse
      pure ⟨.imp a' b', by rw [ha, hb]; rfl⟩)
    (fun _ _ _ _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ => none)
    (fun _ _ _ _ _ => none) (fun _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    (fun _ _ _ _ _ => none) (fun _ _ _ => none)
  termination_by structural φ

def MxExterior.ofFml? (φ : Fml C (.mem (.array (.prim q)) :: Γ)) :
    Option {a : MxExterior q // φ = a.fml} := MxExterior.parseWith φ MxObs.tm MxObs.ofTm?

/-- Public shell equations preserve the exact reconstruction certificates. -/
theorem MxExterior.ofFml?_tt :
    MxExterior.ofFml? (C := C) (Γ := Γ) (q := q) .tt = some ⟨.tt, rfl⟩ := rfl

theorem MxExterior.ofFml?_eq (a b : Tm C (.mem (.array (.prim q)) :: Γ) (.val p)) :
    MxExterior.ofFml? (.eq a b) = (do
      let ⟨a', ha⟩ ← MxObs.ofTm? a
      let ⟨b', hb⟩ ← MxObs.ofTm? b
      pure ⟨.eq a' b', by rw [ha, hb]; rfl⟩) := rfl

theorem MxExterior.ofFml?_not (a : Fml C (.mem (.array (.prim q)) :: Γ)) :
    MxExterior.ofFml? (.not a) = (do
      let ⟨a', ha⟩ ← MxExterior.ofFml? a
      pure ⟨.not a', by rw [ha]; rfl⟩) := rfl

theorem MxExterior.ofFml?_and (a b : Fml C (.mem (.array (.prim q)) :: Γ)) :
    MxExterior.ofFml? (.and a b) = (do
      let ⟨a', ha⟩ ← MxExterior.ofFml? a
      let ⟨b', hb⟩ ← MxExterior.ofFml? b
      pure ⟨.and a' b', by rw [ha, hb]; rfl⟩) := rfl

theorem MxExterior.ofFml?_imp (a b : Fml C (.mem (.array (.prim q)) :: Γ)) :
    MxExterior.ofFml? (.imp a b) = (do
      let ⟨a', ha⟩ ← MxExterior.ofFml? a
      let ⟨b', hb⟩ ← MxExterior.ofFml? b
      pure ⟨.imp a' b', by rw [ha, hb]; rfl⟩) := rfl

theorem MxExterior.holds_alloc (σ : State C Γ) (o : MObj σ.H (.array (.prim q))) :
    (a : MxExterior q) → (holds (σ.allocPush o) a.fml ↔ a.obs o)
  | .tt => Iff.rfl
  | .eq a b => by change a.tm.denote _ = b.tm.denote _ ↔ _; rw [a.denote_alloc σ o, b.denote_alloc σ o]; rfl
  | .not a => not_congr (a.holds_alloc σ o)
  | .and a b => and_congr (a.holds_alloc σ o) (b.holds_alloc σ o)
  | .imp a b => imp_congr (a.holds_alloc σ o) (b.holds_alloc σ o)

theorem MxExterior.rebuild {H : HTy} (o : MObj H (.array (.prim q))) (B : List Int)
    (hn : ((MObj.elems .dyn o).length : Int) ∈ B) :
    (a : MxExterior q) → (∀ k ∈ a.reads, k.1 ∈ B) →
      (a.obs (mxFloorRebuild .dyn (by trivial) o B) ↔ a.obs o)
  | .tt, _ => Iff.rfl
  | .eq a b, hr => by
    change a.obs _ = b.obs _ ↔ _
    rw [a.rebuild o B hn (fun k hk => hr k (List.mem_append_left _ hk)),
      b.rebuild o B hn (fun k hk => hr k (List.mem_append_right _ hk))]
    rfl
  | .not a, hr => not_congr (a.rebuild o B hn hr)
  | .and a b, hr => and_congr
      (a.rebuild o B hn (fun k hk => hr k (List.mem_append_left _ hk)))
      (b.rebuild o B hn (fun k hk => hr k (List.mem_append_right _ hk)))
  | .imp a b, hr => imp_congr
      (a.rebuild o B hn (fun k hk => hr k (List.mem_append_left _ hk)))
      (b.rebuild o B hn (fun k hk => hr k (List.mem_append_right _ hk)))

#print axioms MxExterior.rebuild
#print axioms MxExterior.holds_alloc

end Solidity.Decide
